package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DeterminizeDD;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


public class Determinize<LETTER,STATE> implements IOperation {

	protected static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Operand;
	private final DeterminizeNwa<LETTER, STATE> m_Determinized;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;
	private final IStateDeterminizer<LETTER,STATE> stateDeterminizer;
	private final StateFactory<STATE> m_StateFactory;
	
	
	@Override
	public String operationName() {
		return "determinize";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				m_Result.sizeInformation();
	}
	
	
	public Determinize(INestedWordAutomatonSimple<LETTER,STATE> input) throws OperationCanceledException {
		this.stateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input);
		this.m_StateFactory = input.getStateFactory();
		this.m_Operand = input;
		s_Logger.info(startMessage());
		m_Determinized = new DeterminizeNwa<LETTER, STATE>(input, stateDeterminizer, m_StateFactory);
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Determinized);
		s_Logger.info(exitMessage());
	}
	


	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		if (stateDeterminizer instanceof PowersetDeterminizer) {
			assert (checkResult(m_StateFactory));
		}
		return m_Result;
	}


	
	public boolean checkResult(StateFactory<STATE> sf) throws OperationCanceledException {
		s_Logger.info("Start testing correctness of " + operationName());
		INestedWordAutomatonOldApi<LETTER, STATE> operandOldApi = ResultChecker.getOldApiNwa(m_Operand);
		
		boolean correct = true;

		// should have same number of states as old determinization
		INestedWordAutomatonOldApi<LETTER, STATE> resultDD = (new DeterminizeDD<LETTER, STATE>(operandOldApi)).getResult();
		correct &= (resultDD.size() == m_Result.size());
		// should recognize same language as old computation
		correct &= (ResultChecker.nwaLanguageInclusion(resultDD, m_Result, sf) == null);
		correct &= (ResultChecker.nwaLanguageInclusion(m_Result, resultDD, sf) == null);
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_Operand);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	
}

