/*
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.rcfg.RcfgUtils;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqFunctionNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.elements.EqNode;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states.VPTfStateBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.util.RCFGEdgeVisitor;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap3;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class VPTransFormulaStateBuilderPreparer {
	
	VPDomainPreanalysis mPreAnalysis;

//	private final Collection<EqNode> mAllEqNodes;
//	private final Set<EqFunctionNode> mAllEqFunctionNodes;
//	private final Set<EqNode> mAllEqNonFunctionNodes;
	private final Set<EqNode> mAllConstantEqNodes;
	private final Map<TransFormula, VPTfStateBuilder> mTransFormulaToVPTfStateBuilder = 
			new HashMap<>();
	private final ILogger mLogger;
	
//	NestedMap3<IProgramVarOrConst, 
//			Pair<IProgramVar, TermVariable>,  
//			Pair<IProgramVar, TermVariable>, 
//			VPTfArrayIdentifier> mPvocToInVarToOutVarToArrayIdentifier = new NestedMap3<>();
	
	
	public VPTransFormulaStateBuilderPreparer(VPDomainPreanalysis preAnalysis, IIcfg<?> root, ILogger logger) {
		mPreAnalysis = preAnalysis;
		mLogger = logger;
		
		Collection<EqNode> allEqNodes = preAnalysis.getTermToEqNodeMap().values();
		Set<EqFunctionNode> allEqFunctionNodes = 
				allEqNodes.stream()
				.filter(node -> node instanceof EqFunctionNode)
				.map(node -> (EqFunctionNode) node)
				.collect(Collectors.toSet());
//		HashSet<EqNode> allEqNonFunctionNodes = new HashSet<>(allEqNodes);
		allEqFunctionNodes.removeAll(allEqFunctionNodes);

//		mAllEqNodes = Collections.unmodifiableCollection(allEqNodes);
//		mAllEqFunctionNodes = Collections.unmodifiableSet(allEqFunctionNodes);
//		mAllEqNonFunctionNodes = Collections.unmodifiableSet(allEqNonFunctionNodes);
		
		
		Set<EqNode> allConstantEqNodes = 
				allEqNodes.stream()
				.filter(node -> node.isConstant())
				.collect(Collectors.toSet());
		mAllConstantEqNodes = Collections.unmodifiableSet(allConstantEqNodes);

		process(RcfgUtils.getInitialEdges(root));
	}

	private <T extends IcfgEdge> void process(final Collection<T> edges) {
		mLogger.info("started VPDomainPreAnalysis");
		

		final Deque<IcfgEdge> worklist = new ArrayDeque<>();
		final Set<IcfgEdge> finished = new HashSet<>();

		worklist.addAll(edges);
		while (!worklist.isEmpty()) {
			final IcfgEdge current = worklist.removeFirst();
			if (!finished.add(current)) {
				continue;
			}
			if (current instanceof IAction) {
				visit((IAction) current);
			}
			worklist.addAll(current.getTarget().getOutgoingEdges());
		}
	}
	
	
	protected void visit(IAction c) {
		if (c instanceof ICallAction) {
			visit((ICallAction) c);
		} else if (c instanceof IReturnAction) {
			visit((IReturnAction) c);
		} else if (c instanceof IInternalAction) {
			visit((IInternalAction) c);
		} else {
			assert false : "forgot a case?";
		}
	}
	
	
	protected void visit(ICallAction c) {
		TransFormula tf = c.getLocalVarsAssignment();
		handleTransFormula(tf);
	}

	protected void visit(IReturnAction c) {
		TransFormula tf = c.getAssignmentOfReturn();
		handleTransFormula(tf);
	}

	protected void visit(IInternalAction c) {
		TransFormula tf = c.getTransformula();
		handleTransFormula(tf);
	}



	private void handleTransFormula(TransFormula tf) {
		VPTfStateBuilder vptsb = new VPTfStateBuilder(mPreAnalysis, this, tf, mAllConstantEqNodes);
		
		mTransFormulaToVPTfStateBuilder.put(tf, vptsb);
	}
	
	
	public VPTfStateBuilder getVPTfStateBuilder(TransFormula tf) {
		VPTfStateBuilder result = mTransFormulaToVPTfStateBuilder.get(tf);
		assert result != null : "we should have a VPTransitionStateBuidler for every Transformula in the program";
		assert result.isTopConsistent();
		return result;
	}

	public Set<EqNode> getAllConstantEqNodes() {
		return mAllConstantEqNodes;
	}

//	public VPTfArrayIdentifier getArrayIdentifier(Term term, TransFormula transFormula) {
//		return getArrayIdentifier(
//				mPreAnalysis.getIProgramVarOrConstOrLiteral(term, 
//					VPDomainHelpers.computeProgramVarMappingFromTransFormula(transFormula)),
//				VPDomainHelpers.projectToTerm(transFormula.getInVars(), term),
//				VPDomainHelpers.projectToTerm(transFormula.getOutVars(), term));
//	}
//
//	/**
//	 * 
//	 * @param function
//	 * @param inVars
//	 * @param outVars
//	 * @return
//	 * 
//	 * TODO should we move this to the VPTfStateBuilder, like the management for VPNodeIdenfifiers??
//	 */
//	public VPTfArrayIdentifier getArrayIdentifier(IProgramVarOrConst function, 
//			Map<IProgramVar, TermVariable> inVars,
//			Map<IProgramVar, TermVariable> outVars) {
//		Pair<IProgramVar, TermVariable> inVar = null;;
//		Pair<IProgramVar, TermVariable> outVar = null;;
//		
//		TermVariable iTv = inVars.get(function);
//		if (iTv != null) {
//			inVar = new Pair<>((IProgramVar) function, iTv);
//		}
//		TermVariable oTv = inVars.get(function);
//		if (oTv != null) {
//			outVar = new Pair<>((IProgramVar) function, oTv);
//		}
//		VPTfArrayIdentifier result = mPvocToInVarToOutVarToArrayIdentifier.get(function, inVar, outVar);
//		
//		if (result == null) {
//			result = new VPTfArrayIdentifier(function, inVar, outVar);
//			mPvocToInVarToOutVarToArrayIdentifier.put(function, inVar, outVar, result);
//		}
//		return result;
//	}
}
