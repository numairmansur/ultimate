/*
 * Copyright (C) 2014-2015 Betim Musa (musab@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.PartialQuantifierElimination;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SafeSubstitutionWithLocalSimplification;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;

/**
 * @author musab@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 * 
 */
public class PredicateTransformer {
	private final Script mScript;
	private final ModifiableGlobalVariableManager mModifiableGlobalVariableManager;
	private final ManagedScript mManagedScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplicationTechnique mSimplificationTechnique;
	private final XnfConversionTechnique mXnfConversionTechnique;

	public PredicateTransformer(final ManagedScript variableManager, final Script script, 
			final ModifiableGlobalVariableManager modifiableGlobalVariableManager,
			final IUltimateServiceProvider services, 
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
		mXnfConversionTechnique = xnfConversionTechnique;
		mScript = script;
		mModifiableGlobalVariableManager = modifiableGlobalVariableManager;
		mManagedScript = variableManager;
	}
	
	private static TermVariable constructFreshTermVariable(final ManagedScript freshVarConstructor, final IProgramVar pv) {
		return freshVarConstructor.constructFreshTermVariable(pv.getGloballyUniqueId(), pv.getTermVariable().getSort());
	}


	/**
	 * Computes the strongest postcondition of the given predicate p and the
	 * TransFormula tf. - invars of the given transformula, which don't occur in
	 * the outvars or are mapped to different values are renamed to fresh
	 * variables. The corresponding term variables in the given predicate p, are
	 * renamed to the same fresh variables. - outvars are renamed to
	 * corresponding term variables. If an outvar doesn't occur in the invars,
	 * its occurrence in the given predicate is substituted by a fresh variable.
	 * All fresh variables are existentially quantified.
	 */
	public Term strongestPostcondition(final IPredicate p, final TransFormula tf) {
		if (SmtUtils.isFalse(p.getFormula())) {
			return p.getFormula();
		}
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = new IValueConstruction<IProgramVar, TermVariable>() {

			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				final TermVariable result = constructFreshTermVariable(mManagedScript, pv);
				varsToQuantify.add(result);
				return result;
			}
			
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForPredecessor = new ConstructionCache<>(substituentConstruction);
		
		final Map<Term, Term> substitutionForTransFormula = new HashMap<Term, Term>();
		final Map<Term, Term> substitutionForPredecessor = new HashMap<Term, Term>();
		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (entry.getValue() == tf.getOutVars().get(pv)) {
				// special case, variable unchanged will be renamed when
				// considering outVars
			} else {
				final TermVariable substituent = termVariablesForPredecessor.getOrConstuct(pv);
				substitutionForTransFormula.put(entry.getValue(), substituent);
				if (p.getVars().contains(pv)) {
					substitutionForPredecessor.put(pv.getTermVariable(), substituent);
				}
			}
		}

		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!tf.getInVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				final TermVariable substituent = termVariablesForPredecessor.getOrConstuct(entry.getKey());
				substitutionForPredecessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}
		
		final Term renamedTransFormula = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForTransFormula).transform(tf.getFormula());
		final Term renamedPredecessor = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForPredecessor).transform(p.getFormula());
			
		final Term result = Util.and(mScript, renamedTransFormula, renamedPredecessor);

		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;
	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way.
	 */
	@Deprecated
	public Term strongestPostcondition(final IPredicate p, final Call call, final boolean isPendingCall) {
		return strongestPostcondition(p, call.getTransitionFormula(),
				mModifiableGlobalVariableManager.getGlobalVarsAssignment(call.getCallStatement().getMethodName()),
				mModifiableGlobalVariableManager.getOldVarsAssignment(call.getCallStatement().getMethodName()),
				isPendingCall);
	}
	
	
	public Term weakLocalPostconditionCall(final IPredicate p, final TransFormula globalVarAssignments, final Set<IProgramVar> modifiableGlobals) {
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		
		final Term renamedOldVarsAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : globalVarAssignments.getAssignedVars()) {
				assert (pv instanceof IProgramNonOldVar);
				substitutionMapping.put(globalVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : globalVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof IProgramOldVar);
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			renamedOldVarsAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mManagedScript, substitutionMapping).transform(globalVarAssignments.getFormula());
		}

		final Term renamedPredicate;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			TermVariable substituent;
			for (final IProgramVar pv : p.getVars()) {
				if (pv instanceof IProgramNonOldVar) {
					if (modifiableGlobals.contains(pv)) {
						substituent = constructFreshTermVariable(mManagedScript, pv);
						varsToQuantify.add(substituent);
						substitutionMapping.put(pv.getTermVariable(), substituent);
					} else {
						// do nothing
					}
				} else if (pv instanceof IProgramOldVar) {
					substituent = constructFreshTermVariable(mManagedScript, pv);
					varsToQuantify.add(substituent);
					substitutionMapping.put(pv.getTermVariable(), substituent);
				} else if (pv instanceof ILocalProgramVar) {
					substituent = constructFreshTermVariable(mManagedScript, pv);
					varsToQuantify.add(substituent);
					substitutionMapping.put(pv.getTermVariable(), substituent);
				} else {
					throw new AssertionError();
				}
			}
			renamedPredicate = new SafeSubstitutionWithLocalSimplification(mScript, mManagedScript, substitutionMapping).transform(p.getFormula());
		}
		final Term sucessorTerm = Util.and(mScript, renamedPredicate, renamedOldVarsAssignment);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, sucessorTerm);
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;

	}
	
	
	public Term strongestPostconditionCall(final IPredicate p, final TransFormula localVarAssignments,
			final TransFormula globalVarAssignments, final TransFormula oldVarAssignments, final Set<IProgramVar> modifiableGlobals) {
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = new IValueConstruction<IProgramVar, TermVariable>() {

			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				final TermVariable result;
				if (pv instanceof IProgramNonOldVar) {
					if (modifiableGlobals.contains(pv)) {
						result = constructFreshTermVariable(mManagedScript, pv);
						varsToQuantify.add(result);
					} else {
						result = pv.getTermVariable();
					}
				} else if (pv instanceof IProgramOldVar) {
					result = constructFreshTermVariable(mManagedScript, pv);
					varsToQuantify.add(result);
				} else if (pv instanceof ILocalProgramVar) {
					result = constructFreshTermVariable(mManagedScript, pv);
					varsToQuantify.add(result);
				} else {
					throw new AssertionError();
				}
				return result;
			}
			
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForPredecessor = new ConstructionCache<>(substituentConstruction);
		
		final Term renamedGlobalVarAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : globalVarAssignments.getAssignedVars()) {
				assert (pv instanceof IProgramNonOldVar);
				substitutionMapping.put(globalVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : globalVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof IProgramOldVar);
				substitutionMapping.put(entry.getValue(), entry.getKey().getTermVariable());
			}
			renamedGlobalVarAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mManagedScript, substitutionMapping).transform(globalVarAssignments.getFormula());
		}
		
		final Term renamedOldVarsAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : oldVarAssignments.getAssignedVars()) {
				assert (pv instanceof IProgramOldVar);
				substitutionMapping.put(oldVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : oldVarAssignments.getInVars().entrySet()) {
				assert (entry.getKey() instanceof IProgramNonOldVar);
				substitutionMapping.put(entry.getValue(), termVariablesForPredecessor.getOrConstuct(entry.getKey()));
			}
			renamedOldVarsAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mManagedScript, substitutionMapping).transform(oldVarAssignments.getFormula());
		}
		
		final Term renamedLocalVarsAssignment;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : localVarAssignments.getAssignedVars()) {
				assert (pv instanceof ILocalProgramVar);
				substitutionMapping.put(localVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			for (final Entry<IProgramVar, TermVariable> entry : localVarAssignments.getInVars().entrySet()) {
				substitutionMapping.put(entry.getValue(), termVariablesForPredecessor.getOrConstuct(entry.getKey()));
			}
			renamedLocalVarsAssignment = new SafeSubstitutionWithLocalSimplification(mScript, mManagedScript, substitutionMapping).transform(localVarAssignments.getFormula());
		}
		
		final Term renamedPredicate;
		{
			final Map<Term, Term> substitutionMapping = new HashMap<Term, Term>();
			for (final IProgramVar pv : p.getVars()) {
				substitutionMapping.put(pv.getTermVariable(), termVariablesForPredecessor.getOrConstuct(pv));
			}
			renamedPredicate = new SafeSubstitutionWithLocalSimplification(mScript, mManagedScript, substitutionMapping).transform(p.getFormula());
		}
		final Term sucessorTerm = Util.and(mScript, renamedPredicate, renamedLocalVarsAssignment, renamedOldVarsAssignment,
				renamedGlobalVarAssignment);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantify, sucessorTerm);
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;

	}

	/**
	 * Compute the strongest postcondition for a predicate and a call statement.
	 * Call statements must be treated in a special way. TODO: How do we compute
	 * the SP of a Call Statement?
	 */
	@Deprecated
	private Term strongestPostcondition(final IPredicate p, final TransFormula localVarAssignments,
			final TransFormula globalVarAssignments, final TransFormula oldVarAssignments, final boolean isPendingCall) {

		// VarsToQuantify contains the local Vars and the global vars of the
		// calling proc, for a non-pending call.
		final Set<TermVariable> varsToQuantifyNonPendingCall = new HashSet<TermVariable>();
		// Variables, which should be quantified if we have a pending call.
		final Set<TermVariable> varsToQuantifyPendingCall = new HashSet<TermVariable>();
		// We rename oldvars of non-modifiable global variables to freshvars and
		// quantify them.
		final Set<TermVariable> varsToQuantifyNonModOldVars = new HashSet<TermVariable>();
		// In Pred we rename oldvars of non-modifiable global variables to
		// freshvars.
		final Map<Term, Term> varsToRenameInPredInBoth = new HashMap<Term, Term>();
		// Union Set of auxvars occurring in each transformula
		final Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(localVarAssignments.getAuxVars());
		allAuxVars.addAll(globalVarAssignments.getAuxVars());
		allAuxVars.addAll(oldVarAssignments.getAuxVars());

		final Map<Term, Term> varsToRenameInPredPendingCall = new HashMap<Term, Term>();
		final Map<Term, Term> varsToRenameInPredNonPendingCall = new HashMap<Term, Term>();
		// 1.1 Rename the invars in global variable assignments.Invars are
		// {old(g) --> old(g)_23}
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		Term globalVarsInvarsRenamed = substituteToRepresantativesAndAddToQuantify(globalVarAssignments.getInVars(),
				globalVarAssignments.getFormula(), varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		varsToQuantifyPendingCall.addAll(varsToQuantifyNonPendingCall);
		varsToRenameInPredPendingCall.putAll(varsToRenameInPredNonPendingCall);

		Term globalVarsInVarsRenamedOutVarsRenamed = substituteToRepresantativesAndAddToQuantify(
				restrictMap(globalVarAssignments.getOutVars(), GlobalType.NONOLDVAR), globalVarsInvarsRenamed,
				varsToRenameInPredNonPendingCall, varsToQuantifyNonPendingCall);
		substitution.clear();
		if (SmtUtils.isTrue(globalVarAssignments.getFormula())) {
			for (final IProgramVar pv : oldVarAssignments.getInVars().keySet()) {
				substitution.put(oldVarAssignments.getInVars().get(pv), pv.getTermVariable());
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				varsToQuantifyNonPendingCall.add(freshVar);
				varsToRenameInPredNonPendingCall.put(pv.getTermVariable(), freshVar);
			}
			globalVarsInvarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution)
					.transform(oldVarAssignments.getFormula());
			substitution.clear();

			for (final IProgramVar pv : oldVarAssignments.getOutVars().keySet()) {
				if (pv.isOldvar()) {
					final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
					substitution.put(oldVarAssignments.getOutVars().get(pv), pv.getTermVariable());
					varsToQuantifyPendingCall.add(freshVar);
					varsToRenameInPredPendingCall.put(pv.getTermVariable(), freshVar);
					varsToRenameInPredNonPendingCall.put(pv.getTermVariable(), freshVar);
					varsToQuantifyNonPendingCall.add(freshVar);
				}
			}
			globalVarsInVarsRenamedOutVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution)
					.transform(globalVarsInvarsRenamed);
		}
		// Collect the local and the non-modifiable global variables of the
		// calling proc.
		for (final IProgramVar pv : p.getVars()) {
			// Procedure is null, if it is a global variable
			if (pv.getProcedure() != null) {
				varsToQuantifyNonPendingCall.add(pv.getTermVariable());
				/*
				 * On 2014-06-25 Matthias commented the following two lines of
				 * code: This lead to a problem with recursive programs where a
				 * variable occurred in p and also in the call. I do not know if
				 * commenting these lines is a proper solution (or is the reason
				 * for other bugs).
				 */
				// Ensure that variable doesn't occur in call
				// if (!localVarAssignments.getInVars().containsKey(pv)
				// && !localVarAssignments.getOutVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				varsToRenameInPredPendingCall.put(pv.getTermVariable(), freshVar);
				varsToQuantifyPendingCall.add(freshVar);
				varsToQuantifyNonPendingCall.add(pv.getTermVariable());
				// }
			} else {
				// if is global var of modifiable oldvar we rename var to oldvar
				if (!pv.isOldvar() && oldVarAssignments.getInVars().containsKey(pv)) {
					varsToRenameInPredInBoth.put(pv.getTermVariable(), ((IProgramNonOldVar) pv).getOldVar().getTermVariable());
				}
				
				if (!globalVarAssignments.getInVars().containsKey(pv)
						&& !globalVarAssignments.getOutVars().containsKey(pv)) {
					if (pv.isOldvar()) {
						final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
						varsToRenameInPredInBoth.put(pv.getTermVariable(), freshVar);
						varsToQuantifyNonModOldVars.add(freshVar);
					}
				}
			}
		}
		substitution.clear();

		// 2.1 Rename the invars of the term of Call-Statement.
		for (final IProgramVar pv : localVarAssignments.getInVars().keySet()) {

			if (globalVarAssignments.getOutVars().containsKey(pv)) {
				// If it is a global var, then we substitute it through its
				// oldvar
				substitution.put(localVarAssignments.getInVars().get(pv), ((IProgramNonOldVar) pv).getOldVar()
						.getTermVariable());
			} else {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				substitution.put(localVarAssignments.getInVars().get(pv), freshVar);
				varsToRenameInPredPendingCall.put(pv.getTermVariable(), freshVar);
				varsToQuantifyPendingCall.add(freshVar);
				varsToQuantifyNonPendingCall.add(pv.getTermVariable());
			}
		}
		final Term call_TermInVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(localVarAssignments
				.getFormula());
		substitution.clear();

		final Term predNonModOldVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInPredInBoth).transform(p.getFormula());

		final Term quantified;
		if (isPendingCall) {
			// 2.2 Rename the outvars of the term of the Call-Statement.
			for (final IProgramVar pv : localVarAssignments.getOutVars().keySet()) {
				substitution.put(localVarAssignments.getOutVars().get(pv), pv.getTermVariable());
			}
			final Term callTermInvarsRenamedOutVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution)
					.transform(call_TermInVarsRenamed);
			// Rename the invars of CAll, local Vars and old version of global
			// variables.
			final Term predRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInPredPendingCall)
					.transform(predNonModOldVarsRenamed);
			final Term predANDCallANDGlobalVars = Util.and(mScript, predRenamed, callTermInvarsRenamedOutVarsRenamed,
					globalVarsInVarsRenamedOutVarsRenamed);
			varsToQuantifyPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyPendingCall.addAll(allAuxVars);

			quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyNonPendingCall, predANDCallANDGlobalVars);
		} else {
			final Term predRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInPredNonPendingCall)
					.transform(predNonModOldVarsRenamed);
			varsToQuantifyNonPendingCall.addAll(varsToQuantifyNonModOldVars);
			varsToQuantifyNonPendingCall.addAll(allAuxVars);
			
			final Term result = Util.and(mScript, predRenamed, globalVarsInVarsRenamedOutVarsRenamed);
			quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyNonPendingCall, result);
		}
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;

	}

	/**
	 * Compute strongest postcondition for a return statement, where calleePred
	 * is the predicate that holds in the called procedure before the return
	 * statement and callerPred is the predicate that held in the calling
	 * procedure before the corresponding call. TODO: How is it computed?
	 */
	public Term strongestPostcondition(final IPredicate calleePred, final IPredicate callerPred, final TransFormula ret_TF,
			final TransFormula callTF, final TransFormula globalVarsAssignment, final TransFormula oldVarsAssignment) {
		// VarsToQuantify contains local vars of called procedure, and it may
		// contain
		// some invars, if it was a recursive call, i.e. callingProc =
		// calledProc.
		final Set<TermVariable> varsToQuantifyOverAll = new HashSet<TermVariable>();
		final Set<TermVariable> varsToQuantifyInCalleePred = new HashSet<TermVariable>();
		final Set<TermVariable> varsToQuantifyInCallerPredAndCallTF = new HashSet<TermVariable>();
		final Map<Term, Term> varsToRenameInCalleePred = new HashMap<Term, Term>();
		final Map<Term, Term> varsToRenameInCallerPred = new HashMap<Term, Term>();
		final Map<Term, Term> outVarsToRenameInCallTF = new HashMap<Term, Term>();
		final Map<Term, Term> inVarsToRenameInReturnTF = new HashMap<Term, Term>();
		final Set<TermVariable> allAuxVars = new HashSet<TermVariable>();
		allAuxVars.addAll(ret_TF.getAuxVars());
		allAuxVars.addAll(callTF.getAuxVars());
		allAuxVars.addAll(globalVarsAssignment.getAuxVars());

		// Substitute oldvars of modifiable global vars by fresh vars in
		// calleePred
		// and substitue their non-oldvar by the same fresh var in callerPred.
		for (final IProgramVar pv : globalVarsAssignment.getInVars().keySet()) {
			final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
			varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
			varsToRenameInCallerPred.put((((IProgramOldVar) pv).getNonOldVar()).getTermVariable(), freshVar);
			varsToQuantifyOverAll.add(freshVar);
		}
		// Note: We have to take also the outvars into account, because
		// sometimes it may be the case,
		// that a invar does not occur in the outvars.
		for (final IProgramVar pv : globalVarsAssignment.getOutVars().keySet()) {
			// We have only to check the vars, that are not contained in the map
			// varsToRenameInCallerPred,
			// because otherwise it is already treated in the case above.
			if (!pv.isOldvar() && !varsToRenameInCallerPred.containsKey(pv.getTermVariable())) {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				varsToRenameInCallerPred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
			}

		}

		// Collect the local variables of called proc
		for (final IProgramVar pv : calleePred.getVars()) {
			if (pv.isGlobal() || pv.isOldvar()) {
				continue;
			}
			if (ret_TF.getOutVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(pv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(pv), freshVar);
				}
				if (callTF.getOutVars().containsKey(pv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(pv), freshVar);
				}
			} else if (callTF.getInVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(pv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(pv), freshVar);
				}
				if (callTF.getOutVars().containsKey(pv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(pv), freshVar);
				}
			} else if (callerPred.getVars().contains(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyOverAll.add(freshVar);
				if (ret_TF.getInVars().containsKey(pv)) {
					inVarsToRenameInReturnTF.put(ret_TF.getInVars().get(pv), freshVar);
				}
				if (callTF.getOutVars().containsKey(pv)) {
					outVarsToRenameInCallTF.put(callTF.getOutVars().get(pv), freshVar);
				}
			} else if (!ret_TF.getInVars().containsKey(pv) && !callTF.getOutVars().containsKey(pv)) {
				if (!mModifiableGlobalVariableManager.getGlobals().containsKey(pv.getIdentifier())) {
					varsToQuantifyInCalleePred.add(pv.getTermVariable());
				}
			}

		}

		// 1.1 We doesn't rename the invars of the TransFormula Return,
		// because we quantify them out.
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (final IProgramVar pv : ret_TF.getInVars().keySet()) {
			if (!inVarsToRenameInReturnTF.containsKey(ret_TF.getInVars().get(pv))) {
				final TermVariable substitutor = ret_TF.getInVars().get(pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}
		// 1.2 Rename outvars of Return statement
		for (final IProgramVar pv : ret_TF.getOutVars().keySet()) {
			if (calleePred.getVars().contains(pv)) {
				if (!varsToRenameInCalleePred.containsKey(pv.getTermVariable())) {
					final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
					varsToRenameInCalleePred.put(pv.getTermVariable(), freshVar);
					varsToQuantifyOverAll.add(freshVar);
				}
			}
			substitution.put(ret_TF.getOutVars().get(pv), pv.getTermVariable());
			varsToQuantifyInCallerPredAndCallTF.add(pv.getTermVariable());
		}
		Term retTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, inVarsToRenameInReturnTF).transform(ret_TF.getFormula());
		retTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(retTermRenamed);
		// 2.1 Rename invars of TransFormula of corresponding Call statement
		substitution.clear();
		for (final IProgramVar pv : callTF.getInVars().keySet()) {
			if (ret_TF.getOutVars().containsKey(pv)) {
				final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
				substitution.put(callTF.getInVars().get(pv), freshVar);
				varsToRenameInCallerPred.put(pv.getTermVariable(), freshVar);
				varsToQuantifyInCallerPredAndCallTF.add(freshVar);
			} else if (globalVarsAssignment.getOutVars().containsKey(pv)) {
				final Term freshVar = varsToRenameInCallerPred.get(pv.getTermVariable());
				assert freshVar != null : "added null to substitution mapping";
				substitution.put(callTF.getInVars().get(pv), freshVar);
			} else {
				substitution.put(callTF.getInVars().get(pv), pv.getTermVariable());
			}
		}
		Term callTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, outVarsToRenameInCallTF).transform(callTF.getFormula());
		callTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(callTermRenamed);
		// 2.2 We doesn't rename the outvars, because the outvars are the
		// localvars
		// of the called procedure, therefore we want to quantify them out.
		for (final IProgramVar pv : callTF.getOutVars().keySet()) {
			if (!outVarsToRenameInCallTF.containsKey(callTF.getOutVars().get(pv))) {
				final TermVariable substitutor = callTF.getOutVars().get(pv);
				varsToRenameInCalleePred.put(pv.getTermVariable(), substitutor);
				varsToQuantifyOverAll.add(substitutor);
			}
		}

		// 3. Rename the vars in calleePred, which occur as an outvar in the
		// TransFormula of Return Statement, or
		// which occur as an invar in the TransFormula of the corresponding Call
		// statement.
		// This substitution is only necessary, if we have a recursive call.
		final Term calleePredVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInCalleePred).transform(calleePred
				.getFormula());

		// 5. Substitute oldvars through fresh variables in calleePredicate.
		final Term calleePredVarsRenamedOldVarsToFreshVars = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInCalleePred)
				.transform(calleePredVarsRenamed);

		// 6. Substitute the global variables in callerPred through the fresh
		// Vars computed in (4).
		final Term callerPredVarsRenamedToFreshVars = new SafeSubstitutionWithLocalSimplification(mScript, varsToRenameInCallerPred)
				.transform(callerPred.getFormula());

		// 1. CalleePredRenamed and loc vars quantified
		final Term calleePredRenamedQuantified = PartialQuantifierElimination.quantifier(mServices, mLogger, mScript, mManagedScript,
				mSimplificationTechnique, mXnfConversionTechnique, Script.EXISTS, varsToQuantifyInCalleePred,
				calleePredVarsRenamedOldVarsToFreshVars, (Term[][]) null);
		// 2. CallTF and callerPred
		final Term calleRPredANDCallTFRenamedQuantified = PartialQuantifierElimination.quantifier(mServices, mLogger,
				mScript, mManagedScript, mSimplificationTechnique, mXnfConversionTechnique, Script.EXISTS, varsToQuantifyInCallerPredAndCallTF, 
				Util.and(mScript,
						callerPredVarsRenamedToFreshVars, callTermRenamed), (Term[][]) null);
		// 3. Result
		varsToQuantifyOverAll.addAll(allAuxVars);

		final Term result = Util.and(mScript, calleePredRenamedQuantified, retTermRenamed, calleRPredANDCallTFRenamedQuantified);
		final Term quantified = SmtUtils.quantifier(mScript, Script.EXISTS, varsToQuantifyOverAll, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;

	}
	

	public Term weakestPrecondition(final IPredicate p, final TransFormula tf) {
		if (SmtUtils.isTrue(p.getFormula())) {
			return p.getFormula();
		}
		final Set<TermVariable> varsToQuantify = new HashSet<>();
		final IValueConstruction<IProgramVar, TermVariable> substituentConstruction = new IValueConstruction<IProgramVar, TermVariable>() {

			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				final TermVariable result = constructFreshTermVariable(mManagedScript, pv);
				varsToQuantify.add(result);
				return result;
			}
			
		};
		final ConstructionCache<IProgramVar, TermVariable> termVariablesForSuccessor = new ConstructionCache<>(substituentConstruction);
		
		final Map<Term, Term> substitutionForTransFormula = new HashMap<Term, Term>();
		final Map<Term, Term> substitutionForSuccessor = new HashMap<Term, Term>();
		
		for (final Entry<IProgramVar, TermVariable> entry : tf.getOutVars().entrySet()) {
			final IProgramVar pv = entry.getKey();
			if (entry.getValue() == tf.getInVars().get(pv)) {
				// special case, variable unchanged will be renamed when
				// considering outVars
			} else {
				final TermVariable substituent = termVariablesForSuccessor.getOrConstuct(pv);
				substitutionForTransFormula.put(entry.getValue(), substituent);
				if (p.getVars().contains(pv)) {
					substitutionForSuccessor.put(pv.getTermVariable(), substituent);
				}
			}
		}

		for (final Entry<IProgramVar, TermVariable> entry : tf.getInVars().entrySet()) {
			substitutionForTransFormula.put(entry.getValue(), entry.getKey().getTermVariable());
			if (!tf.getOutVars().containsKey(entry.getKey()) && p.getVars().contains(entry.getKey())) {
				final TermVariable substituent = termVariablesForSuccessor.getOrConstuct(entry.getKey());
				substitutionForSuccessor.put(entry.getKey().getTermVariable(), substituent);
			}
		}
		
		final Term renamedTransFormula = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForTransFormula).transform(tf.getFormula());
		final Term renamedSuccessor = new SafeSubstitutionWithLocalSimplification(mScript, substitutionForSuccessor).transform(p.getFormula());
			
		final Term result = Util.or(mScript, SmtUtils.not(mScript, renamedTransFormula), renamedSuccessor);
		// Add aux vars to varsToQuantify
		varsToQuantify.addAll(tf.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;
	}

	/**
	 * Responsible for computing WP of a Call statement.
	 * 
	 */
	public Term weakestPrecondition(final IPredicate calleePred, final TransFormula call_TF,
			final TransFormula globalVarsAssignments, final TransFormula oldVarsAssignments, 
			final Set<IProgramVar> modifiableGlobals) {
		
		final InstanceProviderWpCall ip = new InstanceProviderWpCall(modifiableGlobals);
		
		Term calleePredRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final IProgramVar pv : calleePred.getVars()) {
				substitution.put(pv.getTermVariable(), ip.getOrConstuctAfterCallInstance(pv));
			}
			calleePredRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(calleePred.getFormula());
		}
		
		final Term call_TFrenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : call_TF.getInVars().entrySet()) {
				final TermVariable beforeCallInstance = ip.getOrConstuctBeforeCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : call_TF.getOutVars().entrySet()) {
				final TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), afterCallInstance);
			}
			call_TFrenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(call_TF.getFormula());
		}
		
		final Term globalVarsAssignmentsRenamed;
		{
			// for the global vars assignment, we use only "after call instances"
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : globalVarsAssignments.getInVars().entrySet()) {
				assert entry.getKey().isOldvar();
				final TermVariable beforeCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : globalVarsAssignments.getOutVars().entrySet()) {
				if (entry.getKey().isOldvar()) {
					// do nothing
				} else {
					final TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
					substitution.put(entry.getValue(), afterCallInstance);
				}
			}
			globalVarsAssignmentsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(globalVarsAssignments.getFormula());
		}
		
		final Term oldVarsAssignmentsRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : oldVarsAssignments.getInVars().entrySet()) {
				assert !entry.getKey().isOldvar();
				final TermVariable beforeCallInstance = ip.getOrConstuctBeforeCallInstance(entry.getKey()); 
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : oldVarsAssignments.getOutVars().entrySet()) {
				if (entry.getKey().isOldvar()) {
					final TermVariable afterCallInstance = ip.getOrConstuctAfterCallInstance(entry.getKey()); 
					substitution.put(entry.getValue(), afterCallInstance);
				} else {
					// do nothing
				}
			}
			oldVarsAssignmentsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(oldVarsAssignments.getFormula());
		}

		final Set<TermVariable> varsToQuantify = new HashSet<TermVariable>(ip.getFreshTermVariables());
		final Term result = Util.or(mScript,
				SmtUtils.not(mScript, Util.and(mScript, call_TFrenamed, globalVarsAssignmentsRenamed, oldVarsAssignmentsRenamed)),
				calleePredRenamed);
		varsToQuantify.addAll(call_TF.getAuxVars());
		final Term quantified = SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
		final Term pushed = new QuantifierPusher(mScript, mServices, mManagedScript).transform(quantified);
		return pushed;

	}

	/**
	 * Computes weakest precondition of a Return statement. oldvars of
	 * modifiable global variables are renamed to their representatives, and
	 * they are substituted in caller predicate and returner predicate to same
	 * fresh variables modifiable global variables are renamed to fresh
	 * variables and their occurrence in the caller predicate is substituted by
	 * the same fresh variables. InVars of returnTF are renamed to
	 * representatives, their occurrence in ..
	 * @param varsOccurringBetweenCallAndReturn 
	 * 
	 */
	public Term weakestPrecondition(final IPredicate returnerPred, final IPredicate callerPred, final TransFormula returnTF,
			final TransFormula callTF, final TransFormula globalVarsAssignments, final TransFormula oldVarAssignments,
			final Set<IProgramVar> modifiableGlobals, final Set<IProgramVar> varsOccurringBetweenCallAndReturn) {
		final InstanceProviderWpReturn ir = new InstanceProviderWpReturn(modifiableGlobals, varsOccurringBetweenCallAndReturn, returnTF.getAssignedVars());
		
		
		final Term globalVarsRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			if (globalVarsAssignments != null) {
				for (final Entry<IProgramVar, TermVariable> entry : globalVarsAssignments.getInVars().entrySet()) {
					final IProgramOldVar oldVar = (IProgramOldVar) entry.getKey(); 
					substitution.put(entry.getValue(), oldVar.getTermVariable());
				}
				for (final Entry<IProgramVar, TermVariable> entry : globalVarsAssignments.getOutVars().entrySet()) {
					if (entry.getKey() instanceof IProgramNonOldVar) {
						final TermVariable beforeCallInstance = 
								ir.getOrConstuctBeforeCallInstance(entry.getKey());
						substitution.put(entry.getValue(), beforeCallInstance);
					} else {
						assert (entry.getKey() instanceof IProgramOldVar);
					}
				}
				globalVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(globalVarsAssignments.getFormula());
			} else {
				for (final Entry<IProgramVar, TermVariable> entry : oldVarAssignments.getOutVars().entrySet()) {
					final IProgramOldVar oldVar = (IProgramOldVar) entry.getKey(); 
					substitution.put(entry.getValue(), oldVar.getTermVariable());
				}
				for (final Entry<IProgramVar, TermVariable> entry : oldVarAssignments.getInVars().entrySet()) {
					if (entry.getKey() instanceof IProgramNonOldVar) {
						final TermVariable beforeCallInstance = 
								ir.getOrConstuctBeforeCallInstance(entry.getKey());
						substitution.put(entry.getValue(), beforeCallInstance);
					} else {
						assert (entry.getKey() instanceof IProgramOldVar);
					}
				}
				globalVarsRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(oldVarAssignments.getFormula());
			}
		}
		
		final Term returnTermRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : returnTF.getInVars().entrySet()) {
				final TermVariable beforeReturnInstance = 
						ir.getOrConstuctBeforeReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeReturnInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : returnTF.getOutVars().entrySet()) {
				final TermVariable afterReturnInstance = 
						ir.getOrConstuctAfterReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), afterReturnInstance);
			}
			returnTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(returnTF.getFormula());
		}
		
		final Term callTermRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final Entry<IProgramVar, TermVariable> entry : callTF.getInVars().entrySet()) {
				final TermVariable beforeCallInstance = 
						ir.getOrConstuctBeforeCallInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeCallInstance);
			}
			for (final Entry<IProgramVar, TermVariable> entry : callTF.getOutVars().entrySet()) {
				final TermVariable beforeReturnInstance = 
						ir.getOrConstuctBeforeReturnInstance(entry.getKey());
				substitution.put(entry.getValue(), beforeReturnInstance);
			}
			callTermRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(callTF.getFormula());
		}
		
		Term callerPredRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final IProgramVar pv : callerPred.getVars()) {
				substitution.put(pv.getTermVariable(), ir.getOrConstuctBeforeCallInstance(pv));
			}
			callerPredRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(callerPred.getFormula());
		}
		
		Term returnPredRenamed;
		{
			final Map<Term, Term> substitution = new HashMap<Term, Term>();
			for (final IProgramVar pv : returnerPred.getVars()) {
				substitution.put(pv.getTermVariable(), ir.getOrConstuctAfterReturnInstance(pv));
			}
			returnPredRenamed = new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(returnerPred.getFormula());
		}

		final Set<TermVariable> varsToQuantify = new HashSet<TermVariable>(ir.getFreshTermVariables());
		assert(callTF.getAuxVars().isEmpty()) : "no auxvars allowed";
		assert(returnTF.getAuxVars().isEmpty()) : "no auxvars allowed";
		assert(globalVarsAssignments.getAuxVars().isEmpty()) : "no auxvars allowed";
		if (callerPredRenamed instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) callerPredRenamed;
			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.EXISTS) {
//			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.FORALL) {
				mLogger.warn("universally quantified caller pred");
//				throw new UnsupportedOperationException("only existentially quantified callerPred supported, but obtained " + callerPred);
			}
//			varsToQuantify.addAll(Arrays.asList(quantifiedFormula.getVariables()));
//			callerPredRenamed = ((QuantifiedFormula) callerPredRenamed).getSubformula();
		}
		if (returnPredRenamed instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) returnPredRenamed;
			if (quantifiedFormula.getQuantifier() != QuantifiedFormula.FORALL) {
				throw new UnsupportedOperationException("only universally quantified returnPred supported, but obtained " + returnerPred);
			}
//			varsToQuantify.addAll(Arrays.asList(quantifiedFormula.getVariables()));
//			returnPredRenamed = ((QuantifiedFormula) returnPredRenamed).getSubformula();
		}

		final Term callerPredANDCallANDReturnAndGlobalVars = Util.and(mScript, callerPredRenamed, returnTermRenamed,
				callTermRenamed, globalVarsRenamed);

		final Term result = Util.or(mScript, SmtUtils.not(mScript, callerPredANDCallANDReturnAndGlobalVars), returnPredRenamed);
		return SmtUtils.quantifier(mScript, Script.FORALL, varsToQuantify, result);
	}
	

	/**
	 * return true if varsOccurringBetweenCallAndReturn contains pv or 
	 * varsOccurringBetweenCallAndReturn is null (which means that the return
	 * is a pending return and possibly all vars may occur before return)
	 * @param pv
	 * @return
	 */
	private boolean varOccursBetweenCallAndReturn(
			final Set<IProgramVar> varsOccurringBetweenCallAndReturn, final IProgramVar pv) {
		if (varsOccurringBetweenCallAndReturn == null) {
			return true;
		} else {
			return varsOccurringBetweenCallAndReturn.contains(pv);
		}
	}
	
	/**
	 * Return instances of BoogieVars for computation of weakest precondition
	 * for call statements.
	 * Each instance is represented by a TermVariable.
	 * Each BoogieVar can have up to two instances: "before call" and 
	 * "after call".
	 * An instance can be the representative TermVariable for this BoogieVar
	 * of a fresh auxiliary variable. 
	 *  Objects of this class construct the fresh variables on demand and return
	 * the correct instances (which means it checks that for coinciding 
	 * instances a common TermVariable is returned). 
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	private class InstanceProviderWpCall {
		private final Set<IProgramVar> mModifiableGlobals;
		private final IValueConstruction<IProgramVar, TermVariable> mValueConstruction = new IValueConstruction<IProgramVar, TermVariable>() {
			@Override
			public TermVariable constructValue(final IProgramVar pv) {
				return constructFreshTermVariable(mManagedScript, pv);
			}
		};
		private final ConstructionCache<IProgramVar, TermVariable> mFreshVariables = new ConstructionCache<>(mValueConstruction);
		
		public InstanceProviderWpCall(final Set<IProgramVar> modifiableGlobals) {
			super();
			mModifiableGlobals = modifiableGlobals;
		}

		public TermVariable getOrConstuctBeforeCallInstance(final IProgramVar pv) {
			return pv.getTermVariable();
		}

		public TermVariable getOrConstuctAfterCallInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return mFreshVariables.getOrConstuct(pv);
				} else {
					if (mModifiableGlobals.contains(pv)) {
						return mFreshVariables.getOrConstuct(pv);
					} else {
						return pv.getTermVariable();
					}
				}
			} else {
				return mFreshVariables.getOrConstuct(pv);
			}
		}
		
		public Collection<TermVariable> getFreshTermVariables() {
			return mFreshVariables.getMap().values();
		}
	}
	
	/**
	 * Return instances of BoogieVars for computation of weakest precondition
	 * for return statements.
	 * Each instance is represented by a TermVariable.
	 * Each BoogieVar can have up to three instances: "Before call", (directly)
	 * "before return", and "after return".
	 * An instance can be the representative TermVariable for this BoogieVar
	 * of a fresh auxiliary variable. In some cases these instances 
	 * (fresh auxiliary variable) coincide.
	 * Objects of this class construct the fresh variables on demand and return
	 * the correct instances (which means it checks that for coinciding 
	 * instances a common TermVariable is returned). 
	 * 
	 * @author heizmann@informatik.uni-freiburg.de
	 *
	 */
	private class InstanceProviderWpReturn {
		private final Map<IProgramVar, TermVariable> mBeforeCall = new HashMap<IProgramVar, TermVariable>();
		private final Map<IProgramVar, TermVariable> mAfterReturn = new HashMap<IProgramVar, TermVariable>();
		private final Map<IProgramVar, TermVariable> mBeforeAfterCallCoincide = new HashMap<IProgramVar, TermVariable>();
		private final Set<IProgramVar> mModifiableGlobals;
		private final Set<IProgramVar> mVarsOccurringBetweenCallAndReturn;
		private final Set<IProgramVar> mAssignedOnReturn;
		private final Set<TermVariable> mFreshTermVariables = new HashSet<TermVariable>();
		
		public InstanceProviderWpReturn(final Set<IProgramVar> modifiableGlobals,
				final Set<IProgramVar> varsOccurringBetweenCallAndReturn,
				final Set<IProgramVar> assignedOnReturn) {
			super();
			mModifiableGlobals = modifiableGlobals;
			mVarsOccurringBetweenCallAndReturn = varsOccurringBetweenCallAndReturn;
			mAssignedOnReturn = assignedOnReturn;
		}

		public TermVariable getOrConstuctBeforeCallInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return getOrConstructTermVariable(mBeforeAfterCallCoincide, pv);
				} else {
					if (mModifiableGlobals.contains(pv)) {
						return getOrConstructTermVariable(mBeforeCall, pv);
					} else {
						if (doesVarOccurBetweenCallAndReturn((IProgramNonOldVar) pv)) {
							return pv.getTermVariable();
						} else {
							return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mBeforeCall);
						}
					}
				}
			} else {
				return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mBeforeCall);
			}
		}

		public TermVariable getOrConstuctBeforeReturnInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return pv.getTermVariable();
				} else {
					throw new AssertionError("illegal case");
				}
			} else {
				return pv.getTermVariable();
			}
		}
		
		public TermVariable getOrConstuctAfterReturnInstance(final IProgramVar pv) {
			if (pv.isGlobal()) {
				if (pv.isOldvar()) {
					return getOrConstructTermVariable(mBeforeAfterCallCoincide, pv);
				} else {
					if (mModifiableGlobals.contains(pv)) {
						if (mAssignedOnReturn.contains(pv)) {
							return getOrConstructTermVariable(mAfterReturn, pv);
						} else {
							return pv.getTermVariable();
						}
					} else {
						if (doesVarOccurBetweenCallAndReturn((IProgramNonOldVar) pv)) {
							if (mAssignedOnReturn.contains(pv)) {
								return getOrConstructTermVariable(mAfterReturn, pv);
							} else {
								return pv.getTermVariable();
							}
						} else {
							return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mAfterReturn);
						}
					}
				}
			} else {
				return getOrConstructTermVariable_BeforeAndAfterIfNecessary(pv, mAfterReturn);
			}
		}
		
		public Set<TermVariable> getFreshTermVariables() {
			return mFreshTermVariables;
		}

		private boolean doesVarOccurBetweenCallAndReturn(
				final IProgramNonOldVar nonOld) {
			return mVarsOccurringBetweenCallAndReturn.contains(nonOld);
		}

		/**
		 * getOrConstructTermVariable for map if pv is assigned on return
		 * (which means instance before call and after return is different)
		 * and getOrConstructTermVariable for the mBeforeAfterCallCoincide map
		 * if the variable is not assigned on return.
		 */
		private TermVariable getOrConstructTermVariable_BeforeAndAfterIfNecessary(final IProgramVar pv, final Map<IProgramVar, TermVariable> map) {
			assert map == mBeforeCall || map == mAfterReturn;
			if (mAssignedOnReturn.contains(pv)) {
				return getOrConstructTermVariable(map, pv); 
			} else {
				return getOrConstructTermVariable(mBeforeAfterCallCoincide, pv);
			}
		}
		
		private TermVariable getOrConstructTermVariable(
				final Map<IProgramVar, TermVariable> map, final IProgramVar pv) {
			TermVariable tv = map.get(pv);
			if (tv == null) {
				tv = constructFreshTermVariable(mManagedScript, pv);
				mFreshTermVariables.add(tv);
				map.put(pv, tv);
			}
			return tv;
		}
		
	}


	private enum GlobalType {
		OLDVAR, NONOLDVAR
	}

	/**
	 * Returns copy of map restricted to keys that are of the given GlobalType
	 * (oldVar or nonOldVar).
	 */
	private Map<IProgramVar, TermVariable> restrictMap(final Map<IProgramVar, TermVariable> map, final GlobalType globalType) {
		final Map<IProgramVar, TermVariable> result = new HashMap<IProgramVar, TermVariable>();
		for (final Entry<IProgramVar, TermVariable> entry : map.entrySet()) {
			if ((globalType == GlobalType.OLDVAR) == (entry.getKey().isOldvar())) {
				result.put(entry.getKey(), entry.getValue());
			}
		}
		return result;
	}

	/**
	 * Substitutes in the given formula the values of the given map by fresh
	 * variables, and puts the substitution from the term variable to the same
	 * fresh variable into the second given map. It also adds the fresh variable
	 * to the given set.
	 * 
	 * @param varsToBeSubstituted
	 *            - the occurrence of the values of this map in the given
	 *            formula are renamed to fresh variables
	 * @param formulaToBeSubstituted
	 *            - the formula in which the variables should be substituted
	 * @param varsToBeSubstitutedByFreshVars
	 *            - map to which the substitutions from corresponding term
	 *            variables to fresh variables should be added
	 * @param varsToQuantify
	 *            - set, to which the fresh variables are added
	 * @return formulaToBeSubstituted, where the variables are substituted by
	 *         fresh variables
	 */
	private Term substituteToFreshVarsAndAddToQuantify(final Map<IProgramVar, TermVariable> varsToBeSubstituted,
			final Term formulaToBeSubstituted, final Map<TermVariable, Term> varsToBeSubstitutedByFreshVars,
			final Set<TermVariable> varsToQuantify) {
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (final IProgramVar pv : varsToBeSubstituted.keySet()) {
			final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
			substitution.put(varsToBeSubstituted.get(pv), freshVar);
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(pv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(formulaToBeSubstituted);
	}

	/**
	 * Substitutes in the given formula the values of the given map by the keys
	 * of the given map. It also puts a substitution from the keys of the given
	 * map to fresh variables into the second given map and adds the fresh
	 * variables to the given set.
	 * 
	 * @param varsToBeSubstituted
	 *            - the occurrence of the values of this map in the given
	 *            formula are substituted by the keys of this map
	 * @param formulaToBeSubstituted
	 *            - the formula in which the variables should be substituted
	 * @param varsToBeSubstitutedByFreshVars
	 *            - map to which the substitutions from the keys of the map
	 *            "varsToBeSubstituted" to fresh variables should be added
	 * @param varsToQuantify
	 *            - set, to which the fresh variables are added
	 * @return formulaToBeSubstituted, where the variables are substituted by
	 *         the corresponding term variables
	 */
	private Term substituteToRepresantativesAndAddToQuantify(final Map<IProgramVar, TermVariable> varsToBeSubstituted,
			final Term formulaToBeSubstituted, final Map<Term, Term> varsToBeSubstitutedByFreshVars,
			final Set<TermVariable> varsToQuantify) {
		final Map<Term, Term> substitution = new HashMap<Term, Term>();
		for (final IProgramVar pv : varsToBeSubstituted.keySet()) {
			final TermVariable freshVar = constructFreshTermVariable(mManagedScript, pv);
			substitution.put(varsToBeSubstituted.get(pv), pv.getTermVariable());
			if (varsToBeSubstitutedByFreshVars != null) {
				varsToBeSubstitutedByFreshVars.put(pv.getTermVariable(), freshVar);
			}
			if (varsToQuantify != null) {
				varsToQuantify.add(freshVar);
			}
		}
		return new SafeSubstitutionWithLocalSimplification(mScript, substitution).transform(formulaToBeSubstituted);
	}
}
