/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

/**
 * IHoareTripleChecker that "protects" another IHoareTripleChecker from
 * intricate predicates.
 * The m_PredicateUnifer defines what an intricate predicates is.
 * If the Hoare triple that should be checked contains an intricate predicate
 * we return Validity.NOT_CHECKED. Otherwise we ask the "protected" 
 * IHoareTripleChecker.
 * @author Matthias Heizmann
 *
 */
public class ProtectiveHoareTripleChecker implements IHoareTripleChecker {
	
	private final IHoareTripleChecker m_ProtectedHoareTripleChecker;
	private final PredicateUnifier m_PredicateUnifer;
	
	public ProtectiveHoareTripleChecker(
			IHoareTripleChecker protectedHoareTripleChecker,
			PredicateUnifier predicateUnifer) {
		super();
		m_ProtectedHoareTripleChecker = protectedHoareTripleChecker;
		m_PredicateUnifer = predicateUnifer;
	}

	@Override
	public Validity checkInternal(IPredicate pre, IInternalAction act, IPredicate succ) {
		if (m_PredicateUnifer.isIntricatePredicate(pre) || 
				m_PredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		} else {
			return m_ProtectedHoareTripleChecker.checkInternal(pre, act, succ);
		}
	}

	@Override
	public Validity checkCall(IPredicate pre, ICallAction act, IPredicate succ) {
		if (m_PredicateUnifer.isIntricatePredicate(pre) || 
				m_PredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		} else {
			return m_ProtectedHoareTripleChecker.checkCall(pre, act, succ);
		}
	}

	@Override
	public Validity checkReturn(IPredicate preLin, IPredicate preHier,
			IReturnAction act, IPredicate succ) {
		if (m_PredicateUnifer.isIntricatePredicate(preLin) || 
				m_PredicateUnifer.isIntricatePredicate(preHier) || m_PredicateUnifer.isIntricatePredicate(succ)) {
			return Validity.NOT_CHECKED;
		} else {
			return m_ProtectedHoareTripleChecker.checkReturn(preLin, preHier, act, succ);
		}
	}
	
	

	@Override
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return m_ProtectedHoareTripleChecker.getEdgeCheckerBenchmark();
	}

	public IHoareTripleChecker getProtectedHoareTripleChecker() {
		return m_ProtectedHoareTripleChecker;
	}

	@Override
	public void releaseLock() {
		m_ProtectedHoareTripleChecker.releaseLock();
	}
	
	

}
