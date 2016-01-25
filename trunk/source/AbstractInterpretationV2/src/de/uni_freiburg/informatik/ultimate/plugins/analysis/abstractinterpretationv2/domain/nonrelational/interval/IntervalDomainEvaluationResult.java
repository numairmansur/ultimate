/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluator;

/**
 * Class for evaluation results used to return both, a new abstract state and an evaluated value for evaluators.
 * 
 * @author Marius Greitschus <greitsch@informatik.uni-freiburg.de>
 *
 */
public class IntervalDomainEvaluationResult implements IEvaluationResult<IntervalDomainEvaluationResult> {

	private IntervalDomainValue mValue;
	private IntervalDomainState mAbstractState;
	private BooleanValue mBooleanValue;

	/**
	 * Default constructor for an {@link IntervalDomainEvaluationResult}.
	 * 
	 * @param value
	 *            The {@link IntervalDomainValue} to set in the result.
	 * @param state
	 *            The {@link IntervalDomainState} to set in the result.
	 * @param booleanValue
	 *            The {@link BooleanValue} to set in the result.
	 */
	protected IntervalDomainEvaluationResult(IntervalDomainValue value, IntervalDomainState state,
	        BooleanValue booleanValue) {
		mValue = value;
		mAbstractState = state;
		mBooleanValue = booleanValue;
	}

	/**
	 * @return The evaluated state that is the result of calling the {@link IEvaluator#evaluate(IAbstractState)} method.
	 */
	protected IntervalDomainState getEvaluatedState() {
		return mAbstractState;
	}

	/**
	 * @return The evaluated value that is the result of calling the {@link IEvaluator#evaluate(IAbstractState)} method.
	 */
	protected IntervalDomainValue getEvaluatedValue() {
		return mValue;
	}

	@Override
	public IntervalDomainEvaluationResult getResult() {
		return this;
	}

	@Override
	public BooleanValue getBooleanValue() {
		return mBooleanValue;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Value: ");
		sb.append(mValue);
		sb.append(" -- Boolean Value: ");
		sb.append(mBooleanValue);
		sb.append(" -- State: ");
		sb.append(mAbstractState);
		return sb.toString();
	}
}
