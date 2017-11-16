/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.hopcroft;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IIncomingTransitionlet;

public class IncomingsIntCall<LETTER, STATE> extends Incomings<LETTER, STATE> {
	// visited letters
	private final Set<LETTER> mVisitedLettersInternal;
	private final Set<LETTER> mVisitedLettersCall;
	// flag to handle both internal and call transitions in one class
	private boolean mIsInternal;

	public IncomingsIntCall(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter) {
		super(operand, splitter);
		mVisitedLettersInternal = new HashSet<>();
		mVisitedLettersCall = new HashSet<>();
	}

	@Override
	public boolean hasNext() {
		if (mNextLetter != null) {
			// can only happen if this method was called twice without calling next()
			return true;
		}
		while (hasStatesLeft()) {
			// check if there is a next internal letter
			if (mNextLetters == null) {
				mIsInternal = true;
				mNextLetters = mOperand.lettersInternalIncoming(getCurrentState()).iterator();
			}
			if (findFreshLetter()) {
				return true;
			}
			if (mIsInternal) {
				// also try call letters
				mIsInternal = false;
				mNextLetters = mOperand.lettersCallIncoming(getCurrentState()).iterator();
				if (findFreshLetter()) {
					return true;
				}
			}
			tryNextState();
		}
		return false;
	}

	@Override
	protected Set<LETTER> getVisitedLetters() {
		return mIsInternal ? mVisitedLettersInternal : mVisitedLettersCall;
	}

	@Override
	protected BiFunction<STATE, LETTER, Iterable<? extends IIncomingTransitionlet<LETTER, STATE>>>
			getIncomingProvider() {
		return mIsInternal ? mOperand::internalPredecessors : mOperand::callPredecessors;
	}
}
