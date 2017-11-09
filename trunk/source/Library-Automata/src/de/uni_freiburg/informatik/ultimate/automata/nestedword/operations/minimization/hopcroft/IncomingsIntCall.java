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

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IIncomingTransitionlet;

public class IncomingsIntCall<LETTER, STATE> implements Iterator<Iterable<STATE>> {
	// operand (for finding incoming transitions)
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	// splitter states
	private final ArrayList<STATE> mSplitter;
	// current state index
	private int mStatesIdx;
	// visited letters
	private final Set<LETTER> mVisitedLettersInternal;
	private final Set<LETTER> mVisitedLettersCall;
	// next letter to visit
	private LETTER mNextLetter;
	private Iterator<LETTER> mNextLetters;
	private boolean mIsInternal;

	public IncomingsIntCall(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter) {
		mOperand = operand;
		mSplitter = new ArrayList<>(splitter);
		mStatesIdx = 0;
		mVisitedLettersInternal = new HashSet<>();
		mVisitedLettersCall = new HashSet<>();
		mNextLetter = null;
		mNextLetters = null;
	}

	@Override
	public boolean hasNext() {
		if (mNextLetter != null) {
			// can only happen if this method was called twice without calling next()
			return true;
		}
		while (mStatesIdx < mSplitter.size()) {
			// check if there is a next internal letter
			if (mNextLetters == null) {
				mIsInternal = true;
				mNextLetters = getIncomingLetters();
			}
			if (findFreshLetter()) {
				return true;
			}
			if (mIsInternal) {
				// also try call letters
				mIsInternal = false;
				mNextLetters = getIncomingLetters();
				if (findFreshLetter()) {
					return true;
				}
			}

			// try the next state
			mNextLetters = null;
			++mStatesIdx;
		}
		return false;
	}

	@Override
	public Collection<STATE> next() {
		assert mNextLetter != null : "This iterator relies on first calling hasNext() before calling next().";

		final Collection<STATE> res = new ArrayList<>();
		final BiFunction<STATE, LETTER, Iterable<? extends IIncomingTransitionlet<LETTER, STATE>>> getTransitions =
				mIsInternal ? mOperand::internalPredecessors : mOperand::callPredecessors;
		for (int i = mSplitter.size() - 1; i >= mStatesIdx; --i) {
			final STATE state = mSplitter.get(i);
			for (final IIncomingTransitionlet<LETTER, STATE> trans : getTransitions.apply(state, mNextLetter)) {
				res.add(trans.getPred());
			}
		}

		final Set<LETTER> visitedLetters = mIsInternal ? mVisitedLettersInternal : mVisitedLettersCall;
		assert !visitedLetters.contains(mNextLetter) : "A letter was visited twice.";
		visitedLetters.add(mNextLetter);
		mNextLetter = null;

		return res;
	}

	private boolean findFreshLetter() {
		final Predicate<LETTER> pred = mIsInternal ? mVisitedLettersInternal::contains : mVisitedLettersCall::contains;
		while (mNextLetters.hasNext()) {
			final LETTER letter = mNextLetters.next();
			if (!pred.test(letter)) {
				mNextLetter = letter;
				return true;
			}
		}
		return false;
	}

	private Iterator<LETTER> getIncomingLetters() {
		return mIsInternal
				? mOperand.lettersInternalIncoming(mSplitter.get(mStatesIdx)).iterator()
				: mOperand.lettersCallIncoming(mSplitter.get(mStatesIdx)).iterator();
	}
}
