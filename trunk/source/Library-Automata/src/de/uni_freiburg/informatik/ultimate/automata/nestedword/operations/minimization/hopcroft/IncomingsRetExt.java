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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;

public class IncomingsRetExt<LETTER, STATE> extends Incomings<LETTER, STATE> {
	private final Partition<STATE> mPartition;
	private final Set<LETTER> mVisitedLetters;

	public IncomingsRetExt(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition) {
		super(operand, splitter);
		mPartition = partition;
		mVisitedLetters = new HashSet<>();
	}

	@Override
	public boolean hasNext() {
		if (mNextLetter != null) {
			// can only happen if this method was called twice without calling next()
			return true;
		}
		while (hasStatesLeft()) {
			// check if there is a next return letter
			if (mNextLetters == null) {
				mNextLetters = mOperand.lettersReturnIncoming(getCurrentState()).iterator();
			}
			if (findFreshLetter()) {
				return true;
			}
			tryNextState();
		}
		return false;
	}

	@Override
	public Collection<STATE> next() {
		assert mNextLetter != null : "This iterator relies on first calling hasNext() before calling next().";

		final Collection<STATE> res = determineSplitsWithGivenLetter();

		assert !getVisitedLetters().contains(mNextLetter) : "A letter was visited twice.";
		getVisitedLetters().add(mNextLetter);
		mNextLetter = null;

		return res;
	}

	@Override
	protected Set<LETTER> getVisitedLetters() {
		return mVisitedLetters;
	}

	private Collection<STATE> determineSplitsWithGivenLetter() {
		final Collection<STATE> res = new ArrayList<>();
		for (int i = mSplitter.size() - 1; i >= mStatesIdx; --i) {
			final STATE state = mSplitter.get(i);
			for (final IncomingReturnTransition<LETTER, STATE> trans : mOperand.returnPredecessors(state,
					mNextLetter)) {
				// TODO
			}
		}
		return res;
	}
}
