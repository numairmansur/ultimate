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
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;

public class IncomingsRet<LETTER, STATE> extends Incomings<LETTER, STATE> {
	private enum ReturnSplitMode {
		/**
		 * Old MinimizeSevpa behavior. TODO describe
		 */
		LAZY,
		/**
		 * Old ShrinkNwa behavior. TODO describe
		 */
		EAGER,
		/**
		 * Mixed behavior. TODO describe
		 */
		MIXED
	}

	private final Partition<STATE> mPartition;
	private final Set<LETTER> mVisitedLetters;
	// maps block of (linear/hierarchical) predecessors to set of (hierarchical/linear) predecessors
	private final HashMap<Partition<STATE>.Block, Set<STATE>> mBlock2set;
	private Iterator<Set<STATE>> mMarkSets;
	private ReturnSplitMode mMode;
	private Function<IncomingReturnTransition<LETTER, STATE>, STATE> mFirstStateFromTransition;
	private Function<IncomingReturnTransition<LETTER, STATE>, STATE> mSecondStateFromTransition;
	private boolean mLazyLinMode;

	public IncomingsRet(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition) {
		this(operand, splitter, partition, ReturnSplitMode.LAZY);
	}

	public IncomingsRet(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition, final ReturnSplitMode mode) {
		super(operand, splitter);
		mPartition = partition;
		mMode = mode;
		mVisitedLetters = new HashSet<>();
		mBlock2set = new HashMap<>();
		mMarkSets = Collections.emptyIterator();
		changeLazyMode(true);
	}

	private void changeLazyMode(final boolean isLin) {
		mLazyLinMode = isLin;
		if (isLin) {
			mFirstStateFromTransition = IncomingReturnTransition::getLinPred;
			mSecondStateFromTransition = IncomingReturnTransition::getHierPred;
		} else {
			mFirstStateFromTransition = IncomingReturnTransition::getHierPred;
			mSecondStateFromTransition = IncomingReturnTransition::getLinPred;
		}
		// reset things
		mStatesIdx = 0;
		mNextLetter = null;
		mNextLetters = null;
		mVisitedLetters.clear();
		mBlock2set.clear();
	}

	private boolean hasNextLetter() {
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

		// no state/letter left, continue depending on the mode
		switch (mMode) {
			case LAZY:
				if (mLazyLinMode) {
					changeLazyMode(false);
					return hasNextLetter();
				}
				return false;

			case EAGER:
			case MIXED:
			default:
				throw new UnsupportedOperationException("Mode " + mMode + "not supported yet.");
		}
	}

	@Override
	public boolean hasNext() {
		while (!mMarkSets.hasNext()) {
			if (!hasNextLetter()) {
				return false;
			}
			assert mNextLetter != null : "This iterator relies on first calling hasNext() before calling next().";
			determineModeAndFillMap();

			assert !getVisitedLetters().contains(mNextLetter) : "A letter was visited twice.";
			getVisitedLetters().add(mNextLetter);
			mNextLetter = null;
		}
		return true;
	}

	private void determineModeAndFillMap() {
		for (int i = mSplitter.size() - 1; i >= mStatesIdx; --i) {
			final STATE state = mSplitter.get(i);
			for (final IncomingReturnTransition<LETTER, STATE> trans : mOperand.returnPredecessors(state,
					mNextLetter)) {
				addStateToSetInBlockMap(mFirstStateFromTransition.apply(trans), mSecondStateFromTransition.apply(trans), mBlock2set);
			}
		}

		switch (mMode) {
			case LAZY:
				mMarkSets = new LinkedHashSet<>(mBlock2set.values()).iterator();
				break;
			case EAGER:
			case MIXED:
			default:
				throw new UnsupportedOperationException("Mode " + mMode + "not supported yet.");
		}
	}

	private void addStateToSetInBlockMap(final STATE state, final STATE blockState,
			final HashMap<Partition<STATE>.Block, Set<STATE>> map) {
		final Partition<STATE>.Block block = mPartition.getBlock(blockState);
		Set<STATE> set = map.get(block);
		if (set == null) {
			set = new HashSet<>();
			map.put(block, set);
		}
		set.add(state);
	}

	@Override
	public Collection<STATE> next() {
		return mMarkSets.next();
	}

	@Override
	protected Set<LETTER> getVisitedLetters() {
		return mVisitedLetters;
	}
}
