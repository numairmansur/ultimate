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
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class IncomingsRet<LETTER, STATE> extends Incomings<LETTER, STATE> {
	private final Partition<STATE> mPartition;
	private final Set<LETTER> mVisitedLetters;
	// maps block of (linear/hierarchical) predecessors to set of (hierarchical/linear) predecessors
	private final LinkedHashMap<Partition<STATE>.Block, Pair<Integer, Set<STATE>>> mBlock2sizeAndSet;
	private Iterator<Set<STATE>> mMarkSets;
	private Function<IncomingReturnTransition<LETTER, STATE>, STATE> mFirstStateFromTransition;
	private Function<IncomingReturnTransition<LETTER, STATE>, STATE> mSecondStateFromTransition;
	private boolean mLazyLinMode;

	public IncomingsRet(final INestedWordAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition) {
		super(operand, splitter);
		mPartition = partition;
		mVisitedLetters = new HashSet<>();
		mBlock2sizeAndSet = new LinkedHashMap<>();
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
		mBlock2sizeAndSet.clear();
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
		// no state/letter left
		if (mLazyLinMode) {
			changeLazyMode(false);
			return hasNextLetter();
		}
		return false;
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
				addStateToSetInBlockMap(mFirstStateFromTransition.apply(trans), mSecondStateFromTransition.apply(trans),
						mBlock2sizeAndSet);
			}
		}
		mMarkSets = new BlocksIterator();
	}

	private void addStateToSetInBlockMap(final STATE state, final STATE blockState,
			final LinkedHashMap<Partition<STATE>.Block, Pair<Integer, Set<STATE>>> block2sizeAndSet2) {
		final Partition<STATE>.Block block = mPartition.getBlock(blockState);
		final Pair<Integer, Set<STATE>> pair = block2sizeAndSet2.get(block);
		final Set<STATE> set;
		if (pair == null) {
			set = new HashSet<>();
			block2sizeAndSet2.put(block, new Pair<>(block.size(), set));
		} else {
			set = pair.getSecond();
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

	/**
	 * Skips those sets that were created from a split via blocks whose size has already changed since the analysis. We
	 * can save this split because we will make a more precise split in the next iteration.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private class BlocksIterator implements Iterator<Set<STATE>> {
		private final Iterator<Entry<Partition<STATE>.Block, Pair<Integer, Set<STATE>>>> mIt =
				new LinkedHashSet<>(mBlock2sizeAndSet.entrySet()).iterator();
		private Set<STATE> mNext;

		@Override
		public boolean hasNext() {
			while (mIt.hasNext()) {
				final Entry<Partition<STATE>.Block, Pair<Integer, Set<STATE>>> entry = mIt.next();
				final Pair<Integer, Set<STATE>> pair = entry.getValue();
				if (entry.getKey().size() == pair.getFirst()) {
					mNext = pair.getSecond();
					return true;
				}
			}
			mNext = null;
			return false;
		}

		@Override
		public Set<STATE> next() {
			assert mNext != null;
			final Set<STATE> next = mNext;
			mNext = null;
			return next;
		}
	}
}
