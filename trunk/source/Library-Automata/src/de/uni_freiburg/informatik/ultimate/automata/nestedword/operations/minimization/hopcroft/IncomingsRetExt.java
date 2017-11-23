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
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.LinkedHashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.SymmetricHashRelation;

public class IncomingsRetExt<LETTER, STATE> extends Incomings<LETTER, STATE> {
	private final IDoubleDeckerAutomaton<LETTER, STATE> mDoubleDecker;
	private final Partition<STATE> mPartition;
	private final Set<LETTER> mVisitedLetters;

	public IncomingsRetExt(final IDoubleDeckerAutomaton<LETTER, STATE> operand, final Collection<STATE> splitter,
			final Partition<STATE> partition) {
		super(operand, splitter);
		mDoubleDecker = operand;
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

		final Pair<Collection<STATE>, Boolean> pair = determineSplitsWithGivenLetter();

		if (pair.getSecond()) {
			// letter has been analyzed completely
			assert !getVisitedLetters().contains(mNextLetter) : "A letter was visited twice.";
			getVisitedLetters().add(mNextLetter);
			mNextLetter = null;
		}
		return pair.getFirst();
	}

	@Override
	protected Set<LETTER> getVisitedLetters() {
		return mVisitedLetters;
	}

	private Pair<Collection<STATE>, Boolean> determineSplitsWithGivenLetter() {
		// find pairs of linear/hierarchical blocks
		final LinkedHashRelation<Partition<STATE>.Block, Partition<STATE>.Block> hierBlock2linBlocks =
				new LinkedHashRelation<>();
		for (int i = mSplitter.size() - 1; i >= mStatesIdx; --i) {
			final STATE state = mSplitter.get(i);
			for (final IncomingReturnTransition<LETTER, STATE> trans : mOperand.returnPredecessors(state,
					mNextLetter)) {
				final Partition<STATE>.Block linBlock = mPartition.getBlock(trans.getLinPred());
				final Partition<STATE>.Block hierBlock = mPartition.getBlock(trans.getHierPred());
				hierBlock2linBlocks.addPair(hierBlock, linBlock);
			}
		}

		return determineSplitsWithGivenLetterAndPairs(hierBlock2linBlocks);
	}

	private Pair<Collection<STATE>, Boolean> determineSplitsWithGivenLetterAndPairs(
			final LinkedHashRelation<Partition<STATE>.Block, Partition<STATE>.Block> hierBlock2linBlocks) {
		final ArrayList<STATE> res = new ArrayList<>();
		boolean fullAnalysis = true;

		for (final Entry<Partition<STATE>.Block, Partition<STATE>.Block> pair : hierBlock2linBlocks.entrySet()) {
			final Partition<STATE>.Block hierBlock = pair.getKey();
			final Partition<STATE>.Block linBlock = pair.getValue();
			final Set<Partition<STATE>.Block>[][] linColumns = initializeMatrix(hierBlock.size());
			int j = 0;
			for (final STATE hier : hierBlock) {
				final Set<Partition<STATE>.Block>[] linColumn = initializeArray(linBlock.size());
				int i = 0;
				for (final STATE lin : linBlock) {
					linColumn[i++] = createLinColumn(hier, lin);
				}
				linColumns[j++] = linColumn;
			}
			fullAnalysis = fullAnalysis && makeConsistent(linColumns, linBlock, hierBlock);
		}

		return new Pair<>(res, fullAnalysis);
	}

	private Set<Partition<STATE>.Block> createLinColumn(final STATE hier, final STATE lin) {
		final Set<Partition<STATE>.Block> succBlocks;
		if (!mDoubleDecker.isDoubleDecker(lin, hier)) {
			return null;
		}
		succBlocks = new HashSet<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(lin, hier, mNextLetter)) {
			succBlocks.add(mPartition.getBlock(trans.getSucc()));
		}
		return succBlocks;
	}

	private boolean makeConsistent(final Set<Partition<STATE>.Block>[][] linColumns,
			final Partition<STATE>.Block linBlock, final Partition<STATE>.Block hierBlock) {
		final Separation separation = new Separation();

		// simple, unambiguous separation (vertical and horizontal)
		final Set<Partition<STATE>.Block>[] hierRow = initializeArray(hierBlock.size());
		for (int j = 0; j < linColumns.length; ++j) {
			final Set<Partition<STATE>.Block>[] linColumn = linColumns[j];
			if (j == 0) {
				makeLineConsistent(linColumn, linBlock, separation);
			}

			for (int i = 0; i < linColumn.length; ++i) {
				hierRow[i] = linColumns[j][i];
			}
			makeLineConsistent(hierRow, hierBlock, separation);
		}

		// disjunctive separation (diagonal)
		if (linBlock.size() > 1 && hierBlock.size() > 0) {
			// FIXME
		}

		return createConsistentSeparation(separation);
	}

	private void makeLineConsistent(final Set<Partition<STATE>.Block>[] targetBlocksLine,
			final Partition<STATE>.Block block, final Separation separation) {
		final Partition<STATE>.Block.StatesIterator it1 = block.getStatesIterator();
		int i = 0;
		while (it1.hasNext()) {
			final STATE s1 = it1.next();
			final Set<Partition<STATE>.Block> targetBlocks1 = targetBlocksLine[i];
			final Partition<STATE>.Block.StatesIterator it2 = block.getStatesIterator(it1);
			int j = i + 1;
			while (it2.hasNext()) {
				final STATE s2 = it2.next();
				final Set<Partition<STATE>.Block> targetBlocks2 = targetBlocksLine[j];
				++j;
				if (!targetBlocks1.equals(targetBlocks2)) {
					separation.separate(block, s1, s2);
				}
			}
			++i;
		}
	}

	private boolean createConsistentSeparation(final Separation separation) {
		for (final Entry<Partition<STATE>.Block, SymmetricHashRelation<STATE>> entry : separation.mBlock2differences
				.entrySet()) {
			final Partition<STATE>.Block block = entry.getKey();
			final SymmetricHashRelation<STATE> differences = entry.getValue();
		}
		// FIXME
		return false;
	}

	@SuppressWarnings("unchecked")
	private Set<Partition<STATE>.Block>[] initializeArray(final int numberOfStates) {
		return new Set[numberOfStates];
	}

	@SuppressWarnings("unchecked")
	private Set<Partition<STATE>.Block>[][] initializeMatrix(final int numberOfStates) {
		return new Set[numberOfStates][];
	}

	private class Separation {
		private final Map<Partition<STATE>.Block, SymmetricHashRelation<STATE>> mBlock2differences;

		public Separation() {
			mBlock2differences = new LinkedHashMap<>();
		}

		public void separate(final Partition<STATE>.Block block, final STATE s1, final STATE s2) {
			SymmetricHashRelation<STATE> differences = mBlock2differences.get(block);
			if (differences == null) {
				differences = new SymmetricHashRelation<>();
				mBlock2differences.put(block, differences);
			}
			differences.addPair(s1, s2);
		}
	}
}
