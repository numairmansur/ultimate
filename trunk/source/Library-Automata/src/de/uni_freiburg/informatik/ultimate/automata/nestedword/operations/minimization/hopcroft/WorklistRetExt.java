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
import java.util.PriorityQueue;
import java.util.function.Consumer;

public class WorklistRetExt<STATE> extends Worklist<STATE> {
	private final PriorityQueue<Partition<STATE>.Block> mQueueExt;
	private final Consumer<Partition<STATE>.Block> mAddBlockFunctionExt;
	private final Consumer<Partition<STATE>.Block> mRemoveBlockFunctionExt;

	private WorklistRetExt(final int initialCapacity, final Consumer<Partition<STATE>.Block> addBlockFunction,
			final Consumer<Partition<STATE>.Block> removeBlockFunction,
			final Consumer<Partition<STATE>.Block> addBlockFunctionExt,
			final Consumer<Partition<STATE>.Block> removeBlockFunctionExt) {
		super(initialCapacity, addBlockFunction, removeBlockFunction);
		mQueueExt = new PriorityQueue<>(initialCapacity, new BlockComparator());
		mAddBlockFunctionExt = addBlockFunctionExt;
		mRemoveBlockFunctionExt = removeBlockFunctionExt;
	}

	public static <STATE> WorklistRetExt<STATE> getWorklistRet(final int operandSize) {
		return new WorklistRetExt<>(Math.max(operandSize, 1), Partition<STATE>.Block::addToWorklistRet,
				Partition<STATE>.Block::removeFromWorklistRet, Partition<STATE>.Block::addToWorklistRetExt,
				Partition<STATE>.Block::removeFromWorklistRetExt);
	}

	@Override
	public void add(final Partition<STATE>.Block block) {
		if (!block.isInWorklistRet()) {
			super.add(block);
		}
		if (!block.isInWorklistRetExt()) {
			assert !mQueueExt.contains(block) : "Adding a block to worklist that is already present.";
			mAddBlockFunctionExt.accept(block);
			mQueueExt.add(block);
		}
	}

	public boolean isEmptyExt() {
		return mQueueExt.isEmpty();
	}

	public Collection<STATE> pollExt() {
		final Partition<STATE>.Block block = mQueueExt.poll();
		mRemoveBlockFunctionExt.accept(block);
		return block;
	}

	@Override
	public String toString() {
		final StringBuilder builder = new StringBuilder();
		builder.append("(");
		super.toStringHelper(builder);
		builder.append(", ");
		addToStringBuilder(builder, mQueueExt);
		builder.append(")");
		return builder.toString();
	}
}
