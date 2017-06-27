/*
 * Copyright (C) 2017 Moritz Mohr (mohrm@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;

public class IcfgLoop<INLOC extends IcfgLocation> {

	private final Set<IcfgLoop<INLOC>> mNestedLoops;
	private final Set<INLOC> mLoopbody;
	private final INLOC mHead;
	private final Set<INLOC> mNestedNodes;
	private final Set<ArrayList<IcfgEdge>> mPaths;
	private final IUltimateServiceProvider mServices;

	public IcfgLoop(final IUltimateServiceProvider services) {
		this(services, new HashSet<>(), null);
	}

	public IcfgLoop(final IUltimateServiceProvider services, final Set<INLOC> loopNodes, final INLOC head) {
		mNestedLoops = new HashSet<>();
		mLoopbody = new HashSet<>(loopNodes);
		mHead = head;
		mNestedNodes = new HashSet<>();
		mPaths = new HashSet<>();
		mServices = services;
	}

	public void addAll(final Set<INLOC> loopNodes) {
		mLoopbody.addAll(loopNodes);
	}

	public void addNestedLoop(final IcfgLoop<INLOC> loopNodes) {
		for (final IcfgLoop<INLOC> nestedLoop : mNestedLoops) {
			if (nestedLoop.contains(loopNodes.getHead())) {
				nestedLoop.addNestedLoop(loopNodes);
				mNestedNodes.addAll(loopNodes.getLoopbody());
				return;
			}
		}

		mNestedLoops.add(loopNodes);
	}

	public boolean hasNestedLoops() {
		return !mNestedLoops.isEmpty();
	}

	public Set<IcfgLoop<INLOC>> getNestedLoops() {
		return mNestedLoops;
	}

	public Set<INLOC> getLoopbody() {
		return mLoopbody;
	}

	public INLOC getHead() {
		return mHead;
	}

	public boolean contains(final INLOC node) {
		return mLoopbody.contains(node);
	}

	public Set<ArrayList<IcfgEdge>> getPaths() {
		if (mPaths.isEmpty()) {
			loopPaths();
		}

		return mPaths;
	}

	@SuppressWarnings("unchecked")
	private void loopPaths() {
		final Deque<ArrayList<IcfgEdge>> queue = new ArrayDeque<>();
		for (final IcfgEdge edge : mHead.getOutgoingEdges()) {
			if (mLoopbody.contains(edge.getTarget())) {
				final ArrayList<IcfgEdge> a = new ArrayList<>();
				a.add(edge);
				queue.add(a);
			}
		}

		while (!queue.isEmpty()) {
			if (!mServices.getProgressMonitorService().continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "enumerating all paths in loop");
			}
			final ArrayList<IcfgEdge> path = queue.removeFirst();
			final INLOC destination = (INLOC) path.get(path.size() - 1).getTarget();
			if (destination.equals(mHead)) {
				mPaths.add(path);
				continue;
			}
			for (final IcfgEdge edge : destination.getOutgoingEdges()) {
				if (!mNestedNodes.contains(edge.getTarget()) && mLoopbody.contains(edge.getTarget())) {
					final ArrayList<IcfgEdge> addPath = new ArrayList<>(path);
					addPath.add(edge);
					queue.add(addPath);
				}
			}
		}
	}

}
