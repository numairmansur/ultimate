/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.util.Collection;
import java.util.HashSet;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Memory efficient data structure that stores for a given equivalence relation
 * if pairs are in the relation, not in the relation, if the membership status
 * is unknown
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class ThreeValuedEquivalenceRelation<E> {

	private final UnionFind<E> mUnionFind;
	private final HashRelation<E, E> mDisequalities;
	private boolean mIsInconsistent;

	public ThreeValuedEquivalenceRelation() {
		mUnionFind = new UnionFind<>();
		mDisequalities = new HashRelation<>();
		mIsInconsistent = false;
	}

	public ThreeValuedEquivalenceRelation(final ThreeValuedEquivalenceRelation<E> tver) {
		this.mUnionFind = new UnionFind<>(tver.mUnionFind);
		this.mDisequalities = new HashRelation<>(tver.mDisequalities);
		this.mIsInconsistent = tver.mIsInconsistent;
		assert disequalitiesOnlyContainRepresentatives();
	}

	public ThreeValuedEquivalenceRelation(final UnionFind<E> newElemPartition,
			final HashRelation<E, E> newElemDisequalities) {
		mUnionFind = new UnionFind<>(newElemPartition);
		mDisequalities = new HashRelation<>(newElemDisequalities);
		mIsInconsistent = false;
		assert disequalitiesOnlyContainRepresentatives();
	}

	/**
	 * @return true iff elem was not contained in relation before (i.e. we made a change)
	 */
	public boolean addElement(final E elem) {
		if (mUnionFind.find(elem) == null) {
			mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem);
			return true;
		}
		return false;
	}

	public void removeElement(final E elem) {
		final E rep = mUnionFind.find(elem);
		mUnionFind.remove(elem);

		/*
		 * update mDistinctElements
		 */
		if (rep != elem) {
			// elem was not the representative of its equivalence class --> nothing to do for disequalities
			return;
		}
		// elem was the representative of its equivalence class --> we need to update mDistinctElements
		final Set<E> equivalenceClass = mUnionFind.getEquivalenceClassMembers(elem);
		if (equivalenceClass.isEmpty()) {
			// elem was the only element in its equivalence class --> just remove it from disequalities
			mDisequalities.removeDomainElement(elem);
			mDisequalities.removeRangeElement(elem);
		} else {
			assert rep == elem;
			// elem was the representative of its equivalence class, but not the only element
			// --> replace it by the new representative in mDistinctElements
			final E newRep = mUnionFind.find(equivalenceClass.iterator().next());
			mDisequalities.replaceDomainElement(elem, newRep);
			mDisequalities.replaceRangeElement(elem, newRep);
		}
	}

	/**
	 *
	 * @param elem1
	 * @param elem2
	 * @return true iff the method call changed the state of this ThreeValuedEquivalenceRelation
	 */
	public boolean reportEquality(final E elem1, final E elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		final E oldRep1 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem1);
		final E oldRep2 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem2);

		if (oldRep1 == oldRep2) {
			// the elements already are in the same equivalence class, do nothing
			return false;
		}

		if (getEqualityStatus(elem1, elem2) == EqualityStatus.NOT_EQUAL) {
			mIsInconsistent = true;
			return true;
		}

		mUnionFind.union(elem1, elem2);

		/*
		 * Because either oldRep1 or oldRep2 is no longer a representative now. By our convention, the element of the
		 * relation mDisequalities may only be representatives. Thus we may have to update mDisequalities accordingly.
		 */
		if (isRepresentative(oldRep1)) {
			// elem1 has kept its representative, elem2 has a new representative now
			assert mUnionFind.find(elem2) == oldRep1;

			mDisequalities.replaceDomainElement(oldRep2, oldRep1);
			mDisequalities.replaceRangeElement(oldRep2, oldRep1);
		} else {
			// elem2 has kept its representative, elem1 has a new representative now
			assert mUnionFind.find(elem1) == oldRep2;

			mDisequalities.replaceDomainElement(oldRep1, oldRep2);
			mDisequalities.replaceRangeElement(oldRep1, oldRep2);
		}
		assert disequalitiesOnlyContainRepresentatives();
		return true;
	}

	/**
	 *
	 * @param elem1
	 * @param elem2
	 * @return true iff the method call changed the state of this ThreeValuedEquivalenceRelation
	 */
	public boolean reportDisequality(final E elem1, final E elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		final E rep1 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem1);
		final E rep2 = mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem2);

		if (getEqualityStatus(rep1, rep2) == EqualityStatus.NOT_EQUAL) {
			return false;
		}

		if (rep1 == rep2) {
			mIsInconsistent = true;
			return true;
		}

		mDisequalities.addPair(rep1, rep2);
		assert disequalitiesOnlyContainRepresentatives();
		return true;
	}

	public E getRepresentativeAndAddElementIfNeeded(final E elem) {
		return mUnionFind.findAndConstructEquivalenceClassIfNeeded(elem);
	}

	public E getRepresentative(final E elem) {
		return mUnionFind.find(elem);
	}

	public boolean isRepresentative(final E elem) {
		return getRepresentative(elem) == elem;
	}

	/**
	 * @return true iff the equalities and disequalities that have been reported are inconsistent
	 */
	public boolean isInconsistent() {
		return mIsInconsistent;
	}

	public EqualityStatus getEqualityStatus(final E elem1, final E elem2) {
		if (mIsInconsistent) {
			throw new IllegalStateException();
		}

		final E elem1Rep = mUnionFind.find(elem1);
		if (elem1Rep == null) {
			throw new IllegalArgumentException("Unknown element: " + elem1);
		}
		final E elem2Rep = mUnionFind.find(elem2);
		if (elem2Rep == null) {
			throw new IllegalArgumentException("Unknown element: " + elem2);
		}

		if (elem1Rep.equals(elem2Rep)) {
			return EqualityStatus.EQUAL;
		} else if (mDisequalities.containsPair(elem1Rep, elem2Rep)
				|| mDisequalities.containsPair(elem2Rep, elem1Rep)) {
			return EqualityStatus.NOT_EQUAL;
		} else {
			return EqualityStatus.UNKNOWN;
		}
	}

	private boolean disequalitiesOnlyContainRepresentatives() {
		for (final Entry<E, E> en : mDisequalities.entrySet()) {
			if (!isRepresentative(en.getKey())) {
				return false;
			}
			if (!isRepresentative(en.getValue())) {
				return false;
			}
		}
		return true;
	}

	public Collection<E> getAllRepresentatives() {
		return mUnionFind.getAllRepresentatives();
	}

	public Collection<Set<E>> getAllEquivalenceClasses() {
		return mUnionFind.getAllEquivalenceClasses();
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Equivalences: ");
		sb.append(mUnionFind);
		sb.append("\n");

		sb.append("Non-Equivalences: ");
		sb.append(mDisequalities);
		sb.append("\n");

		sb.append("Containts contradiction: ");
		sb.append(mIsInconsistent);

		return sb.toString();
	}

	public Set<E> getAllElements() {
		return mUnionFind.getAllElements();
	}

	public Set<E> getRepresentativesUnequalTo(final E elem) {
		final Set<E> result = new HashSet<>();

		result.addAll(mDisequalities.getImage(elem));

		for (final E domEl : mDisequalities.getDomain()) {
			if (mDisequalities.getImage(domEl).contains(elem)) {
				result.add(domEl);
			}
		}

		return result;
	}

	public Set<E> getEquivalenceClass(final E elem) {
		return mUnionFind.getEquivalenceClassMembers(elem);
	}
}

