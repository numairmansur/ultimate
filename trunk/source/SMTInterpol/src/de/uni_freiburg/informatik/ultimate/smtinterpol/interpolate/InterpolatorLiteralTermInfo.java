/*
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * This class is used to gather the information from a literal term which is relevant for the interpolator.
 *
 * @author Tanja Schindler
 */
public class InterpolatorLiteralTermInfo {
	/**
	 * The underlying atom of this literal
	 */
	private Term mAtom;
	private boolean mIsNegated;

	/**
	 * The type of this literal, true if it represents a CC equality
	 */
	private boolean mIsCCEquality;

	/**
	 * The type of this literal, true if it represents a LA equality
	 */
	private boolean mIsLAEquality;

	/**
	 * The type of this literal, true if it represents a bound constraint
	 */
	private boolean mIsBoundConstraint;

	/**
	 * Is the bound constraint strict?
	 */
	private boolean mIsStrict;

	/**
	 * If this literal is a CC equality, then this contains the ApplicationTerm (= lhs rhs)
	 */
	private ApplicationTerm mCCEquality;

	/**
	 * The linear variable of this LA literal
	 */
	private InterpolatorAffineTerm mLinVar;

	/**
	 * The bound of this bound constraint literal
	 */
	private Rational mBound;

	/**
	 * Epsilon is 1 for integer constraints, eps for rational constraints
	 */
	private InfinitNumber mEpsilon;

	private boolean mIsInt;

	public InterpolatorLiteralTermInfo() {
		mAtom = null;
		mIsNegated = false;
		mIsCCEquality = false;
		mIsLAEquality = false;
		mIsBoundConstraint = false;
		mLinVar = null;
		mBound = null;
		mEpsilon = null;
		mIsInt = false;
	}

	/**
	 * Collect information about this literal which is needed during interpolation
	 */
	public void computeLiteralTermInfo(final Term term) {
		Term atom = term;
		String annot = null;
		// Get the underlying atom
		if (atom instanceof ApplicationTerm && ((ApplicationTerm) atom).getFunction().getName().equals("not")) {
			mIsNegated = true;
			atom = ((ApplicationTerm) atom).getParameters()[0];
		}
		// Annotations can be inside negations
		if (atom instanceof AnnotatedTerm) {
			assert ((AnnotatedTerm) atom).getAnnotations().length == 1;
			annot = ((AnnotatedTerm) atom).getAnnotations()[0].getKey();
		}
		mAtom = atom;
		mIsCCEquality = annot == ":quotedCC";
		Term unquoted = mAtom instanceof AnnotatedTerm ? ((AnnotatedTerm) atom).getSubterm() : mAtom;
		mIsBoundConstraint = isBoundConstraint(unquoted);
		mIsLAEquality = annot == ":quotedLA" && !mIsBoundConstraint;

		if (mIsLAEquality || mIsBoundConstraint) {
			final InterpolatorAffineTerm lv = computeLinVarAndBound(unquoted);
			assert lv.getConstant().mEps == 0;
			if (mIsBoundConstraint) {
				mIsStrict = isStrict(unquoted);
			}
			mBound = lv.getConstant().negate().mA;
			mLinVar = lv.add(mBound);
			mIsInt = mLinVar.isInt();
			mEpsilon = computeEpsilon(unquoted);
		} else if (mIsCCEquality) {
			mCCEquality = (ApplicationTerm) ((AnnotatedTerm) atom).getSubterm();
		}
	}

	/**
	 * Get the underlying atomic term for an annotated or negated term
	 */
	private Term computeAtom(final Term term) {
		Term inner = term;
		if (isNegated(inner)) {
			inner = ((ApplicationTerm) inner).getParameters()[0];
		}
		if (inner instanceof AnnotatedTerm) {
			inner = ((AnnotatedTerm) inner).getSubterm();
		}
		return inner;
	}

	/**
	 * Check if this atom is a LA equality. Note that some CC equalities look like LA equalities, but in those cases,
	 * they are treated the same way.
	 */
	boolean isLAEquality(final Term atom) {
		if (atom instanceof ApplicationTerm) {
			if (((ApplicationTerm) atom).getFunction().getName().equals("=")) {
				final Term secondParam = ((ApplicationTerm) atom).getParameters()[1];
				if (secondParam instanceof ConstantTerm) {
					return SMTAffineTerm.create(secondParam).getConstant().equals(Rational.ZERO);
				}
			}
		}
		return false;
	}

	/**
	 * Check if this atom is a bound constraint
	 */
	private boolean isBoundConstraint(final Term atom) {
		if (!(atom instanceof ApplicationTerm)) {
			return false;
		}
		final String func = ((ApplicationTerm) atom).getFunction().getName();
		return func.equals("<") || func.equals("<=");
	}

	/**
	 * Check if a bound constraint is strict
	 */
	private boolean isStrict(final Term atom) {
		assert mIsBoundConstraint;
		final String func = ((ApplicationTerm) atom).getFunction().getName();
		return func.equals("<");
	}

	/**
	 * For an LA equality or bound constraint, get the linear variable.
	 */
	private InterpolatorAffineTerm computeLinVarAndBound(final Term laAtom) {
		final Term[] params = ((ApplicationTerm) laAtom).getParameters();
		final Term varTerm = params[0];

		assert params[1] instanceof ConstantTerm;
		assert SMTAffineTerm.create(params[1]).getConstant().equals(Rational.ZERO);
		return Interpolator.termToAffine(varTerm);
	}

	/**
	 * Get the epsilon for this bound constraint. This is 1 for integer constraints, and eps for rational constraints.
	 */
	private InfinitNumber computeEpsilon(final Term term) {
		return mLinVar.isInt() ? InfinitNumber.ONE : InfinitNumber.EPSILON;
	}

	/**
	 * Check if a term is negated
	 */
	private boolean isNegated(final Term term) {
		if (term instanceof ApplicationTerm) {
			return ((ApplicationTerm) term).getFunction().getName().equals("not");
		} else {
			return false;
		}
	}

	public Term getAtom() {
		return mAtom;
	}

	public boolean isNegated() {
		return mIsNegated;
	}

	public boolean isCCEquality() {
		return mIsCCEquality;
	}

	public boolean isLAEquality() {
		return mIsLAEquality;
	}

	public boolean isBoundConstraint() {
		return mIsBoundConstraint;
	}

	public boolean isStrict() {
		return mIsStrict;
	}

	public ApplicationTerm getEquality() {
		return mCCEquality;
	}

	public InterpolatorAffineTerm getLinVar() {
		return mLinVar;
	}

	public Rational getBound() {
		return mBound;
	}

	public InfinitNumber getEpsilon() {
		return mEpsilon;
	}

	public boolean isInt() {
		return mIsInt;
	}
}
