/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE LassoRanker Library.
 * 
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions;

import java.math.BigInteger;
import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;


/**
 * An affine-linear ranking function as generated by the affine template
 * 
 * @author Jan Leike
 */
public class LinearRankingFunction extends RankingFunction {
	private static final long serialVersionUID = 5376322220596462295L;
	
	private final AffineFunction mranking;
	
	public LinearRankingFunction(final AffineFunction ranking) {
		mranking = ranking;
	}
	
	@Override
	public String getName() {
		return "affine";
	}
	
	@Override
	public Set<IProgramVar> getVariables() {
		return Collections.unmodifiableSet(mranking.getVariables());
	}
	
	public AffineFunction getComponent() {
		return mranking;
	}
	
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("f");
		if (!mranking.isConstant()) {
			sb.append("(");
			boolean first = true;
			for (final IProgramVar var : mranking.getVariables()) {
				if (!first) {
					sb.append(", ");
				}
				sb.append(var.getGloballyUniqueId());
				first = false;
			}
			sb.append(")");
		}
		sb.append(" = ");
		sb.append(mranking);
		return sb.toString();
	}
	
	@Override
	public Term[] asLexTerm(final Script script) throws SMTLIBException {
		return new Term[] { mranking.asTerm(script) };
	}
	
	@Override
	public Ordinal evaluate(final Map<IProgramVar, Rational> assignment) {
		BigInteger i = mranking.evaluate(assignment).ceil().numerator();
		if (i.compareTo(BigInteger.ZERO) < 0) {
			i = BigInteger.ZERO;
		}
		return Ordinal.fromInteger(i);
	}
	
	@Override
	public Ordinal codomain() {
		return Ordinal.OMEGA;
	}
}
