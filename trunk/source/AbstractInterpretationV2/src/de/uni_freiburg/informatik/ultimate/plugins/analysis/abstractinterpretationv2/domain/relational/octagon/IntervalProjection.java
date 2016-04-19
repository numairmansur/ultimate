/*
 * Copyright (C) 2015-2016 Claus Schaetzle (schaetzc@informatik.uni-freiburg.de)
 * Copyright (C) 2015-2016 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.relational.octagon;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.UnaryExpression;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.TypeUtil;

/**
 * Utilities to project octagons to intervals, calculated expression using intervals,
 * and assigning the resulting intervals to octagons.
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 */
public class IntervalProjection {

	/**
	 * Processes an assignment by projection to intervals.
	 * 
	 * @param var Variable to be assigned.
	 * @param rhs Expression without if-expressions, describing te new value of the variable.
	 * @param oldStates Octagon abstract states to be updated -- will be modified in-place.
	 * @return Updated states in the same list.
	 */
	public static List<OctDomainState> assignNumericVarWithoutIfs(final String var, final Expression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates);
		for (final OctDomainState state : oldStates) {
			final IntervalDomainValue interval = projectNumericExprWithoutIfs(rhs, state);
			state.assignNumericVarInterval(var, new OctInterval(interval));
		}
		return oldStates;
	}

	/**
	 * Processes an assignment by projection to intervals.
	 * 
	 * @param var Variable to be assigned.
	 * @param rhs Affine expression, describing te new value of the variable.
	 * @param oldStates Octagon abstract states to be updated -- will be modified in-place.
	 * @return Updated states in the same list.
	 */
	public static List<OctDomainState> assignNumericVarAffine(final String var, final AffineExpression rhs,
			List<OctDomainState> oldStates) {

		oldStates = OctPostOperator.removeBottomStates(oldStates);
		for (final OctDomainState state : oldStates) {
			final IntervalDomainValue interval = projectAffineExpr(rhs, state);
			state.assignNumericVarInterval(var, new OctInterval(interval));
		}
		return oldStates;
	}

	/**
	 * Project an octagon to intervals and calculate the abstract result (interval) of an expression.
	 * 
	 * @param expr Expression to be evaluated.
	 * @param state Octagon abstract state, describing the values variables can have.
	 * @return Abstract result (interval) of the expression
	 */
	public static IntervalDomainValue projectNumericExprWithoutIfs(final Expression expr, final OctDomainState state) {
		// TODO (?) cache interval projections of each variable

		if (expr instanceof IntegerLiteral) {
			final IntervalValue pointInterval = new IntervalValue(((IntegerLiteral) expr).getValue());
			return new IntervalDomainValue(pointInterval, pointInterval);
		
		} else if (expr instanceof RealLiteral) {
			final IntervalValue pointInterval = new IntervalValue(((IntegerLiteral) expr).getValue());
			return new IntervalDomainValue(pointInterval, pointInterval);
		
		} else if (expr instanceof IdentifierExpression) {
			final String var = ((IdentifierExpression) expr).getIdentifier();
			final OctInterval octInterval = state.projectToInterval(var);
			return octInterval.toIvlInterval();

		} else if (expr instanceof UnaryExpression) {
			final UnaryExpression unExpr = (UnaryExpression) expr;
			switch (unExpr.getOperator()) {
			case ARITHNEGATIVE:
				return projectNumericExprWithoutIfs(unExpr.getExpr(), state).negate();
			default:
				// see end of this method
			}
			
		} else if (expr instanceof BinaryExpression) {
			final BinaryExpression binExpr = (BinaryExpression) expr;
			final IntervalDomainValue left = projectNumericExprWithoutIfs(binExpr.getLeft(), state);
			final IntervalDomainValue right = projectNumericExprWithoutIfs(binExpr.getRight(), state);
			switch (binExpr.getOperator()) {
			case ARITHPLUS:
				return left.add(right);
			case ARITHMINUS:
				return left.subtract(right);
			case ARITHMUL:
				return left.multiply(right);
			case ARITHDIV:
				if (TypeUtil.isNumericInt(binExpr.getType())) {
					return left.integerDivide(right);
				} else {
					return left.divide(right);
				}
			case ARITHMOD:
				return left.modulo(right, TypeUtil.isNumericInt(binExpr.getType()));
			default:
				// see end of this method
			}

		}
		return new IntervalDomainValue(); // \top = safe over-approximation
	}
	
	/**
	 * Project an octagon to intervals and calculate the abstract result (interval) of an affine expression.
	 * 
	 * @param expr Affine expression to be evaluated.
	 * @param state Octagon abstract state, describing the values variables can have.
	 * @return Abstract result (interval) of the expression
	 */
	public static IntervalDomainValue projectAffineExpr(final AffineExpression expr, final OctDomainState state) {
		IntervalDomainValue resultInterval = new IntervalDomainValue(0, 0);
		for (final Map.Entry<String, BigDecimal> summand : expr.getCoefficients().entrySet()) {
			final IntervalDomainValue varValue = state.projectToInterval(summand.getKey()).toIvlInterval();
			final IntervalValue factor = new IntervalValue(summand.getValue());
			resultInterval = resultInterval.add(varValue.multiply(new IntervalDomainValue(factor, factor)));
		}
		final IntervalValue constant = new IntervalValue(expr.getConstant());
		resultInterval = resultInterval.add(new IntervalDomainValue(constant, constant));
		return resultInterval;
	}

}
