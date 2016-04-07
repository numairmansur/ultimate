/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.boogie.type.ArrayType;
import de.uni_freiburg.informatik.ultimate.boogie.type.PrimitiveType;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.IBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.BooleanValue.Value;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;

/**
 * Implementation of an abstract state of the {@link IntervalDomain}.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class IntervalDomainState implements IAbstractState<IntervalDomainState, CodeBlock, IBoogieVar> {

	private static int sId;
	private final int mId;

	private final Map<String, IBoogieVar> mVariablesMap;
	private final Map<String, IntervalDomainValue> mValuesMap;
	private final Map<String, BooleanValue> mBooleanValuesMap;

	private final Logger mLogger;

	protected enum VariableType {
		VARIABLE, BOOLEAN, ARRAY
	}

	/**
	 * Test constructor of an {@link IntervalDomainState}.
	 * 
	 * <p>
	 * <b>Note:</b> This constructor is for internal (i.e. testing) use only. Do not use except you know what you are
	 * doing, as it could break the abstract interpretation framework if used in conjunction with other abstract
	 * interpretation classes.
	 * </p>
	 */
	protected IntervalDomainState() {
		this(null);
	}

	/**
	 * Default constructor of an {@link IntervalDomainState}.
	 * 
	 * @param logger
	 *            The current logger object in the current context.
	 */
	protected IntervalDomainState(final Logger logger) {
		mVariablesMap = new HashMap<String, IBoogieVar>();
		mValuesMap = new HashMap<String, IntervalDomainValue>();
		mBooleanValuesMap = new HashMap<String, BooleanValue>();
		sId++;
		mId = sId;
		mLogger = logger;
	}

	/**
	 * Creates a new instance of {@link IntervalDomainState} with given logger, variables map, values map and boolean
	 * values map.
	 * 
	 * @param logger
	 *            The current logger object in the current context.
	 * @param variablesMap
	 *            The map with all variable identifiers and their types.
	 * @param valuesMap
	 *            The values of all variables.
	 * @param booleanValuesMap
	 *            The values of all boolean variables.
	 */
	protected IntervalDomainState(final Logger logger, final Map<String, IBoogieVar> variablesMap,
			final Map<String, IntervalDomainValue> valuesMap, final Map<String, BooleanValue> booleanValuesMap) {
		mVariablesMap = new HashMap<String, IBoogieVar>(variablesMap);
		mValuesMap = new HashMap<String, IntervalDomainValue>(valuesMap);
		mBooleanValuesMap = new HashMap<String, BooleanValue>(booleanValuesMap);
		sId++;
		mId = sId;
		mLogger = logger;
	}

	@Override
	public Map<String, IBoogieVar> getVariables() {
		return Collections.unmodifiableMap(mVariablesMap);
	}

	/**
	 * Returns the {@link IntervalDomainValue} of the given variable. If the variable does not have a value, an
	 * {@link UnsupportedOperationException} is thrown.
	 * 
	 * @param variableName
	 *            The name of the variable to get the {@link IntervalDomainValue} for.
	 * @return A new {@link IntervalDomainValue} containing the {@link IntervalDomainValue} of the given variable.
	 */
	protected IntervalDomainValue getValue(final String variableName) {
		if (!mValuesMap.containsKey(variableName)) {
			throw new UnsupportedOperationException("There is no value of variable " + variableName + ".");
		}

		return mValuesMap.get(variableName).copy();
	}

	/**
	 * Returns the {@link BooleanValue} of the given variable. If the variable is not a boolean variable, an
	 * {@link UnsupportedOperationException} is thrown.
	 * 
	 * @param booleanVariableName
	 *            The name of the boolean variable to get the {@link BooleanValue} for.
	 * @return A new {@link BooleanValue} containing the {@link BooleanValue} of the given variable.
	 */
	protected BooleanValue getBooleanValue(final String booleanVariableName) {
		if (!mBooleanValuesMap.containsKey(booleanVariableName)) {
			throw new UnsupportedOperationException(
					"There is no boolean variable with name " + booleanVariableName + ".");
		}

		return new BooleanValue(mBooleanValuesMap.get(booleanVariableName));
	}

	/**
	 * Sets the value of a variable with given name to the given value.
	 * 
	 * @param name
	 *            The name of the variable.
	 * @param value
	 *            The value to set.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> where the value of the given
	 *         variable has been set to the given value.
	 */
	protected IntervalDomainState setValue(final String name, final IntervalDomainValue value) {
		final IntervalDomainState returnState = copy();
		setValueInternally(returnState, name, value);
		return returnState;
	}

	/**
	 * Sets the values of multiple given variables at once.
	 * 
	 * <p>
	 * <b>Note:</b> that the values and variables arrays must have the same size.
	 * </p>
	 * 
	 * @param vars
	 *            The variables to set the values for.
	 * @param values
	 *            The array of values to set.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> where the values of the given
	 *         variables have been set to the given values.
	 */
	protected IntervalDomainState setValues(final String[] vars, final IntervalDomainValue[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(vars, values, new String[0], new BooleanValue.Value[0], new String[0],
				new IntervalDomainValue[0]);
	}

	/**
	 * Sets the value of a boolean variable.
	 * 
	 * @param name
	 *            The boolean variable to set the value for.
	 * @param value
	 *            The value to set.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> where the value of the given
	 *         variable has been set to the given value.
	 */
	protected IntervalDomainState setBooleanValue(final String name, final BooleanValue.Value value) {
		assert name != null;
		assert value != null;

		final IntervalDomainState returnState = copy();
		setValueInternally(returnState, name, new BooleanValue(value));
		return returnState;
	}

	/**
	 * Sets the value of a boolean variable.
	 * 
	 * @param name
	 *            The boolean variable to set the value for.
	 * @param value
	 *            The value to set.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> where the value of the given
	 *         variable has been set to the given value.
	 */
	protected IntervalDomainState setBooleanValue(final String bool, final boolean value) {
		return setBooleanValue(bool, new BooleanValue(value));
	}

	/**
	 * Sets the value of a boolean variable.
	 * 
	 * @param name
	 *            The boolean variable to set the value for.
	 * @param value
	 *            The value to set.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> where the value of the given
	 *         variable has been set to the given value.
	 */
	protected IntervalDomainState setBooleanValue(final String bool, final BooleanValue value) {
		assert bool != null;
		assert value != null;

		return setBooleanValue(bool, value.getValue());
	}

	/**
	 * Sets the values of multiple given boolean variables at once.
	 * 
	 * <p>
	 * <b>Note:</b> that the values and variables arrays must have the same size.
	 * </p>
	 * 
	 * @param vars
	 *            The variables to set the values for.
	 * @param values
	 *            The array of values to set.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> where the values of the given
	 *         variables have been set to the given values.
	 */
	protected IntervalDomainState setBooleanValues(final String[] vars, final BooleanValue.Value[] values) {
		assert vars != null;
		assert values != null;
		assert vars.length == values.length;

		return setMixedValues(new String[0], new IntervalDomainValue[0], vars, values, new String[0],
				new IntervalDomainValue[0]);
	}

	/**
	 * Sets the value of an array variable to a given value.
	 * 
	 * TODO: Implement proper handling of arrays.
	 * 
	 * @param array
	 *            The array name.
	 * @param value
	 *            The value to set the array variable to.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> but with updated value for the
	 *         given array variable.
	 */
	protected IntervalDomainState setArrayValue(final String array, final IntervalDomainValue value) {
		assert array != null;
		assert value != null;
		final IntervalDomainState returnState = copy();
		setValueInternally(returnState, array, value);
		return returnState;
	}

	protected IntervalDomainState setArrayValues(final String[] arrays, final IntervalDomainValue[] values) {
		assert arrays != null;
		assert values != null;
		assert arrays.length == values.length;

		return setMixedValues(new String[0], new IntervalDomainValue[0], new String[0], new BooleanValue.Value[0],
				arrays, values);
	}

	/**
	 * Sets multiple values of multiple variable types at the same time.
	 * 
	 * TODO: Arrays are currently handled as normal variables.
	 * 
	 * @param vars
	 *            A list of variable identifiers whose values are to be changed.
	 * @param values
	 *            A list of values which corresponds to the list of variable identifiers.
	 * @param booleanVars
	 *            A list of boolean variable identifiers whose values are to be changed.
	 * @param booleanValues
	 *            A list of values which corresponds to the list of boolean variable identifiers.
	 * @return A new {@link IntervalDomainState} which is the copy of <code>this</code> but with the updated values.
	 */
	protected IntervalDomainState setMixedValues(final String[] vars, final IntervalDomainValue[] values,
			final String[] booleanVars, final BooleanValue.Value[] booleanValues, final String[] arrays,
			final IntervalDomainValue[] arrayValues) {
		assert vars != null;
		assert values != null;
		assert booleanVars != null;
		assert booleanValues != null;
		assert vars.length == values.length;
		assert booleanVars.length == booleanValues.length;

		final IntervalDomainState returnState = copy();
		for (int i = 0; i < vars.length; i++) {
			setValueInternally(returnState, vars[i], values[i]);
		}

		for (int i = 0; i < booleanVars.length; i++) {
			setValueInternally(returnState, booleanVars[i], new BooleanValue(booleanValues[i]));
		}

		for (int i = 0; i < arrays.length; i++) {
			setValueInternally(returnState, arrays[i], arrayValues[i]);
		}

		return returnState;
	}

	/**
	 * Internally sets the value of a variable of a given {@link IntervalDomainState}.
	 * 
	 * @param state
	 *            The state to set the variable value for.
	 * @param name
	 *            The name of the variable to change the value for.
	 * @param value
	 *            The value to set.
	 */
	private static void setValueInternally(final IntervalDomainState state, final String name,
			final IntervalDomainValue value) {
		assert state != null;
		assert name != null;
		assert value != null;
		assert state.mVariablesMap.get(name) != null : "Variable unknown";
		assert state.mValuesMap.get(name) != null : "Variable not in values map";
		state.mValuesMap.put(name, value);
	}

	/**
	 * Internally sets the value of a boolean variable of a given {@link IntervalDomainState}.
	 * 
	 * @param state
	 *            The state to set the variable value for.
	 * @param name
	 *            The name of the variable to change the value for.
	 * @param value
	 *            The value to set.
	 */
	private static void setValueInternally(final IntervalDomainState state, final String name,
			final BooleanValue value) {
		assert state != null;
		assert name != null;
		assert state.mVariablesMap.get(name) != null : "Variable unknown";
		assert state.mBooleanValuesMap.get(name) != null : "Boolean variable not in boolean values map";
		state.mBooleanValuesMap.put(name, value);
	}

	@Override
	public IntervalDomainState addVariable(final String name, final IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final IntervalDomainState returnState = copy();
		addVariableInternally(returnState, name, variable);
		return returnState;
	}

	/**
	 * Returns the type of a given variable.
	 * 
	 * @param var
	 *            The variable name to obtain the type for.
	 * @return The {@link VariableType} of the variable.
	 */
	protected VariableType getVariableType(final String var) {
		if (!containsVariable(var)) {
			throw new UnsupportedOperationException("The variable " + var + " does not exist in the current state.");
		}

		if (mBooleanValuesMap.containsKey(var)) {
			return VariableType.BOOLEAN;
		}

		if (mValuesMap.containsKey(var)) {
			return VariableType.VARIABLE;
		}

		// TODO: Implement proper handling of arrays.
		throw new UnsupportedOperationException(
				"The variable " + var + " exists but was not found in the variable sets.");
	}

	/**
	 * Adds the given variable with given name and type to the appropriate data structures of <code>this</code>.
	 * 
	 * @param name
	 *            The variable to add.
	 * @param variable
	 *            The type of the variable.
	 */
	private static void addVariableInternally(final IntervalDomainState state, final String name,
			final IBoogieVar variable) {
		assert state != null;
		assert name != null;
		assert variable != null;

		final IBoogieVar old = state.mVariablesMap.put(name, variable);

		if (old != null) {
			throw new UnsupportedOperationException(
					"Variable names must be disjoint. Variable " + name + " is already present.");
		}

		if (variable.getIType() instanceof PrimitiveType) {
			final PrimitiveType primitiveType = (PrimitiveType) variable.getIType();

			if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
				state.mBooleanValuesMap.put(name, new BooleanValue(true));
			} else {
				state.mValuesMap.put(name, new IntervalDomainValue());
			}
		} else if (variable.getIType() instanceof ArrayType) {
			// TODO:
			// We treat Arrays as normal variables for the time being.
			state.mValuesMap.put(name, new IntervalDomainValue());
		} else {
			state.mLogger.warn("The IBoogieVar type " + variable.getIType().getClass().toString() + " of variable "
					+ name + " is not implemented. Assuming top.");
			state.mValuesMap.put(name, new IntervalDomainValue());
		}
	}

	@Override
	public IntervalDomainState removeVariable(final String name, final IBoogieVar variable) {
		assert name != null;
		assert variable != null;

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		newVarMap.remove(name);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		newValMap.remove(name);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);
		newBooleanValMap.remove(name);

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap);
	}

	@Override
	public IntervalDomainState addVariables(final Map<String, IBoogieVar> variables) {
		assert variables != null;
		if (variables.isEmpty()) {
			// nothing to add, nothing changes
			return this;
		}

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);

		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			final String id = entry.getKey();
			final IBoogieVar var = entry.getValue();
			final IBoogieVar old = newVarMap.put(id, var);
			if (old != null) {
				throw new UnsupportedOperationException(
						"Variable names must be disjoint. The variable " + id + " is already present.");
			}
			if (var.getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					newBooleanValMap.put(id, new BooleanValue());
				} else {
					newValMap.put(id, new IntervalDomainValue());
				}

			} else if (var.getIType() instanceof ArrayType) {
				// TODO:
				// We treat Arrays as normal variables for the time being.
				newValMap.put(id, new IntervalDomainValue());
			} else {
				mLogger.warn("The IBoogieVar type " + var.getIType().getClass().toString() + " of variable " + id
						+ " is not implemented. Assuming top.");
				newValMap.put(id, new IntervalDomainValue());
			}
		}

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap);
	}

	@Override
	public IntervalDomainState removeVariables(final Map<String, IBoogieVar> variables) {
		assert variables != null;
		assert !variables.isEmpty();

		final Map<String, IBoogieVar> newVarMap = new HashMap<String, IBoogieVar>(mVariablesMap);
		final Map<String, IntervalDomainValue> newValMap = new HashMap<String, IntervalDomainValue>(mValuesMap);
		final Map<String, BooleanValue> newBooleanValMap = new HashMap<String, BooleanValue>(mBooleanValuesMap);
		for (final Entry<String, IBoogieVar> entry : variables.entrySet()) {
			newVarMap.remove(entry.getKey());
			newValMap.remove(entry.getKey());
			newBooleanValMap.remove(entry.getKey());
		}

		return new IntervalDomainState(mLogger, newVarMap, newValMap, newBooleanValMap);
	}

	@Override
	public boolean containsVariable(final String name) {
		final IBoogieVar var = mVariablesMap.get(name);
		return var != null;
	}

	@Override
	public boolean isEmpty() {
		return mVariablesMap.isEmpty();
	}

	@Override
	public boolean isBottom() {
		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			if (entry.getValue().isBottom()) {
				return true;
			}
		}

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			if (entry.getValue().getValue() == Value.BOTTOM) {
				return true;
			}
		}

		return false;
	}

	/**
	 * Build a string of the form "var1 : type1 = [lb1 ; ub1]; var2 : type2 = [lb2 ; ub2]; ...", where lb is a lower
	 * bound and ub is an upper bound. lb can also be -\infty or \infty. Note that a value may also be "{}" if the
	 * corresponding interval is &bot;.
	 * 
	 * @return A string of all variables with their values.
	 */
	@Override
	public String toLogString() {
		final StringBuilder stringBuilder = new StringBuilder();
		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {

			stringBuilder.append(entry.getKey()).append(" = ");

			final IntervalDomainValue val = mValuesMap.get(entry.getKey());

			if (val != null) {
				stringBuilder.append(mValuesMap.get(entry.getKey()).toString());
			} else {
				stringBuilder.append(mBooleanValuesMap.get(entry.getKey()).toString());
			}

			stringBuilder.append("; ");
		}
		return stringBuilder.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}

	@Override
	public boolean isEqualTo(final IntervalDomainState other) {
		if (!hasSameVariables(other)) {
			return false;
		}

		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			final IntervalDomainValue otherValue = other.mValuesMap.get(entry.getKey());
			if (!mValuesMap.get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			final BooleanValue otherValue = other.mBooleanValuesMap.get(entry.getKey());
			if (!mBooleanValuesMap.get(entry.getKey()).isEqualTo(otherValue)) {
				return false;
			}
		}

		return true;
	}

	public IntervalDomainState copy() {
		return new IntervalDomainState(mLogger, mVariablesMap, mValuesMap, mBooleanValuesMap);
	}

	@Override
	public int hashCode() {
		return mId;
	}

	@Override
	public boolean equals(final Object obj) {
		if (obj == null) {
			return false;
		}

		if (!(obj instanceof IntervalDomainState)) {
			return false;
		}

		return obj == this;
	}

	/**
	 * Returns <code>true</code> if and only if {@link this} has the same variables as other.
	 * 
	 * @param other
	 *            The other state to check for same variables.
	 * @return <code>true</code> iff the variables are the same, <code>false</code> otherwise.
	 */
	protected boolean hasSameVariables(final IntervalDomainState other) {
		if (other == null) {
			return false;
		}

		if (!getClass().isInstance(other)) {
			return false;
		}

		if (other.mVariablesMap.size() != mVariablesMap.size()) {
			return false;
		}

		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
			final IBoogieVar otherType = other.mVariablesMap.get(entry.getKey());
			if (!entry.getValue().equals(otherType)) {
				return false;
			}
		}

		return true;
	}

	/**
	 * Intersects <code>this</code> with another {@link IntervalDomainState} by piecewise intersecting all occurring
	 * variable intervals.
	 * 
	 * @param other
	 *            The other state to intersect with.
	 * @return A new {@link IAbstractState} that corresponds to the intersection of
	 */
	protected IntervalDomainState intersect(final IntervalDomainState other) {
		assert other != null;
		assert hasSameVariables(other);

		final IntervalDomainState returnState = copy();

		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			setValueInternally(returnState, entry.getKey(),
					entry.getValue().intersect(other.mValuesMap.get(entry.getKey())));
		}

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			setValueInternally(returnState, entry.getKey(),
					new BooleanValue(entry.getValue().intersect(other.mBooleanValuesMap.get(entry.getKey()))));
		}

		return returnState;
	}

	@Override
	public Term getTerm(final Script script, final Boogie2SMT bpl2smt) {
		if (isBottom()) {
			return script.term("false");
		}

		final List<Term> acc = new ArrayList<Term>(mValuesMap.size() + mBooleanValuesMap.size());

		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			final IBoogieVar boogievar = mVariablesMap.get(entry.getKey());
			final Term var = getTermVar(boogievar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			if (!sort.isNumericSort()) {
				// TODO: Handle boolean variables (easy)
				// TODO: what about arrays (hard -- but perhaps not necessary, c.f. Matthias' integer programs)
				continue;
			}
			acc.add(entry.getValue().getTerm(script, sort, var));
		}
		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			final IBoogieVar boogievar = mVariablesMap.get(entry.getKey());
			final Term var = getTermVar(boogievar);
			assert var != null : "Error during TermVar creation";
			final Sort sort = var.getSort().getRealSort();
			acc.add(entry.getValue().getTerm(script, sort, var));
		}

		return Util.and(script, acc.toArray(new Term[acc.size()]));
	}

	/**
	 * Generates an SMT {@link Term} for a given variable.
	 * 
	 * @param var
	 *            The variable to generate the SMT Term for.
	 * @return The SMT Term.
	 */
	private Term getTermVar(final IBoogieVar var) {
		assert var != null : "Cannot get TermVariable from null";
		if (var instanceof BoogieVar) {
			final TermVariable termvar = ((BoogieVar) var).getTermVariable();
			assert termvar != null : "There seems to be no termvar for this BoogieVar";
			return termvar;
		} else if (var instanceof BoogieConst) {
			final ApplicationTerm termvar = ((BoogieConst) var).getDefaultConstant();
			assert termvar != null : "There seems to be no termvar for this BoogieConst";
			return termvar;
		}
		return null;
	}

	/**
	 * @return A new {@link IntervalDomainState} containing the same set of variables but with values set to &bot;.
	 */
	protected IntervalDomainState bottomState() {
		final IntervalDomainState ret = copy();
		for (final Entry<String, IntervalDomainValue> entry : ret.mValuesMap.entrySet()) {
			entry.setValue(new IntervalDomainValue(true));
		}

		for (final Entry<String, BooleanValue> entry : ret.mBooleanValuesMap.entrySet()) {
			entry.setValue(new BooleanValue(Value.BOTTOM));
		}

		return ret;
	}

	/**
	 * Sets all variables, booleans, or arrays to &top;, that are specified in the corresponding parameters.
	 * 
	 * @param vars
	 *            The names of the variables to set to &top;.
	 * @param bools
	 *            The names of the booleans to set to &top;.
	 * @param arrays
	 *            The names of the arrays to set to &top;.
	 * @return A new {@link IntervalDomainState} that is the copy of <code>this</code>, where all occurring variables,
	 *         booleans, and arrays given in the parameters are set to &top;.
	 */
	protected IntervalDomainState setVarsToTop(final List<String> vars, final List<String> bools,
			final List<String> arrays) {
		final IntervalDomainState returnState = copy();

		for (final String var : vars) {
			setValueInternally(returnState, var, new IntervalDomainValue());
		}
		for (final String bool : bools) {
			setValueInternally(returnState, bool, new BooleanValue());
		}
		for (final String array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, new IntervalDomainValue());
		}

		return returnState;
	}

	/**
	 * Sets all given variables, booleans, or arrays to &bot;.
	 * 
	 * @param vars
	 *            The names of the variables to set to &bot;.
	 * @param bools
	 *            The names of the booleans to set to &bot;.
	 * @param arrays
	 *            The names of the arrays to set to &bot;.
	 * @return A new {@link IntervalDomainState} that is the copy of <code>this</code>, where all occurring variables,
	 *         booleans, and arrays given as parameters are set to &bot;.
	 */
	protected IntervalDomainState setVarsToBottom(final List<String> vars, final List<String> bools,
			final List<String> arrays) {
		final IntervalDomainState returnState = copy();

		for (final String var : vars) {
			setValueInternally(returnState, var, new IntervalDomainValue(true));
		}
		for (final String bool : bools) {
			setValueInternally(returnState, bool, new BooleanValue(Value.BOTTOM));
		}
		for (final String array : arrays) {
			// TODO: Implement proper handling of arrays.
			setValueInternally(returnState, array, new IntervalDomainValue(true));
		}

		return returnState;
	}

	@Override
	public IBoogieVar getVariableDeclarationType(final String name) {
		assert name != null;
		final IBoogieVar var = mVariablesMap.get(name);
		assert var != null : "Unknown variable";
		return var;
	}

	@Override
	public IntervalDomainState patch(final IntervalDomainState dominator) {
		assert dominator != null;

		final IntervalDomainState returnState = copy();

		for (final Entry<String, IBoogieVar> var : dominator.mVariablesMap.entrySet()) {
			if (!returnState.containsVariable(var.getKey())) {
				addVariableInternally(returnState, var.getKey(), var.getValue());
			}

			if (var.getValue().getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) var.getValue().getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					setValueInternally(returnState, var.getKey(), dominator.mBooleanValuesMap.get(var.getKey()));
				} else if (var.getValue().getIType() instanceof ArrayType) {
					// TODO:
					// We treat Arrays as normal variables for the time being.
					setValueInternally(returnState, var.getKey(), dominator.mValuesMap.get(var.getKey()));
				} else {
					setValueInternally(returnState, var.getKey(), dominator.mValuesMap.get(var.getKey()));
				}
			}

		}

		return returnState;
	}

	/**
	 * Merges <code>this</code> with another {@link IntervalDomainState}. All variables that occur in <code>this</code>
	 * must also occur in the other state.
	 * 
	 * @param other
	 *            The other state to merge with.
	 * @return A new {@link IntervalDomainState} which is the result of the merger of <code>this</code> and
	 *         <code>other</code>.
	 */
	protected IntervalDomainState merge(final IntervalDomainState other) {
		assert other != null;

		if (!hasSameVariables(other)) {
			throw new UnsupportedOperationException(
					"Cannot merge the two states as their sets of variables in the states are disjoint.");
		}

		final IntervalDomainState returnState = copy();

		for (final Entry<String, IBoogieVar> entry : mVariablesMap.entrySet()) {
			final String var = entry.getKey();

			if (entry.getValue().getIType() instanceof PrimitiveType) {
				final PrimitiveType primitiveType = (PrimitiveType) entry.getValue().getIType();

				if (primitiveType.getTypeCode() == PrimitiveType.BOOL) {
					setValueInternally(returnState, var,
							mBooleanValuesMap.get(var).merge(other.mBooleanValuesMap.get(var)));
				} else {
					setValueInternally(returnState, var, mValuesMap.get(var).merge(other.mValuesMap.get(var)));
				}
			} else if (entry.getValue().getIType() instanceof ArrayType) {
				// TODO:
				// Implement better handling of arrays.
				setValueInternally(returnState, var, mValuesMap.get(var).merge(other.mValuesMap.get(var)));
			} else {
				setValueInternally(returnState, var, mValuesMap.get(var).merge(other.mValuesMap.get(var)));
			}
		}
		return returnState;
	}

	@Override
	public SubsetResult isSubsetOf(final IntervalDomainState other) {
		assert hasSameVariables(other);
		for (final Entry<String, IntervalDomainValue> entry : mValuesMap.entrySet()) {
			final IntervalDomainValue thisValue = entry.getValue();
			final IntervalDomainValue otherValue = other.mValuesMap.get(entry.getKey());
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}

		for (final Entry<String, BooleanValue> entry : mBooleanValuesMap.entrySet()) {
			final BooleanValue thisValue = entry.getValue();
			final BooleanValue otherValue = other.mBooleanValuesMap.get(entry.getKey());
			if (!thisValue.isContainedIn(otherValue)) {
				return SubsetResult.NONE;
			}
		}
		return SubsetResult.NON_STRICT;
	}
}
