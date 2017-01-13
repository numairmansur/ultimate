/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.empty;

import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.abstractinterpretation.model.IAbstractStateBinaryOperator;

/**
 * This domain does exactly nothing. It can be used to test various aspects of the framework.
 *
 * @author dietsch@informatik.uni-freiburg.de
 *
 * @param <ACTION>
 *            Any action type.
 * @param <VARDECL>
 *            Any variable declaration.
 */
public class EmptyDomain<ACTION, VARDECL> implements IAbstractDomain<EmptyDomainState<VARDECL>, ACTION, VARDECL> {
	
	private final Class<VARDECL> mVariablesType;

	public EmptyDomain(final Class<VARDECL> variablesType) {
		mVariablesType = variablesType;
	}
	
	@Override
	public EmptyDomainState<VARDECL> createFreshState() {
		return new EmptyDomainState<>(mVariablesType);
	}
	
	@Override
	public EmptyDomainState<VARDECL> createTopState() {
		return new EmptyDomainState<>(false, mVariablesType);
	}

	@Override
	public EmptyDomainState<VARDECL> createBottomState() {
		return new EmptyDomainState<>(true, mVariablesType);
	}
	
	@Override
	public IAbstractStateBinaryOperator<EmptyDomainState<VARDECL>> getWideningOperator() {
		return new EmptyOperator<>();
	}
	
	@Override
	public IAbstractStateBinaryOperator<EmptyDomainState<VARDECL>> getMergeOperator() {
		return new EmptyOperator<>();
	}
	
	@Override
	public IAbstractPostOperator<EmptyDomainState<VARDECL>, ACTION, VARDECL> getPostOperator() {
		return new EmptyPostOperator<>();
	}
	
	@Override
	public int getDomainPrecision() {
		// This domain is the least-expressive domain there is.
		return 0;
	}
}
