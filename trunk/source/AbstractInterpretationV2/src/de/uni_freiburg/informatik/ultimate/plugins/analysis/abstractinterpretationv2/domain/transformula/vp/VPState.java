/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Yu-Wen Chen
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.QuotedObject;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermVarsProc;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 *
 * @author Yu-Wen Chen (yuwenchen1105@gmail.com)
 *
 */
public class VPState implements IAbstractState<VPState, CodeBlock, IProgramVar> {

	private static final String TERM_FUNC_NAME_AND = "and";
	private static final String TERM_TRUE = "true";
	private static final String TERM_FUNC_NAME_DISTINCT = "distinct";
	

	private final Set<IProgramVar> mVars;

	private final Map<EqNode, EqGraphNode> mEqNodeToEqGraphNodeMap;

	private Set<VPDomainSymmetricPair<EqNode>> mDisEqualitySet;

	private final VPDomain mDomain;
	private final Script mScript;
	private final boolean mIsTop;

	/**
	 * Constructor for bottom state only.
	 *
	 * @param domain
	 */
	VPState(final VPDomain domain) {
		this(Collections.emptyMap(), Collections.emptySet(), Collections.emptySet(), domain, false);
	}

	/*
	 * Constructor to be used by VPStateFactory.createTopState() only.
	 */
	VPState(final Map<EqNode, EqGraphNode> eqNodeToEqGraphNodeMap,
			final Set<VPDomainSymmetricPair<EqNode>> disEqualitySet, 
			final Set<IProgramVar> vars, 
			final VPDomain domain, 
			final boolean isTop) {
		mVars = vars;
		mEqNodeToEqGraphNodeMap = Collections.unmodifiableMap(eqNodeToEqGraphNodeMap);
		mDisEqualitySet = Collections.unmodifiableSet(disEqualitySet);
		mDomain = domain;
		mScript = mDomain.getManagedScript().getScript();
		mIsTop = isTop;
	}

	public Set<VPDomainSymmetricPair<EqNode>> getDisEqualitySet() {
		return mDisEqualitySet;
	}

	public void setDisEqualitySet(final Set<VPDomainSymmetricPair<EqNode>> disEqualitySet) {
		mDisEqualitySet = disEqualitySet;
	}

	public Map<EqNode, EqGraphNode> getEqNodeToEqGraphNodeMap() {
		return mEqNodeToEqGraphNodeMap;
	}

	void restorePropagation(final EqFunctionNode node) {

		final Set<EqFunctionNode> fnNodeSet = mDomain.getArrayIdToEqFnNodeMap().getImage(node.getFunction());
		for (final EqFunctionNode fnNode1 : fnNodeSet) {
			for (final EqFunctionNode fnNode2 : fnNodeSet) {
				if (!fnNode1.equals(fnNode2) && find(getEqNodeToEqGraphNodeMap().get(fnNode1))
						.equals(find(getEqNodeToEqGraphNodeMap().get(fnNode2)))) {
					equalityPropagation(getEqNodeToEqGraphNodeMap().get(fnNode1),
							getEqNodeToEqGraphNodeMap().get(fnNode2));
				}
			}
		}
	}

	public void addToDisEqSet(final EqNode node1, final EqNode node2) {
		getDisEqualitySet().add(new VPDomainSymmetricPair<>(node1, node2));
	}

	/**
	 * Use disEqualitySet to check if there exist contradiction in the graph.
	 *
	 * @return true if there is contradiction
	 */
	boolean checkContradiction() {

		for (final VPDomainSymmetricPair<EqNode> disEqPair : getDisEqualitySet()) {
			if (find(mEqNodeToEqGraphNodeMap.get(disEqPair.getFirst()))
					.equals(find(mEqNodeToEqGraphNodeMap.get(disEqPair.getSecond())))) {
				return true;
			}
		}
		return false;
	}

	/**
	 * Returns the representative of a @param node's equivalence class.
	 *
	 * @param node
	 * @return
	 */
	public EqGraphNode find(final EqGraphNode node) {
		if (node.getRepresentative().equals(node)) {
			return node;
		}
		return find(node.getRepresentative());
	}

	/**
	 * Returns the parents of all nodes in @param node's congruence class.
	 *
	 * @param node
	 * @return
	 */
	private Set<EqGraphNode> ccpar(final EqGraphNode node) {
		return find(node).getCcpar();
	}

	public HashRelation<IProgramVarOrConst, List<EqGraphNode>> ccchild(final EqGraphNode node) {
		return find(node).getCcchild();
	}

	/**
	 * Check whether @param node1 and @param node2 are congruent.
	 *
	 * @param node1
	 * @param node2
	 * @return true if they are congruent
	 */
	private boolean congruent(final EqGraphNode node1, final EqGraphNode node2) {
		if (!(node1.eqNode instanceof EqFunctionNode) || !(node2.eqNode instanceof EqFunctionNode)) {
			return false;
		}

		final EqFunctionNode fnNode1 = (EqFunctionNode) node1.eqNode;
		final EqFunctionNode fnNode2 = (EqFunctionNode) node2.eqNode;

		if (!(fnNode1.getFunction().equals(fnNode2.getFunction()))) {
			return false;
		}
		return congruentIgnoreFunctionSymbol(fnNode1, fnNode2);
	}

	/**
	 * Checks if the arguments of the given EqFunctionNodes are all congruent.
	 *
	 * @param fnNode1
	 * @param fnNode2
	 * @return
	 */
	boolean congruentIgnoreFunctionSymbol(final EqFunctionNode fnNode1, final EqFunctionNode fnNode2) {
		assert fnNode1.getArgs() != null && fnNode2.getArgs() != null;
		assert fnNode1.getArgs().size() == fnNode2.getArgs().size();

		for (int i = 0; i < fnNode1.getArgs().size(); i++) {
			final EqNode fnNode1Arg = fnNode1.getArgs().get(i);
			final EqNode fnNode2Arg = fnNode2.getArgs().get(i);
			if (!find(getEqNodeToEqGraphNodeMap().get(fnNode1Arg))
					.equals(find(getEqNodeToEqGraphNodeMap().get(fnNode2Arg)))) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Merge two congruence class. propagation.
	 *
	 * @param i1
	 * @param i2
	 */
	void merge(final EqGraphNode node1, final EqGraphNode node2) {
		if (!find(node1).equals(find(node2))) {
			union(node1, node2);
			equalityPropagation(node1, node2);
		}
	}

	/**
	 * Union of two equivalence classes.
	 *
	 * @param node1
	 * @param node2
	 */
	private void union(final EqGraphNode node1, final EqGraphNode node2) {

		final EqGraphNode graphNode1Find = find(node1);
		final EqGraphNode graphNode2Find = find(node2);

		if (!graphNode1Find.equals(graphNode2Find)) {
			graphNode2Find.addToReverseRepresentative(graphNode1Find);
			graphNode1Find.setRepresentative(graphNode2Find);
			graphNode2Find.addToCcpar(graphNode1Find.getCcpar());
			for (final Entry<IProgramVarOrConst, List<EqGraphNode>> entry : graphNode1Find.getCcchild().entrySet()) {
				graphNode2Find.getCcchild().addPair(entry.getKey(), entry.getValue());
			}
			// graphNode2Find.addToCcchild(graphNode1Find.getCcchild());
		}
	}

	private void equalityPropagation(final EqGraphNode node1, final EqGraphNode node2) {
		final Set<EqGraphNode> p1 = ccpar(node1);
		final Set<EqGraphNode> p2 = ccpar(node2);

		for (final EqGraphNode t1 : p1) {
			for (final EqGraphNode t2 : p2) {
				if (!(find(t1).equals(find(t2))) && congruent(t1, t2)) {
					merge(t1, t2);
				}
			}
		}
	}

	// private boolean isArray(final TermVariable term) {
	// return mDomain.getArrayIdToEqFnNodeMap().containsKey(term);
	// }

//	/**
//	 * Erase all the edges in the graph of this state.
//	 */
//	public void clearState() {
//		mDisEqualitySet.clear();
//		for (EqGraphNode graphNode : this.mEqNodeToEqGraphNodeMap.values()) {
//			graphNode.setNodeToInitial();
//		}
//	}

	@Override
	public VPState addVariable(final IProgramVar variable) {
		if (mVars.contains(variable)) {
			return this;
		}
		final VPState copy = mDomain.getVpStateFactory().copy(this);
		copy.mVars.add(variable);
		return copy;
	}

	@Override
	public VPState removeVariable(final IProgramVar variable) {
		if (!mVars.contains(variable)) {
			return this;
		}
		final VPState copy = mDomain.getVpStateFactory().copy(this);
		copy.mVars.remove(variable);
		return copy;
	}

	@Override
	public VPState addVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final VPState copy = mDomain.getVpStateFactory().copy(this);
		copy.mVars.addAll(variables);
		return copy;
	}

	@Override
	public VPState removeVariables(final Collection<IProgramVar> variables) {
		if (variables == null || variables.isEmpty()) {
			return this;
		}
		final VPState copy = mDomain.getVpStateFactory().copy(this);
		copy.mVars.removeAll(variables);
		return copy;
	}

	@Override
	public boolean containsVariable(final IProgramVar var) {
		return mVars.contains(var);
	}

	@Override
	public Set<IProgramVar> getVariables() {
		return mVars;
	}

	@Override
	public VPState patch(final VPState dominator) {
		//TODO
//		VPState state = mDomain.getVpStateFactory().copy(this);
//
//		state = mDomain.getVpStateFactory().havocVariables(dominator.mVars, state);
//		
//		List<VPState> conjoined = new ArrayList<>();
//		conjoined.addAll(mDomain.getVpStateFactory().conjoin(state, dominator));
//		
//		
//
//		return result;
		return null;
	}

	@Override
	public boolean isEmpty() {
		return mVars.isEmpty();
	}

	@Override
	public boolean isBottom() {
		return false;
	}

	public boolean isTop() {
		return mIsTop;
	}

	@Override
	public boolean isEqualTo(final VPState other) {

		final Script script = mDomain.getManagedScript().getScript();

		final TermVarsProc tvpThis =
				TermVarsProc.computeTermVarsProc(getTerm(mScript), mScript, mDomain.getSymbolTable());
		final TermVarsProc tvpOther =
				TermVarsProc.computeTermVarsProc(other.getTerm(mScript), mScript, mDomain.getSymbolTable());

		/*
		 * build a term that says (not (this.getTerm() <--> other.getTerm))
		 */
		final Term equiv = script.term(TERM_FUNC_NAME_DISTINCT,
				new Term[] { tvpThis.getClosedFormula(), tvpOther.getClosedFormula() });

		script.echo(new QuotedObject("VPState.isEqualTo()"));
		script.push(1);
		script.assertTerm(equiv);
		final LBool res = script.checkSat();
		script.pop(1);

		return res == LBool.UNSAT;

	}

	@Override
	public SubsetResult isSubsetOf(final VPState other) {
		if (isEqualTo(other)) {
			return SubsetResult.EQUAL;
		}
		return SubsetResult.NONE;
	}

	@Override
	public String toLogString() {

		final StringBuilder sb = new StringBuilder();

		sb.append("Graph: \n");
		for (final EqGraphNode graphNode : mEqNodeToEqGraphNodeMap.values()) {
			if (graphNode.getRepresentative() == graphNode) {
				// print only the interesting graph nodes in full
				sb.append(graphNode.eqNode.toString());
			} else {
				sb.append(graphNode.toString());
			}
			sb.append('\n');
		}

		sb.append("Disequality Set:  \n");
		for (final VPDomainSymmetricPair<EqNode> pair : mDisEqualitySet) {
			sb.append(pair.getFirst().toString());
			sb.append(", ");
			sb.append(pair.getSecond().toString());
			sb.append('\n');
		}

		return sb.toString();
	}

	@Override
	public String toString() {
		return toLogString();
	}

//	@Override
//	public int hashCode() {
//		//TODO: overwrite sensibly
//		return mId;
//	}

	@Override
	public boolean equals(final Object obj) {
		if (!(obj instanceof VPState)) {
			return false;
		}
		if (this == obj) {
			return true;
		}
		
		final VPState other = (VPState) obj;
//		if (mId == other.mId) {
//			return true;
//		} else 
		if (isEqualTo(other)) {
			// TODO: Note that computing isEqualTo can be quite expensive!
			return true;
		}
		return false;
	}

	@Override
	public Term getTerm(final Script script) {

		final Term trueTerm = mDomain.getManagedScript().getScript().term(TERM_TRUE);

		Term disEqualityFirst;
		Term disEqualitySecond;
		final Set<Term> distinctTermSet = new HashSet<>();
		Term disEquality;

		for (final VPDomainSymmetricPair<EqNode> pair : mDisEqualitySet) {
			disEqualityFirst = pair.getFirst().getTerm(mScript);
			disEqualitySecond = pair.getSecond().getTerm(mScript);
			distinctTermSet.add(mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_DISTINCT, disEqualityFirst,
					disEqualitySecond));
		}

		if (distinctTermSet.isEmpty()) {
			disEquality = trueTerm;
		} else if (distinctTermSet.size() == 1) {
			disEquality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					distinctTermSet.iterator().next(), trueTerm);
		} else {
			disEquality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					distinctTermSet.toArray(new Term[distinctTermSet.size()]));
		}

		Term equalityFirst;
		Term equalitySecond;
		final Set<Term> equalityTermSet = new HashSet<>();
		Term equality;

		for (final EqGraphNode graphNode : mEqNodeToEqGraphNodeMap.values()) {
			if (!graphNode.equals(graphNode.getRepresentative())) {
				equalityFirst = graphNode.eqNode.getTerm(mScript);
				equalitySecond = graphNode.getRepresentative().eqNode.getTerm(mScript);
				equalityTermSet.add(mDomain.getManagedScript().getScript().term("=", equalityFirst, equalitySecond));
			}
		}

		if (equalityTermSet.isEmpty()) {
			equality = trueTerm;
		} else if (equalityTermSet.size() == 1) {
			equality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					equalityTermSet.iterator().next(), trueTerm);
		} else {
			equality = mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND,
					equalityTermSet.toArray(new Term[equalityTermSet.size()]));
		}

		return mDomain.getManagedScript().getScript().term(TERM_FUNC_NAME_AND, disEquality, equality);
	}

	public Set<EqNode> getEquivalenceRepresentatives() {
		final Set<EqNode> result = new HashSet<>();
		for (final EqGraphNode egn : mEqNodeToEqGraphNodeMap.values()) {
			if (egn.getRepresentative() == egn) {
				result.add(egn.eqNode);
			}
		}
		return result;
	}

	/**
	 *
	 * @param node
	 * @return All the eqNodes that are in the same equivalence class as node in this state.
	 */
	public Set<EqNode> getEquivalentEqNodes(final EqNode node) {
		final Set<EqNode> result = new HashSet<>();
		for (final EqGraphNode egn : mEqNodeToEqGraphNodeMap.values()) {
			if (find(egn).eqNode == node) {
				result.add(egn.eqNode);
			}
		}
		return result;
	}

	public VPDomain getDomain() {
		return mDomain;
	}

	public boolean mayEqual(EqNode accessingNode1, EqNode accessingNode2) {
		return mDisEqualitySet.contains(new VPDomainSymmetricPair<EqNode>(accessingNode1, accessingNode2));
	}
}
