/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.BuchiComplementFKVNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.LevelRankingState;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.StateWithRankInfo;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Marking;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.Place;
import de.uni_freiburg.informatik.ultimate.automata.petrinet.julian.Condition;

public class StringFactory extends StateFactory<String> {

	@Override
	public String intersection(String s1, String s2) {
  		StringBuilder sb = new StringBuilder("[");
  		sb.append(s1).append(", ").append(s2).append("]");
  		return sb.toString();
	}
	
	public String intersectBuchi(String s1, String s2, int track) {
		StringBuilder sb = new StringBuilder("[");
		sb.append(s1).append(", ").append(s2).append(", track").append(track).append("]");
		return sb.toString();
	}

	@Override
	public String determinize(Map<String, Set<String>> down2up) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (String down : down2up.keySet()) {
			Iterator<String> it = down2up.get(down).iterator();
			String up = it.next();
			sb.append("(").append(down).append(",").append(up).append(")");
			while (it.hasNext()) {
				up = it.next();
				sb.append(", ");
				sb.append("(").append(down).append(",").append(up).append(")");				
			}
		}
		sb.append("}");
		return sb.toString();
	}

	@Override
	public String createSinkStateContent() {
		return new String("∅SinkState");
	}
	
	@Override
	public String createEmptyStackState() {
		return "€";
	}

	
	
//	@Override
//	public String getContentOnPetriNet2FiniteAutomaton(Collection<String> cList) {
//		StringBuilder sb = new StringBuilder();
//		sb.append("{");
//		boolean firstElement = true;
//		for (String content :cList) {
//			if (firstElement) {
//				firstElement = false;
//			}
//			else {
//				sb.append(",");
//			}
//			sb.append(content);
//		}
//		sb.append("}");
//		return sb.toString();
//	}

	
	
	@Override
	public String getContentOnPetriNet2FiniteAutomaton(Marking<?, String> marking) {
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		boolean firstElement = true;
		for (Place<?, String> place  : marking) {
			if (firstElement) {
				firstElement = false;
			}
			else {
				sb.append(",");
			}
			sb.append(place.getContent());
		}
		sb.append("}");
		return sb.toString();
	}


	@Override
	public String getBlackContent(String c) {
		return "Black:"+c;
	}


	@Override
	public String getWhiteContent(String c) {
		return "White:"+c;
	}
	
	@Override
	public String buchiComplementFKV(LevelRankingState<?, String> compl) {
		
		StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (StateWithRankInfo<String> down : compl.getDownStates()) {
			for (StateWithRankInfo<String> up : compl.getUpStates(down)) {
				sb.append("(");
				sb.append(down.getState());
				sb.append(",");
				if (down.hasRank()) {
					sb.append(down.getRank());
					if (down.isInO()) {
						sb.append("X");
					}
				} else {
					sb.append("∞");
				}
				sb.append(",");
				sb.append(up.getState());
				sb.append(",");
				if (up.hasRank()) {
					sb.append(up.getRank());
					if (up.isInO()) {
						sb.append("X");
					}
				} else {
					sb.append("∞");
				}
				sb.append(")");					
			}
		}
		sb.append("}");
		return sb.toString();
	}
	
	

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ContentFactory#complementBuchiDeterministicNonFinal(java.lang.Object)
	 */
	@Override
	public String complementBuchiDeterministicNonFinal(String c) {
		// TODO Auto-generated method stub
		return "NonFinal:"+c;
	}

	/* (non-Javadoc)
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ContentFactory#complementBuchiDeterministicFinal(java.lang.Object)
	 */
	@Override
	public String complementBuchiDeterministicFinal(String c) {
		return "Final:"+c;
	}
	
	@Override
	public String minimize(Collection<String> states) {
		if(states == null) {
			return "{}";
		}
		StringBuilder sb = new StringBuilder("{");
		for(Iterator<String> it = states.iterator(); it.hasNext(); ) {
			sb.append(it.next());
			if(it.hasNext()) {
				sb.append(", ");
			}
		}
		return sb.append("}").toString();
	}

	@Override
	public String createDoubleDeckerContent(String down, String up) {
		return "<" + down + "," + up + ">"; 
	}

	@Override
	public String constructBuchiSVWState(Integer stateNb, Integer tmaNb) {
		StringBuilder sb = new StringBuilder("(");
		sb.append(stateNb);
		sb.append(",");
		sb.append(tmaNb);
		sb.append(")");
		return sb.toString();
	}

	@Override
	public String finitePrefix2net(Condition<?, String> c) {
		return c.toString();
	}
	
	@Override
	public String senwa(String entry, String state) {
		String result = state + " (entry " + entry + ")";
		return result;
	}
	
}
