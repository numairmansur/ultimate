/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.blockencoding.rating.util;

/**
 * To create an rating heuristic, which can decide on basis of the underlying
 * program, we need to store some statistical properties, which we can use for
 * that. <br>
 * So for example, the amount of edges in the graph, or the amount of
 * disjunctions used in the minimization, or the amount of variables, and so
 * on...
 * 
 * @author Stefan Wissert
 * 
 */
public class EncodingStatistics {

	/**
	 * stores the total amount of basic edges in the original graph
	 */
	public static int countOfBasicEdges;

	/**
	 * stores the total amount of created disjunctions (minimizing parallel
	 * edges), this is useful because it seems to be good, to break at some
	 * amount of disjunctions
	 */
	public static int countOfDisjunctions;

	/**
	 * Initializes, all stored statistics. This have to be done, before we start
	 * a new run of block encoding.
	 */
	public static void init() {
		countOfBasicEdges = 0;
		countOfDisjunctions = 0;
	}
	
	/**
	 * 
	 */
	public static void incCountOfBasicEdges() {
		countOfBasicEdges++;
	}
	
	/**
	 * 
	 */
	public static void incCountOfDisjunctions() {
		countOfDisjunctions++;
	}
}
