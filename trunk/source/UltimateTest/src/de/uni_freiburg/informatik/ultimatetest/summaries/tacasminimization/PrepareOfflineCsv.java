package de.uni_freiburg.informatik.ultimatetest.summaries.tacasminimization;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderAggregator.Aggregation;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderColumnFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderFromFile;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderPartition;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderRowFilter;
import de.uni_freiburg.informatik.ultimate.util.csv.CsvProviderTransformerCombinator;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderTransformer;

/**
 * Test class to produce benchmark results.
 * <p>
 * Parses a CSV, groups all benchmarks by file name, removes all groups which contain null values, and puts all
 * remaining groups in a CSV again.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class PrepareOfflineCsv {
	private static final String TRANSITIONS_RETURN_OUTPUT = "TRANSITIONS_RETURN_OUTPUT";
	private static final String TRANSITIONS_RETURN_INPUT = "TRANSITIONS_RETURN_INPUT";
	private static final String TRANSITIONS_CALL_OUTPUT = "TRANSITIONS_CALL_OUTPUT";
	private static final String TRANSITIONS_CALL_INPUT = "TRANSITIONS_CALL_INPUT";
	private static final String TRANSITIONS_INTERNAL_OUTPUT = "TRANSITIONS_INTERNAL_OUTPUT";
	private static final String TRANSITIONS_INTERNAL_INPUT = "TRANSITIONS_INTERNAL_INPUT";
	private static final String TIME_SOLVING = "TIME_SOLVING";
	private static final String TIME_PREPROCESSING = "TIME_PREPROCESSING";
	private static final String STATES_REDUCTION_RELATIVE = "STATES_REDUCTION_RELATIVE";
	private static final String STATES_REDUCTION_ABSOLUTE = "STATES_REDUCTION_ABSOLUTE";
	private static final String SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS = "SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS";
	private static final String RUNTIME_TOTAL = "RUNTIME_TOTAL";
	private static final String RESULT_TRANSITIONS = "RESULT_TRANSITIONS";
	private static final String RESULT_NONDETERMINISTIC_STATES = "RESULT_NONDETERMINISTIC_STATES";
	private static final String REMOVED_TRANSITIONS = "REMOVED_TRANSITIONS";
	private static final String NUMBER_OF_CLAUSES = "NUMBER_OF_CLAUSES";
	private static final String NUMBER_OF_VARIABLES = "NUMBER_OF_VARIABLES";
	private static final String BUCHI_TRANSITIONS = "BUCHI_TRANSITIONS";
	private static final String BUCHI_NONDETERMINISTIC_STATES = "BUCHI_NONDETERMINISTIC_STATES";
	private static final String ALPHABET_SIZE_RETURN = "ALPHABET_SIZE_RETURN";
	private static final String ALPHABET_SIZE_CALL = "ALPHABET_SIZE_CALL";
	private static final String ALPHABET_SIZE_INTERNAL = "ALPHABET_SIZE_INTERNAL";
	private static final String STATES_OUTPUT = "STATES_OUTPUT";
	private static final String STATES_INPUT = "STATES_INPUT";
	private static final String FILE = "File";
	
	private static final String INPUT_FILE_NAME = "AutomizerOffline.csv";
	
	private PrepareOfflineCsv() {
		// main class
	}
	
	public static void main(final String[] args) {
		final File inputFile = new File(INPUT_FILE_NAME);
		final ICsvProvider<String> input = CsvProviderFromFile.parse(inputFile);
		
		final List<ICsvProviderTransformer<String>> transformers = new ArrayList<>();
		final CsvProviderTransformerCombinator<String> transformer =
				new CsvProviderTransformerCombinator<>(transformers);
		
		transformers.add(getOperationFilter());
		transformers.add(getInterestingColumnFilter());
		transformers.add(getNonNullFilter());
		
		// full table
		final ICsvProvider<String> result = transformer.transform(input);
		System.out.println(result.toCsv(new StringBuilder(), ",").toString());
		
		// separated tables
		final String statesColumn = STATES_INPUT;
		final int[] thresholds = new int[] { 100, 500, 2500 };
		final CsvProviderPartition<String> partition = new CsvProviderPartition<>(result, statesColumn, thresholds);
		final CsvProviderAggregator<String> csvProviderAggregator = getStatesAggregation();
		for (final ICsvProvider<String> csv : partition.getCsvs()) {
			System.out.println(csv.toCsv(new StringBuilder(), ",").toString());
			
			// aggregate
			final ICsvProvider<String> aggregatedCsv = csvProviderAggregator.transform(csv);
			System.out.println(aggregatedCsv.toCsv(new StringBuilder(), ",").toString());
		}
	}
	
	private static ICsvProviderTransformer<String> getOperationFilter() {
		final String[] allowedOperations = new String[] { "minimizeNwaMaxSat2" };
		final Map<String, Set<String>> column2allowedValues = Collections.singletonMap(
				StatisticsType.OPERATION_NAME.toString(), new HashSet<>(Arrays.asList(allowedOperations)));
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllowedValuesRowFilter<>(column2allowedValues));
	}
	
	private static ICsvProviderTransformer<String> getInterestingColumnFilter() {
		final String[] forbiddenNames = new String[] { "Toolchain", "Settings", "ATS_ID", "BUCHI_ALPHABET_SIZE",
				"BUCHI_TRANSITION_DENSITY_MILLION", "OPERATION_NAME", "RESULT_TRANSITION_DENSITY_MILLION",
				"RESULT_ALPHABET_SIZE" };
		final CsvProviderColumnFilter.NameFilter forbiddenNamesFilter = new CsvProviderColumnFilter.NameFilter(
				new HashSet<>(Arrays.asList(forbiddenNames)));
		return new CsvProviderColumnFilter<>(x -> !x.isEmpty() && !forbiddenNamesFilter.test(x));
	}
	
	private static ICsvProviderTransformer<String> getNonNullFilter() {
		return new CsvProviderRowFilter<>(new CsvProviderRowFilter.AllEntriesNonNullFilter<>());
	}
	
	private static CsvProviderAggregator<String> getStatesAggregation() {
		final Map<String, CsvProviderAggregator.Aggregation> column2aggregation = new HashMap<>();
		
		column2aggregation.put(FILE, Aggregation.IGNORE);
		
		column2aggregation.put(ALPHABET_SIZE_INTERNAL, Aggregation.AVERAGE);
		column2aggregation.put(ALPHABET_SIZE_CALL, Aggregation.AVERAGE);
		column2aggregation.put(ALPHABET_SIZE_RETURN, Aggregation.AVERAGE);
		column2aggregation.put(BUCHI_NONDETERMINISTIC_STATES, Aggregation.AVERAGE);
		column2aggregation.put(BUCHI_TRANSITIONS, Aggregation.AVERAGE);
		column2aggregation.put(NUMBER_OF_VARIABLES, Aggregation.AVERAGE);
		column2aggregation.put(NUMBER_OF_CLAUSES, Aggregation.AVERAGE);
		column2aggregation.put(REMOVED_TRANSITIONS, Aggregation.AVERAGE);
		column2aggregation.put(RESULT_NONDETERMINISTIC_STATES, Aggregation.AVERAGE);
		column2aggregation.put(RESULT_TRANSITIONS, Aggregation.AVERAGE);
		column2aggregation.put(RUNTIME_TOTAL, Aggregation.AVERAGE);
		column2aggregation.put(SIZE_MAXIMAL_INITIAL_EQUIVALENCE_CLASS, Aggregation.AVERAGE);
		column2aggregation.put(STATES_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(STATES_OUTPUT, Aggregation.AVERAGE);
		column2aggregation.put(STATES_REDUCTION_ABSOLUTE, Aggregation.AVERAGE);
		column2aggregation.put(STATES_REDUCTION_RELATIVE, Aggregation.AVERAGE);
		column2aggregation.put(TIME_PREPROCESSING, Aggregation.AVERAGE);
		column2aggregation.put(TIME_SOLVING, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_INTERNAL_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_INTERNAL_OUTPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_CALL_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_CALL_OUTPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_RETURN_INPUT, Aggregation.AVERAGE);
		column2aggregation.put(TRANSITIONS_RETURN_OUTPUT, Aggregation.AVERAGE);
		
		return new CsvProviderAggregator<>(column2aggregation);
	}
}
