/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Test Library.
 *
 * The ULTIMATE Test Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Test Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Test Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Test Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Test Library grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.ultimatetest.suites.evals;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsDefinitions;
import de.uni_freiburg.informatik.ultimate.test.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimate.test.UltimateTestCase;
import de.uni_freiburg.informatik.ultimate.test.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.decider.SafetyCheckTestResultDecider;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ColumnDefinition.Aggregate;
import de.uni_freiburg.informatik.ultimate.test.logs.summaries.ConversionContext;
import de.uni_freiburg.informatik.ultimate.test.util.DirectoryFileEndingsPair;
import de.uni_freiburg.informatik.ultimate.ultimatetest.suites.AbstractEvalTestSuite;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public class LoopAccelerationDevelTestsuite extends AbstractEvalTestSuite {

	private static final String[] C = new String[] { ".i", ".c" };
	private static final String[] BPL = new String[] { ".bpl" };
	private static final int DEFAULT_LIMIT = Integer.MAX_VALUE;

	@SuppressWarnings("unchecked")
	private static final Triple<String, String[], String>[] TOOLCHAINS =
			new Triple[] {

					// BPL
					// new Triple<>("AutomizerBplTransformed.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_BB_Debug.epf"),
					// new Triple<>("AutomizerBplTransformed.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Ahmed_Debug.epf"),

					// new Triple<>("AutomizerBpl.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Werner_Debug.epf"),
					// new Triple<>("AutomizerBplTransformed.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Werner_Debug.epf"),

					// new Triple<>("AutomizerBplTransformed.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_EE.epf"),
					// new Triple<>("AutomizerBplTransformed.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_LE.epf"),
					// new Triple<>("AutomizerBpl.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_EE.epf"),
					// new Triple<>("AutomizerBpl.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_Debug.epf"),
					// new Triple<>("AutomizerBpl.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing.epf"),
					//
					new Triple<>("AutomizerBplTransformed.xml", BPL,
							"loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing_Debug.epf"),
					// new Triple<>("AutomizerBplTransformed.xml", BPL,
					// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing.epf"),
					//
					new Triple<>("AutomizerBpl.xml", BPL,
							"loopacceleration/svcomp-Reach-32bit-Automizer_Default_Mohr.epf"),
					new Triple<>("AutomizerBplTransformed.xml", BPL,
							"loopacceleration/svcomp-Reach-32bit-Automizer_Default_Mohr.epf"),
			// new Triple<>("AutomizerBplTransformed.xml", BPL,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Mohr_Debug.epf"),

			// C
			// new Triple<>("AutomizerCInline.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing.epf"),
			// new Triple<>("AutomizerCInlineTransformed.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_Woelfing.epf"),
			//
			// new Triple<>("AutomizerCInlineTransformed.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_EE.epf"),
			// new Triple<>("AutomizerCInlineTransformed.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_LE.epf"),
			// new Triple<>("AutomizerCInline.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_EE.epf"),

			// new Triple<>("AutomizerCInlineTransformed.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_noMod_EE.epf"),
			// new Triple<>("AutomizerCInlineTransformed.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_noMod_LE.epf"),
			// new Triple<>("AutomizerCInline.xml", C,
			// "loopacceleration/svcomp-Reach-32bit-Automizer_Default_FastUpr_noMod_EE.epf"),

			};

	private static final String[] INPUT = new String[] {

			// Normal regressions
			// "examples/programs/loopAcceleration",
			"examples/programs/loopAcceleration/unsafeLoop.bpl",
			// "examples/svcomp/loop-acceleration/const_true-unreach-call1.i",
			// "examples/svcomp/loop-acceleration/const_false-unreach-call1.i",
			// "examples/svcomp/loops/sum03_true-unreach-call_false-termination.i",
			// "examples/programs/loopAcceleration/loopAccelerationFastUPR/OctagonTest_Default.bpl",
			// "examples/programs/loopAcceleration/loopAccelerationBB/loop1.bpl",

			// Errors in Woelfing
			// "examples/svcomp/loop-lit/cggmp2005_true-unreach-call_true-termination.c.i",
			// "examples/svcomp/loops/for_bounded_loop1_false-unreach-call_true-termination.i",
			// "examples/svcomp/loop-invgen/SpamAssassin-loop_true-unreach-call_false-termination.i",
			// "examples/svcomp/loops/while_infinite_loop_4_false-unreach-call_true-termination.i",
			// "examples/svcomp/loops/for_infinite_loop_2_true-unreach-call_false-termination.i",

			// example: cannot handle arrays
			// "examples/svcomp/bitvector-loops/verisec_sendmail__tTflag_arr_one_loop_false-unreach-call.i",

			// errors in FastUPR
			// "examples/svcomp/loop-industry-pattern/nested_true-unreach-call.c"
			// "examples/svcomp/loop-invgen/NetBSD_loop_true-unreach-call_true-termination.i",

			// unsafe expected safe
			// "examples/svcomp/loop-acceleration/functions_true-unreach-call1_true-termination.i",
			// "examples/svcomp/loops/linear_sea.ch_true-unreach-call.i",
			// "examples/svcomp/loops/nec40_true-unreach-call_true-termination.i",
			// "examples/svcomp/loops/while_infinite_loop_3_true-unreach-call_false-termination.i",

	};

	@Override
	protected long getTimeout() {
		// timeout in ms
		return 30 * 1000;
	}

	@Override
	public ITestResultDecider constructITestResultDecider(final UltimateRunDefinition urd) {
		// boolean param decides whether timeouts/unknowns are fails (false) or success (true)
		return new SafetyCheckTestResultDecider(urd, false);
	}

	@Override
	protected ColumnDefinition[] getColumnDefinitions() {
		return new ColumnDefinition[] {
				new ColumnDefinition("Runtime (ns)", "Avg. runtime", ConversionContext.Divide(1000000000, 2, " s"),
						Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("Allocated memory end (bytes)", "Memory",
						ConversionContext.Divide(1048576, 2, " MB"), Aggregate.Max, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallIterations.toString(), "Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntIterations.toString(), "AI Iter{-}ations",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntStrong.toString(), "AI Strong",
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.AbstIntTime.toString(), "AI Avg. Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition(CegarLoopStatisticsDefinitions.OverallTime.toString(), "Trace Abstraction Time",
						ConversionContext.Divide(1000000000, 2, " s"), Aggregate.Sum, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_NumberOfCodeBlocks", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_SizeOfPredicatesFP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_SizeOfPredicatesBP", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_Conjuncts in SSA", null, ConversionContext.BestFitNumber(),
						Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("TraceCheckerStatistics_Conjuncts in UnsatCore", null,
						ConversionContext.BestFitNumber(), Aggregate.Ignore, Aggregate.Average),
				new ColumnDefinition("InterpolantCoveringCapability", "ICC", ConversionContext.Percent(true, 2),
						Aggregate.Ignore, Aggregate.Average), };
	}

	@Override
	public Collection<UltimateTestCase> createTestCases() {
		for (final Triple<String, String[], String> triple : TOOLCHAINS) {
			final DirectoryFileEndingsPair[] pairs = new DirectoryFileEndingsPair[INPUT.length];
			for (int i = 0; i < INPUT.length; ++i) {
				pairs[i] = new DirectoryFileEndingsPair(INPUT[i], triple.getSecond(), DEFAULT_LIMIT);
			}
			addTestCase(triple.getFirst(), triple.getThird(), pairs);
		}
		return super.createTestCases();
	}
}
