/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.statistics.Benchmark;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsType;

/**
 * Statistics provider for error automaton construction.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class ErrorAutomatonStatisticsGenerator implements IStatisticsDataProvider {
	private static final String ERROR_AUTOMATON_CONSTRUCTION_TIME = "ErrorAutomatonConstructionTime";
	private static final String ERROR_AUTOMATON_DIFFERENCE_TIME = "ErrorAutomatonDifferenceTime";
	private final Benchmark mBenchmark;
	private boolean mRunningConstruction = false;
	private boolean mRunningDifference = false;
	private int mTraceLength = -1;
	private final List<AutomatonStatisticsEntry> mAutomatonStatistics = new LinkedList<>();

	public ErrorAutomatonStatisticsGenerator() {
		mBenchmark = new Benchmark();
		mBenchmark.register(ERROR_AUTOMATON_CONSTRUCTION_TIME);
	}

	public void startErrorAutomatonConstructionTime() {
		assert !mRunningConstruction : "Timing already running";
		mRunningConstruction = true;
		mBenchmark.start(ERROR_AUTOMATON_CONSTRUCTION_TIME);
	}

	public void stopErrorAutomatonConstructionTime() {
		assert mRunningConstruction : "Timing not running";
		mRunningConstruction = false;
		mBenchmark.pause(ERROR_AUTOMATON_CONSTRUCTION_TIME);
	}

	public void startErrorAutomatonDifferenceTime() {
		assert !mRunningDifference : "Timing already running";
		mRunningDifference = true;
		mBenchmark.start(ERROR_AUTOMATON_DIFFERENCE_TIME);
	}

	public void stopErrorAutomatonDifferenceTime() {
		assert mRunningDifference : "Timing not running";
		mRunningDifference = false;
		mBenchmark.pause(ERROR_AUTOMATON_DIFFERENCE_TIME);
	}

	public void reportTraceLength(final int length) {
		assert mTraceLength == -1 : "Length already reported";
		mTraceLength = length;
	}

	public void finishAutomatonInstance() {
		if (mRunningConstruction || mRunningDifference || mTraceLength == -1) {
			throw new IllegalAccessError("Not all statistics data were provided.");
		}
		final long constructionTime =
				(long) mBenchmark.getElapsedTime(ERROR_AUTOMATON_CONSTRUCTION_TIME, TimeUnit.NANOSECONDS);
		final long differenceTime =
				(long) mBenchmark.getElapsedTime(ERROR_AUTOMATON_DIFFERENCE_TIME, TimeUnit.NANOSECONDS);
		final int traceLength = mTraceLength;
		mTraceLength = -1;
		mAutomatonStatistics.add(new AutomatonStatisticsEntry(constructionTime, differenceTime, traceLength));
	}

	@Override
	public Collection<String> getKeys() {
		return ErrorAutomatonStatisticsType.getInstance().getKeys();
	}

	@Override
	public Object getValue(final String key) {
		final ErrorAutomatonStatisticsDefinitions keyEnum =
				Enum.valueOf(ErrorAutomatonStatisticsDefinitions.class, key);
		switch (keyEnum) {
			case TotalNumber:
				return mAutomatonStatistics.size();
			case TraceLengthAvg:
				return getAverageTraceLength();
			case ErrorAutomatonConstructionTimeAvg:
				return getAverageErrorAutomatonConstructionTime(stats -> stats.mConstructionTime);
			case ErrorAutomatonConstructionTimeTotal:
				return getTotalErrorAutomatonConstructionTime(stats -> stats.mConstructionTime);
			case ErrorAutomatonDifferenceTimeAvg:
				return getAverageErrorAutomatonConstructionTime(stats -> stats.mDifferenceTime);
			case ErrorAutomatonDifferenceTimeTotal:
				return getTotalErrorAutomatonConstructionTime(stats -> stats.mDifferenceTime);
			default:
				throw new AssertionError("Unknown key: " + key);
		}
	}

	private int getAverageTraceLength() {
		final int total = mAutomatonStatistics.size();
		if (total == 0) {
			return 0;
		}
		int result = 0;
		for (final AutomatonStatisticsEntry stats : mAutomatonStatistics) {
			result += stats.mTraceLength;
		}
		return result / total;
	}

	private long getAverageErrorAutomatonConstructionTime(final Function<AutomatonStatisticsEntry, Long> stats2long) {
		final int total = mAutomatonStatistics.size();
		if (total == 0) {
			return 0L;
		}
		final long time = getTotalErrorAutomatonConstructionTime(stats2long);
		return time / total;
	}

	private long getTotalErrorAutomatonConstructionTime(final Function<AutomatonStatisticsEntry, Long> stats2long) {
		long time = 0L;
		for (final AutomatonStatisticsEntry stats : mAutomatonStatistics) {
			time += stats2long.apply(stats);
		}
		return time;
	}

	@Override
	public IStatisticsType getBenchmarkType() {
		return ErrorAutomatonStatisticsType.getInstance();
	}

	/**
	 * Statistics per error automaton construction.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private static class AutomatonStatisticsEntry {
		private final long mConstructionTime;
		private final int mTraceLength;
		private final long mDifferenceTime;

		public AutomatonStatisticsEntry(final long constructionTime, final long differenceTime, final int traceLength) {
			mDifferenceTime = differenceTime;
			mConstructionTime = constructionTime;
			mTraceLength = traceLength;
		}
	}
}
