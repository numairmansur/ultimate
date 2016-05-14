package de.uni_freiburg.informatik.ultimate.util.statistics;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.InCaReCounter;

public abstract class AStatisticsType<T extends Enum<T> & IStatisticsElement> implements IStatisticsType {
	
	public static Function<Object, Function<Object,Object>> s_IntegerAddition = 
			x -> y -> (Integer) x + (Integer) y;
	public static Function<Object, Function<Object,Object>> s_LongAddition = 
			x -> y -> (Long) x + (Long) y;
	public static Function<Object, Function<Object,Object>> s_IncareAddition = 
			x -> y -> { ((InCaReCounter) x).add((InCaReCounter) y); return x;};
	public static Function<Object, Function<Object,Object>> s_StatisticsDataAggregation = 
			x -> y -> { ((StatisticsData) x).aggregateBenchmarkData((StatisticsData) y); return x;};
	public static Function<String, Function<Object,String>> s_KeyBeforeData = 
			key -> data -> key + ": " + String.valueOf(data);
	public static Function<String, Function<Object,String>> s_DataBeforeKey = 
			key -> data -> String.valueOf(data) + " " + key;
	public static Function<String, Function<Object,String>> s_TimeBeforeKey = 
			key -> time -> prettyprintNanoseconds( (Long) time) + " " + key;
	
	private final Class<T> m_Keys;
	
	public AStatisticsType(Class<T> keys) {
		super();
		m_Keys = keys;
	}

	@Override
	public Collection<String> getKeys() {
		List<String> result = new ArrayList<>();
		for (Enum<?> test : m_Keys.getEnumConstants()) {
			result.add(test.toString());
		}
		return result;
	}

	@Override
	public Object aggregate(String key, Object value1, Object value2) {
		T keyEnum = (T) Enum.valueOf(m_Keys, key);
		Object result = keyEnum.aggregate(value1, value2);
		return result;
	}

	@Override
	public String prettyprintBenchmarkData(IStatisticsDataProvider benchmarkData) {
		StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (String key : getKeys()) {
			if (first) {
				first = false;
			} else {
				sb.append(", ");
			}
			Object value = benchmarkData.getValue(key);
			T keyE = (T) Enum.valueOf(m_Keys, key);
			sb.append(keyE.prettyprint(value));
		}
		return sb.toString();
	}
	
	
	public static String prettyprintBenchmarkData(String key, IStatisticsDataProvider benchmarkData) {
		return key + " " + benchmarkData.getValue(key);
	}
	
	
	public static String prettyprintNanoseconds(long time) {
		long seconds = time / 1000000000;
		long tenthDigit = (time / 100000000) % 10;
		return seconds + "." + tenthDigit + "s";
	}

}
