package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.io.File;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimatetest.TestSummary;

public class TraceAbstractionTestSummary extends TestSummary {

	private int mCount;

	private String mLogFilePath;
	/**
	 * A map from file names to benchmark results.
	 */
	private Map<String, String> m_TraceAbstractionBenchmarks;
	
	public TraceAbstractionTestSummary(String testSuiteCanonicalName, String logFilePath) {
		super(testSuiteCanonicalName);
		mLogFilePath = logFilePath;
		mCount = 0;
		m_TraceAbstractionBenchmarks = new HashMap<String, String>();
	}
	
	public void addTraceAbstractionBenchmarks(String filename, String benchmarkResults) {
		m_TraceAbstractionBenchmarks.put(filename, benchmarkResults);
	}
	
	@Override
	public String getSummaryLog() {

		StringBuilder sb = new StringBuilder();
		int total = 0;
		mCount = 0;

		sb.append("################# ").append("Trace Abstraction Test Summary")
				.append(" #################").append("\n");

		sb.append(getSummaryLog(mSuccess, "SUCCESSFUL TESTS"));
		int success = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(mUnknown, "UNKNOWN TESTS"));
		int unknown = mCount;
		total = total + mCount;
		mCount = 0;
		sb.append(getSummaryLog(mFailure, "FAILED TESTS"));
		int fail = mCount;
		total = total + mCount;
		sb.append("\n");
		sb.append("====== SUMMARY for ").append("Trace Abstraction")
				.append(" ======").append("\n");
		sb.append("Success:\t" + success).append("\n");
		sb.append("Unknown:\t" + unknown).append("\n");
		sb.append("Failures:\t" + fail).append("\n");
		sb.append("Total:\t\t" + total);
		return sb.toString();
	
	}
	
	private String getSummaryLog(HashMap<String, Summary> map, String title) {
		StringBuilder sb = new StringBuilder();
		sb.append("====== ").append(title).append(" =====").append("\n");
		for (Entry<String, Summary> entry : map.entrySet()) {
			sb.append("\t").append(entry.getKey()).append("\n");

			for (Entry<String, String> fileMsgPair : entry.getValue().getFileToMessage()
					.entrySet()) {
				sb.append("\t\t").append(fileMsgPair.getKey()).append(": ")
						.append(fileMsgPair.getValue()).append("\n");
				// Add TraceAbstraction benchmarks
				sb.append("\t\t").append(m_TraceAbstractionBenchmarks.get(fileMsgPair.getKey())).append("\n");
			}

			sb.append("\tCount for ").append(entry.getKey()).append(": ")
					.append(entry.getValue().getCount()).append("\n");
			sb.append("\t--------").append("\n");
			mCount = mCount + entry.getValue().getCount();
		}
		sb.append("Count: ").append(mCount);
		sb.append("\n\n");
		return sb.toString();
	}


	@Override
	public File getSummaryLogFile() {
		return new File(mLogFilePath);
	}

}
