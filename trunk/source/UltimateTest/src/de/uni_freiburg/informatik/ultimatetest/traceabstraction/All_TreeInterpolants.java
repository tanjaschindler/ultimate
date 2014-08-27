/**
 * 
 */
package de.uni_freiburg.informatik.ultimatetest.traceabstraction;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimatetest.UltimateRunDefinition;
import de.uni_freiburg.informatik.ultimatetest.UltimateTestCase;
import de.uni_freiburg.informatik.ultimatetest.decider.ITestResultDecider;
import de.uni_freiburg.informatik.ultimatetest.decider.SafetyCheckTestResultDecider2;

/**
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class All_TreeInterpolants extends
		AbstractTraceAbstractionTestSuite {
	private static final String[] m_Directories = {
		"examples/programs/regression",
//		"examples/programs/quantifier",
//		"examples/programs/recursivePrograms",
//		"examples/programs/toy"
//		"examples/termination/AProVE"
	};
	
	// Time out for each test case in milliseconds
	private static int m_Timeout = 10000;

	private static final boolean s_Boogie_TreeInterpolants = true;
	private static final boolean s_C_TreeInterpolants = true;
	
	
	@Override
	public Collection<UltimateTestCase> createTestCases() {
		if (s_Boogie_TreeInterpolants) {
			addTestCases(
					"AutomizerBpl.xml",
					"traceAbstractionTestSuite/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".bpl"},
//				    "TraceAbstraction via tree interpolation",
//				    "Boogie",
				    m_Timeout);
		} 
		if (s_C_TreeInterpolants) {
			addTestCases(
					"AutomizerC.xml",
					"traceAbstractionTestSuite/TreeInterpolants.epf",
				    m_Directories,
				    new String[] {".c", ".i"},
//				    "TraceAbstraction via tree interpolation",
//				    "C",
				    m_Timeout);
		}
		return super.createTestCases();
	}
}
