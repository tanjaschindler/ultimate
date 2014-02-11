package de.uni_freiburg.informatik.ultimate.website.toolchains;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.website.Setting;
import de.uni_freiburg.informatik.ultimate.website.Tasks.TaskNames;
import de.uni_freiburg.informatik.ultimate.website.Tool;
import de.uni_freiburg.informatik.ultimate.website.Toolchain;

/**
 * @author Markus Lindenmann
 * @author Oleksii Saukh
 * @author Stefan Wissert
 * @author Matthias Heizmann
 */
public class BoogieConcurrentTraceAbstractionTC extends Toolchain {

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setDescription()
	 */
	@Override
	protected String setDescription() {
		return "Concurrent trace abstraction toolchain";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setName()
	 */
	@Override
	protected String setName() {
		return "Concurrent Trace Abstraction";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setId()
	 */
	@Override
	protected String setId() {
		return "boogieConcurrentTraceAbstr";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTaskName()
	 */
	@Override
	protected TaskNames[] setTaskName() {
		return new TaskNames[] { TaskNames.VerifyConcurrentBoogie };
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.website.Toolchain#setTools()
	 */
	@Override
	protected List<Tool> setTools() {
		List<Tool> tools = new ArrayList<Tool>();
		
		List<Setting> oPre = new ArrayList<Setting>();
		List<Setting> mPre = new ArrayList<Setting>();
		tools.add(new Tool(
				"de.uni_freiburg.informatik.ultimate.boogie.preprocessor",
				oPre, mPre, LoggingLevel.WARN));
		
		List<Setting> oRCFGB = new ArrayList<Setting>();
		List<Setting> mRCFGB = new ArrayList<Setting>();
		tools.add(new Tool("RCFGBuilder", oRCFGB, mRCFGB, LoggingLevel.WARN));
        mRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_ExternalSolver, Setting.SettingType.BOOLEAN,
                "external solver", "false", false));
        mRCFGB.add(new Setting(PrefStrings.s_RCFG_LABEL_BlockSize, PrefStrings.s_RCFG_LABEL_BlockSize,
        		new String[] { PrefStrings.s_RCFG_VALUE_Single }, false, new String[] {
        		PrefStrings.s_RCFG_VALUE_Single, PrefStrings.s_RCFG_VALUE_Seq, PrefStrings.s_RCFG_VALUE_Block }, true));
        List<Setting> oTrAbs = new ArrayList<Setting>();
        List<Setting> mTrAbs = new ArrayList<Setting>();
        oTrAbs.add(new Setting("/Compute\\ Interpolants\\ along\\ a\\ Counterexample", Setting.SettingType.STRING,
                "interpolation", "Craig_NestedInterpolation", false));
        oTrAbs.add(new Setting("/Compute\\ Hoare\\ Annotation\\ of\\ negated\\ interpolant\\ automaton,\\ abstraction\\ and\\ CFG", Setting.SettingType.BOOLEAN,
                "Compute Hoare Annotation", "false", true));
        oTrAbs.add(new Setting("/Minimize\\ abstraction", Setting.SettingType.BOOLEAN,
                "Minimize abstraction", "false", true));
        oTrAbs.add(new Setting("/Timeout", Setting.SettingType.INTEGER,
                "Timeout", "20", false));
        mTrAbs.add(new Setting("/DumpPath", Setting.SettingType.STRING,
                "Where to dump", "C:\\Code\\log\\dump", false));
        tools.add(new Tool("TraceAbstraction", oTrAbs, mTrAbs,
                LoggingLevel.WARN));
		List<Setting> oTrConcur = new ArrayList<Setting>();
		List<Setting> mTrConcur = new ArrayList<Setting>();
        tools.add(new Tool("TraceAbstractionConcurrent", oTrConcur, mTrConcur,
                LoggingLevel.WARN));
		return tools;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setPluginsLoggingLevel
	 * ()
	 */
	@Override
	protected LoggingLevel setPluginsLoggingLevel() {
		return LoggingLevel.INFO;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.website.Toolchain#setToolsLoggingLevel
	 * ()
	 */
	@Override
	protected LoggingLevel setToolsLoggingLevel() {
		return LoggingLevel.INFO;
	}
}
