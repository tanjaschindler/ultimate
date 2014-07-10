package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceItem.PreferenceType;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences;


/**
 * Initializer class for LassoRanker's preferences in Ultimate's GUI
 * 
 * @see Preferences
 * @author Jan Leike
 */
public class PreferencesInitializer extends UltimatePreferenceInitializer {
	/*
	 * Default values for GUI-only preferences
	 */
	public static final boolean s_simplify_result = true;
	public static final boolean s_enable_affine_template = true;
	public static final boolean s_enable_nested_template = true;
	public static final int     s_nested_template_size = 4;
	public static final boolean s_enable_multiphase_template = true;
	public static final int     s_multiphase_template_size = 2;
	public static final boolean s_enable_lex_template = true;
	public static final int     s_lex_template_size = 2;
	public static final boolean s_enable_piecewise_template = true;
	public static final int     s_piecewise_template_size = 2;
	public static final boolean s_enable_parallel_template = true;
	public static final int     s_parallel_template_size = 2;
	
	/*
	 * Preferences Labels
	 */
	public static final String LABEL_termination_analysis =
			"Termination analysis";
	public static final String LABEL_nontermination_analysis =
			"Nontermination analysis";
	public static final String LABEL_num_strict_invariants =
			"Number of strict supporting invariants";
	public static final String LABEL_num_non_strict_invariants =
			"Number of non-strict supporting invariants";
	public static final String LABEL_nondecreasing_invariants =
			"Only non-decreasing invariants";
	public static final String LABEL_compute_integral_hull =
			"Compute integral hull";
	public static final String LABEL_annotate_terms =
			"Add annotations to SMT terms";
	public static final String LABEL_simplify_result =
			"Simplify discovered termination arguments";
	public static final String LABEL_enable_affine_template =
			"Affine template";
	public static final String LABEL_enable_nested_template =
			"Nested template";
	public static final String LABEL_nested_template_size =
			"Nested template size";
	public static final String LABEL_enable_multiphase_template =
			"Multiphase template";
	public static final String LABEL_multiphase_template_size =
			"Multiphase template size";
	public static final String LABEL_enable_lex_template =
			"Lexicographic template";
	public static final String LABEL_lex_template_size =
			"Lexicographic template size";
	public static final String LABEL_enable_piecewise_template =
			"Piecewise template";
	public static final String LABEL_piecewise_template_size =
			"Piecewise template size";
	public static final String LABEL_enable_parallel_template =
			"Parallel template";
	public static final String LABEL_parallel_template_size =
			"Parallel template size";
	public static final String LABEL_use_external_solver =
			"Use external SMT solver";
	public static final String LABEL_smt_solver_command =
			"SMT solver command";
	public static final String LABEL_dump_smt_script =
			"Dump SMT script to file";
	public static final String LABEL_path_of_dumped_script =
			"Path of dumped script";
	
	@Override
	protected UltimatePreferenceItem<?>[] initDefaultPreferences() {
		Preferences preferences = new Preferences(); // Get default preferences
		return new UltimatePreferenceItem<?>[] {
				new UltimatePreferenceItem<AnalysisType>(
						LABEL_termination_analysis,
						preferences.termination_analysis,
						PreferenceType.Combo,
						AnalysisType.allChoices()),
				new UltimatePreferenceItem<AnalysisType>(
						LABEL_nontermination_analysis,
						preferences.nontermination_analysis,
						PreferenceType.Combo,
						AnalysisType.allChoices()),
				new UltimatePreferenceItem<Integer>(
						LABEL_num_strict_invariants,
						preferences.num_strict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Integer>(
						LABEL_num_non_strict_invariants,
						preferences.num_non_strict_invariants,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_nondecreasing_invariants,
						preferences.nondecreasing_invariants,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_compute_integral_hull,
						preferences.compute_integral_hull,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_annotate_terms,
						preferences.annotate_terms,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_simplify_result,
						s_simplify_result,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_affine_template,
						s_enable_affine_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_nested_template,
						s_enable_nested_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_nested_template_size,
						s_nested_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_multiphase_template,
						s_enable_multiphase_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_multiphase_template_size,
						s_multiphase_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_lex_template,
						s_enable_lex_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_lex_template_size,
						s_lex_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_piecewise_template,
						s_enable_piecewise_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_piecewise_template_size,
						s_piecewise_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_enable_parallel_template,
						s_enable_parallel_template,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<Integer>(
						LABEL_parallel_template_size,
						s_parallel_template_size,
						PreferenceType.Integer),
				new UltimatePreferenceItem<Boolean>(
						LABEL_use_external_solver,
						true,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(
						LABEL_smt_solver_command,
						preferences.smt_solver_command,
						PreferenceType.String),
				new UltimatePreferenceItem<Boolean>(
						LABEL_dump_smt_script,
						preferences.dumpSmtSolverScript,
						PreferenceType.Boolean),
				new UltimatePreferenceItem<String>(
						LABEL_path_of_dumped_script,
						preferences.path_of_dumped_script,
						PreferenceType.String)
		};
	}
	
	/**
	 * @return the preferences currently set in the GUI
	 */
	public static Preferences getGuiPreferences() {
		// Get default preferences
		Preferences preferences = new Preferences();
		
		UltimatePreferenceStore store =
				new UltimatePreferenceStore(Activator.s_PLUGIN_ID);
		preferences.termination_analysis =
				store.getEnum(LABEL_termination_analysis,
						AnalysisType.class);
		preferences.nontermination_analysis =
				store.getEnum(LABEL_nontermination_analysis,
						AnalysisType.class);
		preferences.num_strict_invariants = store.getInt(
				LABEL_num_strict_invariants
		);
		preferences.num_non_strict_invariants = store.getInt(
				LABEL_num_non_strict_invariants
		);
		preferences.nondecreasing_invariants = store.getBoolean(
				LABEL_nondecreasing_invariants
		);
		preferences.compute_integral_hull = store.getBoolean(
				LABEL_compute_integral_hull
		);
		preferences.annotate_terms = store.getBoolean(
				LABEL_annotate_terms
		);
		preferences.simplify_result = store.getBoolean(
				LABEL_simplify_result
		);
		preferences.dumpSmtSolverScript = store.getBoolean(
				LABEL_dump_smt_script
		);
		preferences.externalSolver = store.getBoolean(
				LABEL_use_external_solver
		);
		preferences.smt_solver_command = store.getString(
				LABEL_smt_solver_command
		);
		preferences.path_of_dumped_script = store.getString(
				LABEL_path_of_dumped_script
		);
		return preferences;
	}
	
	@Override
	protected String getPlugID() {
		return Activator.s_PLUGIN_ID;
	}
	
	@Override
	public String getPreferencePageTitle() {
		return Activator.s_PLUGIN_NAME;
	}
}