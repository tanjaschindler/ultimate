package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.List;
import java.util.NoSuchElementException;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.IInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.InterpolantAutomatonBuilderFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategyExceptionBlacklist;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.IInterpolantGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceChecker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils.InterpolantsPreconditionPostcondition;

/**
 * An {@link IRefinementStrategy} allows an {@link IRefinementEngine} to try multiple combinations of
 * <ol>
 * <li>a {@link TraceChecker},</li>
 * <li>an {@link IInterpolantGenerator}, and</li>
 * <li>an {@link InterpolantAutomatonBuilderFactory}.</li>
 * </ol>
 * In the following class documentation this combination is just called "combination".
 * <p>
 * The class contract is that {@link #hasNext(RefinementStrategyAdvance)} returns {@code true} iff
 * {@link #next(RefinementStrategyAdvance)} advances the respective component. Between two calls to
 * {@link #next(RefinementStrategyAdvance)} the respective getter returns the same object. However, for instance by a
 * call to this method to advance the {@link IInterpolantGenerator}, the {@link TraceChecker} may change. A user should
 * hence not store these objects temporarily.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 */
public interface IRefinementStrategy {
	/**
	 * Determines which component of the current combination should be advanced.
	 *
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum RefinementStrategyAdvance {
		/**
		 * Advance the {@link TraceChecker}.
		 */
		TRACE_CHECKER,
		/**
		 * Advance the {@link IInterpolantGenerator}.
		 */
		INTERPOLANT_GENERATOR,
	}
	
	String COMMAND_Z3_NO_TIMEOUT = "z3 -smt2 -in SMTLIB2_COMPLIANT=true";
	String COMMAND_Z3_TIMEOUT = COMMAND_Z3_NO_TIMEOUT + " -t:12000";
	String COMMAND_CVC4_NO_TIMEOUT = "cvc4 --tear-down-incremental --print-success --lang smt";
	String COMMAND_CVC4_TIMEOUT = COMMAND_CVC4_NO_TIMEOUT + " --tlimit-per=12000";
	// 20161214 Matthias: MathSAT does not support timeouts
	String COMMAND_MATHSAT = "mathsat";
	
	long TIMEOUT_SMTINTERPOL = 12_000L;
	long TIMEOUT_NONE_SMTINTERPOL = 0L;
	
	String LOGIC_Z3 = "ALL";
	String LOGIC_CVC4_DEFAULT = "AUFLIRA";
	String LOGIC_CVC4_BITVECTORS = "AUFBV";
	String LOGIC_MATHSAT = "ALL";
	
	/**
	 * @param advance
	 *            How to advance.
	 * @return {@code true} iff there are more combinations available.
	 */
	boolean hasNext(RefinementStrategyAdvance advance);
	
	/**
	 * Changes the combination.<br>
	 * Throws a {@link NoSuchElementException} if there is no next combination; use {@link #hasNext()} to check this.
	 *
	 * @param advance
	 *            how to advance
	 */
	void next(final RefinementStrategyAdvance advance);
	
	/**
	 * @return The trace checker strategy of the current combination.
	 */
	TraceChecker getTraceChecker();
	
	/**
	 * This method must only be called if the {@link TraceChecker} returns {@code UNSAT}.
	 *
	 * @return The interpolant generator of the current combination.
	 */
	IInterpolantGenerator getInterpolantGenerator();
	
	/**
	 * @param ipps
	 *            Sequences of interpolants.
	 * @return The interpolant automaton builder.
	 */
	IInterpolantAutomatonBuilder<CodeBlock, IPredicate>
			getInterpolantAutomatonBuilder(List<InterpolantsPreconditionPostcondition> ipps);
	
	/**
	 * @return Predicate unifier.
	 */
	PredicateUnifier getPredicateUnifier();
	
	/**
	 * @return Object that encapsulates which exceptions are blacklisted.
	 */
	RefinementStrategyExceptionBlacklist getExceptionBlacklist();
}
