/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.TermClassifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.CegarLoopStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders.MultiTrackInterpolantAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckerUtils;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.SMTInterpol;

/**
 * {@link IRefinementStrategy} that first tries {@code CVC4} in bitvector mode,
 * then {@code}, and finally {@link SMTInterpol}.
 * <p>
 * The class uses a {@link MultiTrackInterpolantAutomatonBuilder} for
 * constructing the interpolant automaton.
 *
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class WalrusRefinementStrategy<LETTER extends IIcfgTransition<?>>
		extends MultiTrackTraceAbstractionRefinementStrategy<LETTER> {
	public WalrusRefinementStrategy(final ILogger logger, final TaCheckAndRefinementPreferences prefs,
			final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final PredicateUnifier predicateUnifier,
			final AssertionOrderModulation<LETTER> assertionOrderModulation,
			final IRun<LETTER, IPredicate, ?> counterexample, final IAutomaton<LETTER, IPredicate> abstraction,
			final TAPreferences taPrefsForInterpolantConsolidation, final int iteration,
			final CegarLoopStatisticsGenerator cegarLoopBenchmarks) {
		super(logger, prefs, services, cfgSmtToolkit, predicateFactory, predicateUnifier, assertionOrderModulation,
				counterexample, abstraction, taPrefsForInterpolantConsolidation, iteration, cegarLoopBenchmarks);
	}

	@Override
	protected Iterator<Track> initializeInterpolationTechniquesList() {
		final List<Track> list = new ArrayList<>(3);
		final TermClassifier tc = TraceCheckerUtils.classifyTermsInTrace(mCounterexample.getWord(),
				mCsToolkit.getAxioms());
		if (tc.getOccuringSortNames().contains(SmtSortUtils.FLOATINGPOINT_SORT)) {
			if (tc.getOccuringFunctionNames().contains(SmtUtils.FP_TO_IEEE_BV_EXTENSION)
					|| !tc.getOccuringQuantifiers().isEmpty()) {
				// we need Z3, but Z3 is already added later, hence do nothing
			} else {
				list.add(Track.MATHSAT_FPBP);
			}
		} else {
			list.add(Track.CVC4_FPBP);
		}
		list.add(Track.Z3_FPBP);
		return list.iterator();
	}

	@Override
	protected String getCvc4Logic() {
		return LOGIC_CVC4_BITVECTORS;
	}
}
