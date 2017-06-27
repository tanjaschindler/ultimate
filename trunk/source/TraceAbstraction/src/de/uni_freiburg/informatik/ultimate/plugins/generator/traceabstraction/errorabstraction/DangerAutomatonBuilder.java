/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction;

import java.util.ArrayDeque;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.MonolithicImplicationChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.PredicateTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.TermDomainOperationProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.IPredicatePostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.QuantifierEliminationPostprocessor;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.IterativePredicateTransformer.TraceInterpolationException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.DefaultTransFormulas;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TracePredicates;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Constructs a danger automaton for a given error trace.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type in the trace/automaton
 */
public class DangerAutomatonBuilder<LETTER extends IIcfgTransition<?>> implements IErrorAutomatonBuilder<LETTER> {
	/**
	 * {@code true} iff predicates are unified.
	 */
	private static final boolean UNIFY_PREDICATES = false;

	private final NestedWordAutomaton<LETTER, IPredicate> mResult;
	private final int mLastIteration;

	private final IUltimateServiceProvider mServices;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param predicateFactory
	 *            predicate factory
	 * @param predicateUnifier
	 *            predicate unifier
	 * @param csToolkit
	 *            SMT toolkit
	 * @param simplificationTechnique
	 *            simplification technique
	 * @param xnfConversionTechnique
	 *            XNF conversion technique
	 * @param symbolTable
	 *            symbol table
	 * @param predicateFactoryForAutomaton
	 *            predicate factory for the danger automaton (will eventually be
	 *            removed by a refactoring)
	 * @param abstraction
	 *            current program abstraction
	 * @param trace
	 *            error trace
	 * @param iteration
	 *            CEGAR loop iteration in which this builder was created
	 */
	@SuppressWarnings("squid:S00107")
	public DangerAutomatonBuilder(final IUltimateServiceProvider services, final PredicateFactory predicateFactory,
			final IPredicateUnifier predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace,
			final int iteration) {
		mServices = services;
		final ILogger logger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mLastIteration = iteration;
		final PredicateUnificationMechanism internalPredicateUnifier = new PredicateUnificationMechanism(
				predicateUnifier, UNIFY_PREDICATES);

		mResult = constructDangerAutomaton(new AutomataLibraryServices(services), logger, predicateFactory,
				internalPredicateUnifier, csToolkit, simplificationTechnique, xnfConversionTechnique, symbolTable,
				predicateFactoryForAutomaton, abstraction, trace);
	}

	@Override
	public ErrorAutomatonType getType() {
		return ErrorAutomatonType.DANGER_AUTOMATON;
	}

	@Override
	public NestedWordAutomaton<LETTER, IPredicate> getResultBeforeEnhancement() {
		return mResult;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, IPredicate> getResultAfterEnhancement() {
		return mResult;
	}

	@Override
	public IPredicate getErrorPrecondition() {
		return null;
	}

	@Override
	public boolean hasAutomatonInIteration(final int iteration) {
		return mLastIteration == iteration;
	}

	@Override
	public InterpolantAutomatonEnhancement getEnhancementMode() {
		return InterpolantAutomatonEnhancement.NONE;
	}

	private NestedWordAutomaton<LETTER, IPredicate> constructDangerAutomaton(final AutomataLibraryServices services,
			final ILogger logger, final PredicateFactory predicateFactory,
			final PredicateUnificationMechanism predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable,
			final PredicateFactoryForInterpolantAutomata predicateFactoryForAutomaton,
			final INestedWordAutomaton<LETTER, IPredicate> abstraction, final NestedWord<LETTER> trace) {
		final HashRelation<IPredicate, IPredicate> abstState2dangStates = new HashRelation<>();
		final IValueConstruction<Set<IPredicate>, IPredicate> valueConstruction = new IValueConstruction<Set<IPredicate>, IPredicate>() {

			@Override
			public IPredicate constructValue(final Set<IPredicate> key) {
				return predicateFactory.or(false, key);
			}
		};
		final ConstructionCache<Set<IPredicate>, IPredicate> disjunctionProvider = new ConstructionCache<>(
				valueConstruction);
		final Deque<IPredicate> worklist = new ArrayDeque<>();

		final Set<IPredicate> predicates = constructPredicates(logger, predicateFactory, predicateUnifier, csToolkit,
				simplificationTechnique, xnfConversionTechnique, symbolTable, trace);

		final NestedWordAutomaton<LETTER, IPredicate> result = new NestedWordAutomaton<>(services,
				new VpAlphabet<>(abstraction), predicateFactoryForAutomaton);

		final IPredicate trueState = predicateUnifier.getTruePredicate();
		result.addState(false, true, trueState);
		for (final IPredicate state : abstraction.getFinalStates()) {
			abstState2dangStates.addPair(state, trueState);
			worklist.add(state);
		}

		final PredicateTransformer<Term, IPredicate, TransFormula> pt = new PredicateTransformer<Term, IPredicate, TransFormula>(
				csToolkit.getManagedScript(), new TermDomainOperationProvider(mServices, csToolkit.getManagedScript()));
		final MonolithicImplicationChecker ic = new MonolithicImplicationChecker(mServices,
				csToolkit.getManagedScript());

		while (!worklist.isEmpty()) {
			final IPredicate state = worklist.pop();
			for (final IncomingInternalTransition<LETTER, IPredicate> in : abstraction.internalPredecessors(state)) {
				final IPredicate pred = in.getPred();
				final Set<Term> statesThatHaveSuccTerms = new HashSet<>();
				for (final OutgoingInternalTransition<LETTER, IPredicate> out : abstraction.internalSuccessors(pred)) {
					final IPredicate succInAbstraction = out.getSucc();
					final Set<IPredicate> succDisjunctionInDanger = abstState2dangStates.getImage(succInAbstraction);
					if (succDisjunctionInDanger.isEmpty()) {
						// successor state does not (yet?) have corresponding predicate
						continue;
					}
					final IPredicate succInDanger = disjunctionProvider.getOrConstruct(succDisjunctionInDanger);
					final Term wp = pt.weakestPrecondition(succInDanger, out.getLetter().getTransformula());
					final Term pre = SmtUtils.not(csToolkit.getManagedScript().getScript(), wp);
					statesThatHaveSuccTerms.add(pre);
				}
				final IPredicate statesThatHaveSucc = predicateFactory
						.newPredicate(SmtUtils.or(csToolkit.getManagedScript().getScript(), statesThatHaveSuccTerms));
				final Set<IPredicate> coveredPredicates = new HashSet<IPredicate>();
				for (final IPredicate candidate : predicates) {
					final Validity icres = ic.checkImplication(candidate, false, statesThatHaveSucc, false);
					if (icres == Validity.VALID) {
						coveredPredicates.add(candidate);
					}
				}
				if (coveredPredicates.isEmpty()) {
					// no need to continue, a state labeled with false will not
					// help us
				}
				IPredicate newState;
				final Set<IPredicate> oldAbstraction = abstState2dangStates.getImage(pred);
				if (coveredPredicates.equals(oldAbstraction)) {
					// do nothing
					final IPredicate oldstate = disjunctionProvider.getOrConstruct(oldAbstraction);
					newState = oldstate;
				} else {
					// predicate changed we have to "backtrack" (want to try
					// if we can computer better predecessors)
					if (!worklist.contains(pred)) {
						worklist.add(pred);
					}

					newState = disjunctionProvider.getOrConstruct(coveredPredicates);
					final boolean isInitial = abstraction.isInitial(pred);
					final boolean isFinal = abstraction.isFinal(pred);
					result.addState(isInitial, isFinal, newState);
					if (!oldAbstraction.isEmpty()) {
						final IPredicate oldstate = disjunctionProvider.getOrConstruct(oldAbstraction);
						// there was already a state, we have to copy all its
						// incoming
						// transitions and remove it
						copyAllIncomingTransitions(oldstate, newState, result);
						result.removeState(oldstate);
					}
				}
				// add outgoing transitions to all successors that finally
				// contributed
				// (i.e., where the intersection of pre with the abstract state
				// is not empty)
				for (final OutgoingInternalTransition<LETTER, IPredicate> out : abstraction.internalSuccessors(pred)) {
					final IPredicate succInAbstraction = out.getSucc();
					final Set<IPredicate> succDisjunctionInDanger = abstState2dangStates.getImage(succInAbstraction);
					if (succDisjunctionInDanger.isEmpty()) {
						// successor state does not (yet?) have corresponding predicate
						continue;
					}
					final IPredicate succInDanger = disjunctionProvider.getOrConstruct(succDisjunctionInDanger);
					assert result.getStates().contains(succInDanger);
					final Term wp = pt.weakestPrecondition(succInDanger, out.getLetter().getTransformula());
					final Term pre = SmtUtils.not(csToolkit.getManagedScript().getScript(), wp);
					final Term conjunction = SmtUtils.and(csToolkit.getManagedScript().getScript(),
							Arrays.asList(new Term[] { pre, newState.getFormula() }));
					final LBool lBool = SmtUtils.checkSatTerm(csToolkit.getManagedScript().getScript(), conjunction);
					if (lBool != lBool.UNSAT) {
						// edge probably (result might be unknown) contributed
						// we add it
						result.addInternalTransition(newState, out.getLetter(), succInDanger);
						// Matthias: maybe this crashes and we have to check if edge was
						// already added
					}
				}
			}
		}

		return result;
	}

	private Set<IPredicate> constructPredicates(final ILogger logger, final PredicateFactory predicateFactory,
			final PredicateUnificationMechanism predicateUnifier, final CfgSmtToolkit csToolkit,
			final SimplificationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique,
			final IIcfgSymbolTable symbolTable, final NestedWord<LETTER> trace) throws AssertionError {
		final IterativePredicateTransformer ipt = new IterativePredicateTransformer(predicateFactory, csToolkit.getManagedScript(), 
				csToolkit.getModifiableGlobalsTable(), mServices, trace, null, predicateUnifier.getFalsePredicate(), 
				null, predicateUnifier.getTruePredicate(), simplificationTechnique, xnfConversionTechnique, symbolTable);
		final List<IPredicatePostprocessor> postprocessors;
			final QuantifierEliminationPostprocessor qepp = new QuantifierEliminationPostprocessor(mServices, logger,
					csToolkit.getManagedScript(), predicateFactory, simplificationTechnique, xnfConversionTechnique);
			postprocessors = Collections.singletonList(qepp);
			final DefaultTransFormulas dtf = new DefaultTransFormulas(trace, null, null,
					Collections.emptySortedMap(), csToolkit.getOldVarsAssignmentCache(), false);
		TracePredicates tp = null;
		try {
			tp = ipt.computePreSequence(dtf, postprocessors, false);
		} catch (final TraceInterpolationException e) {
			throw new AssertionError("failed to compute sequence " + e);
		}
		final Set<IPredicate> predicates = new HashSet<>(tp.getPredicates());
		predicates.add(tp.getPostcondition());
		predicates.add(tp.getPrecondition());
		return predicates;
	}

	private void copyAllIncomingTransitions(final IPredicate oldstate, final IPredicate newState,
			final NestedWordAutomaton<LETTER, IPredicate> result) {
		for (final IncomingInternalTransition<LETTER, IPredicate> in : result.internalPredecessors(oldstate)) {
			result.addInternalTransition(in.getPred(), in.getLetter(), newState);
		}

	}
}
