/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.LookaheadPartitionConstructor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.LookaheadPartitionConstructor.PartitionPairsWrapper;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaMaxSat2;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa.DelayedNwaGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.nwa.DelayedNwaSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.DirectNwaGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.nwa.DirectNwaSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.nwa.FairNwaGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.nwa.FairNwaSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaDelayedFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaDirectFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.util.PartitionBackedSetOfPairs;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Operation that compares the different types of simulation methods for nwa
 * reduction.<br/>
 * The resulting automaton is the input automaton.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * 
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class CompareReduceNwaSimulation<LETTER, STATE> extends CompareReduceBuchiSimulation<LETTER, STATE> {

	/**
	 * Compares the different types of simulation methods for nwa reduction.
	 * Resulting automaton is the input automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The nwa automaton to compare with
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public CompareReduceNwaSimulation(final AutomataLibraryServices services,
			final IMergeStateFactory<STATE> stateFactory, final INestedWordAutomatonSimple<LETTER, STATE> operand)
					throws AutomataOperationCanceledException {
		super(services, stateFactory, operand);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.performance.CompareReduceBuchiSimulation#operationName()
	 */
	@Override
	public String operationName() {
		return "compareReduceNwaSimulation";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.performance.CompareReduceBuchiSimulation#
	 * verifyAutomatonValidity(de.uni_freiburg.informatik.ultimate.automata.
	 * nwalibrary.INestedWordAutomaton)
	 */
	@Override
	public void verifyAutomatonValidity(final INestedWordAutomatonSimple<LETTER, STATE> automaton) {
		// Do noting to accept nwa automata
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.
	 * simulation.performance.CompareReduceBuchiSimulation#
	 * addGeneralAutomataPerformanceForExternalMethod(de.uni_freiburg.informatik
	 * .ultimate.automata.nestedword.INestedWordAutomaton,
	 * de.uni_freiburg.informatik.ultimate.automata.nestedword.
	 * INestedWordAutomaton)
	 */
	@Override
	protected void addGeneralAutomataPerformanceForExternalMethod(final INestedWordAutomaton<LETTER, STATE> input,
			final INestedWordAutomaton<LETTER, STATE> output) {
		super.addGeneralAutomataPerformanceForExternalMethod(input, output);

		final AutomataLibraryServices services = getServices();
		final Analyze<LETTER, STATE> inputAnalyzer = new Analyze<>(services, input, true);

		mCountingMeasures.put(ECountingMeasure.BUCHI_ALPHABET_SIZE_INTERNAL,
				inputAnalyzer.getNumberOfSymbols(SymbolType.INTERNAL));
		mCountingMeasures.put(ECountingMeasure.BUCHI_ALPHABET_SIZE_CALL,
				inputAnalyzer.getNumberOfSymbols(SymbolType.CALL));
		mCountingMeasures.put(ECountingMeasure.BUCHI_ALPHABET_SIZE_RETURN,
				inputAnalyzer.getNumberOfSymbols(SymbolType.RETURN));

		mCountingMeasures.put(ECountingMeasure.BUCHI_TRANSITIONS_INTERNAL,
				inputAnalyzer.getNumberOfTransitions(SymbolType.INTERNAL));
		mCountingMeasures.put(ECountingMeasure.BUCHI_TRANSITIONS_CALL,
				inputAnalyzer.getNumberOfTransitions(SymbolType.CALL));
		mCountingMeasures.put(ECountingMeasure.BUCHI_TRANSITIONS_RETURN,
				inputAnalyzer.getNumberOfTransitions(SymbolType.RETURN));

		mCountingMeasures.put(ECountingMeasure.BUCHI_TRANSITION_INTERNAL_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.INTERNAL) * 1_000_000));
		mCountingMeasures.put(ECountingMeasure.BUCHI_TRANSITION_CALL_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.CALL) * 1_000_000));
		mCountingMeasures.put(ECountingMeasure.BUCHI_TRANSITION_RETURN_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.RETURN) * 1_000_000));

		final Analyze<LETTER, STATE> outputAnalyzer = new Analyze<>(services, output, true);

		mCountingMeasures.put(ECountingMeasure.RESULT_ALPHABET_SIZE_INTERNAL,
				outputAnalyzer.getNumberOfSymbols(SymbolType.INTERNAL));
		mCountingMeasures.put(ECountingMeasure.RESULT_ALPHABET_SIZE_CALL,
				outputAnalyzer.getNumberOfSymbols(SymbolType.CALL));
		mCountingMeasures.put(ECountingMeasure.RESULT_ALPHABET_SIZE_RETURN,
				outputAnalyzer.getNumberOfSymbols(SymbolType.RETURN));

		mCountingMeasures.put(ECountingMeasure.RESULT_TRANSITIONS_INTERNAL,
				outputAnalyzer.getNumberOfTransitions(SymbolType.INTERNAL));
		mCountingMeasures.put(ECountingMeasure.RESULT_TRANSITIONS_CALL,
				outputAnalyzer.getNumberOfTransitions(SymbolType.CALL));
		mCountingMeasures.put(ECountingMeasure.RESULT_TRANSITIONS_RETURN,
				outputAnalyzer.getNumberOfTransitions(SymbolType.RETURN));

		mCountingMeasures.put(ECountingMeasure.RESULT_TRANSITION_INTERNAL_DENSITY_MILLION,
				(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.INTERNAL) * 1_000_000));
		mCountingMeasures.put(ECountingMeasure.RESULT_TRANSITION_CALL_DENSITY_MILLION,
				(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.CALL) * 1_000_000));
		mCountingMeasures.put(ECountingMeasure.RESULT_TRANSITION_RETURN_DENSITY_MILLION,
				(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.RETURN) * 1_000_000));
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.performance.CompareReduceBuchiSimulation#
	 * measureMethodPerformance(java.lang.String,
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.ESimulationType, boolean,
	 * de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices,
	 * long,
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory,
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.
	 * INestedWordAutomaton)
	 */
	@Override
	protected void measureMethodPerformance(final String name, final ESimulationType type, final boolean useSCCs,
			final AutomataLibraryServices services, final long timeout, final IMergeStateFactory<STATE> stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operandRaw) {
		final ILogger logger = getLogger();
		final IProgressAwareTimer progressTimer = services.getProgressAwareTimer().getChildTimer(timeout);
		boolean timedOut = false;
		boolean outOfMemory = false;
		Object method = null;
		if (!(operandRaw instanceof IDoubleDeckerAutomaton)) {
			throw new IllegalArgumentException("Input must be of type " + IDoubleDeckerAutomaton.class);
		}
		final IDoubleDeckerAutomaton<LETTER, STATE> operand = (IDoubleDeckerAutomaton<LETTER, STATE>) operandRaw;

		final PartitionPairsWrapper<STATE> partitionAndPairs = new LookaheadPartitionConstructor<>(
				services, operand, true).getResult();
		final Collection<Set<STATE>> possibleEquivalenceClasses = partitionAndPairs.getPartition();

		try {
			if (type.equals(ESimulationType.DIRECT)) {
				final PartitionBackedSetOfPairs<STATE> possibleEquivalenceClassesForDirect =
						new LookaheadPartitionConstructor<>(services, operand, true).getPartition();

				final DirectNwaGameGraph<LETTER, STATE> graph = new DirectNwaGameGraph<>(services, stateFactory,
						progressTimer, logger, operand, possibleEquivalenceClassesForDirect.getRelation());
				graph.generateGameGraphFromAutomaton();
				final DirectNwaSimulation<LETTER, STATE> sim = new DirectNwaSimulation<>(progressTimer, logger, useSCCs,
						stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(ESimulationType.DELAYED)) {
				final DelayedNwaGameGraph<LETTER, STATE> graph = new DelayedNwaGameGraph<>(services,
						stateFactory, progressTimer, logger, operand, possibleEquivalenceClasses);
				graph.generateGameGraphFromAutomaton();
				final DelayedNwaSimulation<LETTER, STATE> sim = new DelayedNwaSimulation<>(progressTimer, logger,
						useSCCs, stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(ESimulationType.FAIR)) {
				final FairNwaGameGraph<LETTER, STATE> graph = new FairNwaGameGraph<>(services,
						stateFactory, progressTimer, logger, operand, possibleEquivalenceClasses);
				graph.generateGameGraphFromAutomaton();
				final FairNwaSimulation<LETTER, STATE> sim = new FairNwaSimulation<>(progressTimer, logger, useSCCs,
						stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(ESimulationType.DIRECT_FULL_MULTIPEBBLE)) {
				final long startTime = System.currentTimeMillis();
				method = new ReduceNwaDirectFullMultipebbleSimulation<>(services, stateFactory, operand);
				setExternalOverallTime(System.currentTimeMillis() - startTime);
			} else if (type.equals(ESimulationType.DELAYED_FULL_MULTIPEBBLE)) {
				final long startTime = System.currentTimeMillis();
				method = new ReduceNwaDelayedFullMultipebbleSimulation<>(services, stateFactory, operand);
				setExternalOverallTime(System.currentTimeMillis() - startTime);
			} else if (type.equals(ESimulationType.EXT_MINIMIZESEVPA)) {
				final long startTime = System.currentTimeMillis();
				method = new MinimizeSevpa<>(getServices(), stateFactory, operand);
				setExternalOverallTime(System.currentTimeMillis() - startTime);
			} else if (type.equals(ESimulationType.EXT_SHRINKNWA)) {
				final long startTime = System.currentTimeMillis();
				method = new ShrinkNwa<>(getServices(), stateFactory, operand);
				setExternalOverallTime(System.currentTimeMillis() - startTime);
			} else if (type.equals(ESimulationType.EXT_MINIMIZENWAMAXSAT)) {
				final long startTime = System.currentTimeMillis();
				method = new MinimizeNwaPmaxSat<>(services, stateFactory, operand,
						new PartitionBackedSetOfPairs<>(possibleEquivalenceClasses),
						new MinimizeNwaMaxSat2.Settings<>());
				setExternalOverallTime(System.currentTimeMillis() - startTime);
			}
		} catch (final AutomataOperationCanceledException e) {
			logger.info("Method timed out.");
			timedOut = true;
		} catch (final OutOfMemoryError e) {
			logger.info("Method has thrown an out of memory error.");
			outOfMemory = true;
		}
		appendMethodPerformanceToLog(method, name, type, useSCCs, timedOut, outOfMemory, operand);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * simulation.performance.CompareReduceBuchiSimulation#measurePerformances(
	 * java.lang.String, long,
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory,
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.
	 * reachableStatesAutomaton.NestedWordAutomatonReachableStates)
	 */
	@Override
	protected void measurePerformances(final String automatonName, final long timeOutMillis,
			final IMergeStateFactory<STATE> stateFactory,
			final NestedWordAutomatonReachableStates<LETTER, STATE> reachableOperand) {
		// Direct nwa simulation without SCC
//		measureMethodPerformance(automatonName, ESimulationType.DIRECT, false, getServices(), timeOutMillis,
//				stateFactory, reachableOperand);
		// Delayed nwa simulation without SCC
//		measureMethodPerformance(automatonName, ESimulationType.DELAYED, false, getServices(), timeOutMillis,
//				stateFactory, reachableOperand);
		
		// Full multi-pebble simulation
		measureMethodPerformance(automatonName, ESimulationType.DIRECT_FULL_MULTIPEBBLE, false, getServices(),
				timeOutMillis, stateFactory, reachableOperand);
		measureMethodPerformance(automatonName, ESimulationType.DELAYED_FULL_MULTIPEBBLE, false, getServices(),
				timeOutMillis, stateFactory, reachableOperand);

		// Other minimization methods
//		measureMethodPerformance(automatonName, ESimulationType.EXT_MINIMIZESEVPA, false, mServices, timeOutMillis,
//				stateFactory, reachableOperand);
//		measureMethodPerformance(automatonName, ESimulationType.EXT_SHRINKNWA, false, mServices, timeOutMillis,
//				stateFactory, reachableOperand);
//		measureMethodPerformance(automatonName, ESimulationType.EXT_MINIMIZENWAMAXSAT, false, mServices, timeOutMillis,
//				stateFactory, reachableOperand);
	}
}
