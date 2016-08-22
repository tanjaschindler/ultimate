/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jan Hättig (haettigj@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.SortedMap;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonEpimorphism;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.SuperDifference;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.ITransitionlet;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IncrementalHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.ProgramPoint;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.InductivityCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.AssertCodeBlockOrder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.InterpolationTechnique;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.Minimization;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.InterpolatingTraceCheckerCraig;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.TraceChecker;

/**
 * @author haettigj@informatik.uni-freiburg.de
 * 
 */
public class CegarLoopSWBnonRecursive extends BasicCegarLoop {
	/**
	 * Maps states from the original automaton to corresponding states in the new interpolant automaton.
	 */
	protected AutomatonEpimorphism<IPredicate> mEpimorphism;

	/**
	 * List of states we already added to the new interpolant automaton.
	 */
	protected ArrayList<IPredicate> mAnnotatedStates;

	/**
	 * Holds the nodes and edges of the error path
	 */
	protected NestedRun<CodeBlock, IPredicate> mCounterExamplePath;

	/**
	 * Used for computing the interpolants of additional paths
	 */
	protected TraceChecker mExtraTraceChecker;

	/**
	 * Version of the abstraction, casted as NestedWordAutomaton. It is casted in every call of
	 * constructInterpolantAutomaton.
	 */
	private INestedWordAutomaton<CodeBlock, IPredicate> mNestedAbstraction;

	/**
	 * Version of the abstraction, castet as DoubleDeckerAutomaton. Must be castet in every call of
	 * constructInterpolantAutomaton
	 */
	private IDoubleDeckerAutomaton<CodeBlock, IPredicate> mDoubleDeckerAbstraction;

	/**
	 * When adding additional sub paths to the interpolant automaton. We always start from a state which is already
	 * added. This holds that starting point.
	 */
	protected IPredicate mActualStartingState;

	/***
	 * Precondition of the actual search, corresponds to the actual starting state.
	 */
	protected IPredicate mActualPrecondition;

	/**
	 * When adding additional sub paths to the interpolant automaton This will hold the actual path.
	 */
	protected ArrayList<IPredicate> mActualPath;

	/**
	 * Points to the initial state of the abstraction, i.e. true
	 */
	protected IPredicate mAbstractionInitialState;

	/**
	 * Points to the final state of the abstraction, i.e. false
	 */
	protected IPredicate mAbstractionFinalState;

	/**
	 * This is used to merge states
	 */
	protected PredicateUnifier mPredicateUnifier;

	/**
	 * Count how many paths other than the initial path have been added in the actual iteration.
	 */
	protected int mnofAdditionalPaths;

	/**
	 * Counts how many paths have been explored, but could not be added.
	 */
	protected int mnofDeclinedPaths;

	// / ------- debugging -------
	/**
	 * Holds the error paths, for debbuging.
	 */
	private final ArrayList<String> mErrorPathHistory;
	private final ArrayList<Integer> mnofStates;

	/**
	 * Create and initialize Cegar-Loop.
	 * 
	 * @param name
	 * @param rootNode
	 * @param smtManager
	 * @param traceAbstractionBenchmarks
	 * @param taPrefs
	 * @param errorLocs
	 * @param interpolation
	 * @param computeHoareAnnotation
	 * @param services
	 */
	public CegarLoopSWBnonRecursive(final String name, final RootNode rootNode, final SmtManager smtManager,
			final TraceAbstractionBenchmarks traceAbstractionBenchmarks, final TAPreferences taPrefs,
			final Collection<ProgramPoint> errorLocs, final InterpolationTechnique interpolation,
			final boolean computeHoareAnnotation, final IUltimateServiceProvider services,
			final IToolchainStorage storage) {
		super(name, rootNode, smtManager, taPrefs, errorLocs, interpolation, computeHoareAnnotation, services, storage);
		mErrorPathHistory = new ArrayList<String>();
		mnofStates = new ArrayList<Integer>();
	}

	/**
	 * constructs the interpolant automaton.
	 * 
	 * @throws AutomataOperationCanceledException
	 */
	@Override
	protected void constructInterpolantAutomaton() throws AutomataOperationCanceledException {
		mLogger.debug("Start constructing interpolant automaton.");

		mnofAdditionalPaths = 0;
		mnofDeclinedPaths = 0;

		// cast the abstraction automaton as nested word and double decker
		// automaton
		mNestedAbstraction = (INestedWordAutomaton<CodeBlock, IPredicate>) mAbstraction;

		mDoubleDeckerAbstraction = (new RemoveUnreachable<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
				(INestedWordAutomatonSimple<CodeBlock, IPredicate>) mAbstraction)).getResult();
		// (IDoubleDeckerAutomaton<CodeBlock, IPredicate>) mAbstraction.get;

		// cast the path as nested run
		mCounterExamplePath = (NestedRun<CodeBlock, IPredicate>) mCounterexample;

		// create an new interpolant automaton
		mInterpolAutomaton = new NestedWordAutomaton<CodeBlock, IPredicate>(new AutomataLibraryServices(mServices),
				mNestedAbstraction.getAlphabet(), mNestedAbstraction.getCallAlphabet(),
				mNestedAbstraction.getReturnAlphabet(), mNestedAbstraction.getStateFactory());

		// remember some of its properties
		mAbstractionInitialState = mInterpolantGenerator.getPrecondition();
		mAbstractionFinalState = mInterpolantGenerator.getPostcondition();
		mPredicateUnifier = mInterpolantGenerator.getPredicateUnifier();
		mEpimorphism = new AutomatonEpimorphism<>(new AutomataLibraryServices(mServices));

		// // / debugging
		// {
		// String h = "";
		// for (int i = 0; i < mCounterExamplePath.getLength() - 1; i++)
		// {
		// h = h + "<[" + mCounterExamplePath.getStateAtPosition(i) + "]>"
		// + "--{" + mCounterExamplePath.getSymbol(i).toString() + "}-->";
		// }
		// h = h
		// + "["
		// + mCounterExamplePath.getStateAtPosition(mCounterExamplePath
		// .getLength() - 1) + "]";
		// mErrorPathHistory.add(h);
		// }

		// hold an iterable list of all states we added to the new automaton
		mAnnotatedStates = new ArrayList<IPredicate>();

		// counter example components
		final ArrayList<IPredicate> ce_states = mCounterExamplePath.getStateSequence();
		final NestedWord<CodeBlock> ce_edges = mCounterExamplePath.getWord();
		final IPredicate[] ce_interp = mInterpolantGenerator.getInterpolants();

		// -- initialize interpolant automaton --
		// Add the initial state of the error path
		mLogger.debug("Add the initial state of the error path");
		mAnnotatedStates.add(ce_states.get(0));
		mInterpolAutomaton.addState(true, mAbstractionInitialState == mAbstractionFinalState, mAbstractionInitialState);
		mEpimorphism.insert(ce_states.get(0), mAbstractionInitialState);

		// Add the final state of the error path
		mLogger.debug("Add the final state of the error path");
		if (mAnnotatedStates.contains(ce_states.get(ce_states.size() - 1))) {
			throw new Error();
		}
		mAnnotatedStates.add(ce_states.get(ce_states.size() - 1));
		if (!mInterpolAutomaton.getStates().contains(mAbstractionFinalState)) {
			mInterpolAutomaton.addState(mAbstractionInitialState == mAbstractionFinalState, true,
					mAbstractionFinalState);
		}
		mEpimorphism.insert(ce_states.get(ce_states.size() - 1), mAbstractionFinalState);

		// Add internal states of the error path
		mLogger.debug("Add internal states and edges of the error path");
		addPath(ce_edges, ce_states, ce_interp, mAbstractionInitialState, mAbstractionFinalState,
				new TreeMap<Integer, IPredicate>());

		// // // debugging
		// {
		// s_Logger.debug("States in the one-error-path-automaton:");
		// for (int i = 0; i < mAnnotatedStates.size(); i++)
		// {
		// s_Logger.debug(i + ": " + mAnnotatedStates.get(i));
		// }
		// }

		// -- Try to add additional paths --
		mLogger.debug("--- Try to add additional paths ---");
		// go through each state in the list of states as
		// starting point and find a path to any other annotated state
		// mAddedStates will grow
		for (int i = 0; i < mAnnotatedStates.size(); i++) {
			mActualStartingState = mAnnotatedStates.get(i);

			mLogger.debug("Start with: " + mActualStartingState.toString());

			mActualPrecondition = mEpimorphism.getMapping(mActualStartingState);

			// return transitions
			for (final IPredicate hier : mDoubleDeckerAbstraction.getDownStates(mActualStartingState)) {
				// if we did not annotate the hierarchical predecessor we cannot
				// test
				// the path yet
				// so we just do not
				if (mAnnotatedStates.contains(hier)) {
					for (final OutgoingReturnTransition<CodeBlock, IPredicate> e : mNestedAbstraction
							.returnSuccessorsGivenHier(mActualStartingState, hier)) {
						// the next state is the target state of the edge
						final IPredicate target = e.getSucc();
						exploreInitialEdge(e, target,
								new NestedWord<CodeBlock>(e.getLetter(), NestedWord.MINUS_INFINITY));
					}
				}
			}

			// calls transitions
			for (final OutgoingCallTransition<CodeBlock, IPredicate> e : mNestedAbstraction
					.callSuccessors(mActualStartingState)) {
				// the next state is the target state of the edge
				final IPredicate target = e.getSucc();
				exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.PLUS_INFINITY));
			}

			// start the depth first search procedure for every state edge going
			// out
			// from the
			// actual starting state, ignoring if a path was find or not (i.e.
			// the
			// return value of exploreState)
			for (final OutgoingInternalTransition<CodeBlock, IPredicate> e : mNestedAbstraction
					.internalSuccessors(mActualStartingState)) {
				// the next state is the target state of the edge
				final IPredicate target = e.getSucc();

				exploreInitialEdge(e, target, new NestedWord<CodeBlock>(e.getLetter(), NestedWord.INTERNAL_POSITION));
			}
		}

		mLogger.info("Explored paths: " + (mnofDeclinedPaths + mnofAdditionalPaths));
		mLogger.info("Added paths   : " + mnofAdditionalPaths);
		mLogger.info("Declined paths: " + mnofDeclinedPaths);
		mLogger.debug("Epimorphism:");
		mEpimorphism.print();

		assert (new InductivityCheck(mServices,
				mInterpolAutomaton, false, true, new IncrementalHoareTripleChecker(
						mRootNode.getRootAnnot().getManagedScript(), mModGlobVarManager)))
								.getResult() : "Not inductive";

		mnofStates.add(mAbstraction.size());
		int ii = 0;
		for (final Integer i : mnofStates) {
			mLogger.debug(ii++ + ":" + i);
		}
	}

	/**
	 * Explore the first edge. If we can already reach an annotated state we must check if the edge is already in one of
	 * the added paths.
	 * 
	 * @param e
	 *            The edge to be taken (firstly)
	 * @param target
	 *            The target of the edge
	 * @param initialWord
	 *            Word consisting of the label of the edge
	 */
	private void exploreInitialEdge(final ITransitionlet<CodeBlock, IPredicate> e, final IPredicate target,
			final NestedWord<CodeBlock> initialWord) {
		mActualPath = new ArrayList<IPredicate>(16);
		// remember the path, we follow
		mActualPath.add(mActualStartingState);
		mActualPath.add(target);

		mLogger.debug("Explore primary edge: " + e.toString() + " wordLen: " + initialWord.length() + " pathLen: "
				+ mActualPath.size());

		// check if the edge points to an already annotated state
		// if the target state is already added, we completed a path ...
		if (mAnnotatedStates.contains(target)) {
			mLogger.debug("Found an annotated state.");
			// check if this is an edge which is already in the automaton
			if (!mInterpolAutomaton.succInternal(mEpimorphism.getMapping(mActualStartingState), e.getLetter())
					.contains(mEpimorphism.getMapping(target))) {
				// we have either a self-loop or another separate edge
				checkAndAddPath(initialWord, mActualPrecondition, mEpimorphism.getMapping(target));
			}
		} else {
			exploreState(target, initialWord);
		}
	}

	// Variable stacks to emulate recursion
	private ArrayList<IPredicate> mStackState;
	private ArrayList<Integer> mStackEdgeType;
	private ArrayList<Iterator<ITransitionlet<CodeBlock, IPredicate>>> mStackIterator;
	private ArrayList<Iterator<IPredicate>> mStackHier;
	private ArrayList<NestedWord<CodeBlock>> mStackWord;

	/**
	 * Explores all edges of a node. If it completes a path feed out: - If the path was accepted by the interpolant
	 * generator add the states to the new interpolant automaton - If the path was not accepted just go back and try
	 * other paths.
	 * 
	 * @param state
	 *            Actual state of the algorithm, initially: starting state
	 * @param word
	 *            Labels of the edges of the actual path
	 * @param actualPath
	 *            List of the states of the actual path
	 */
	@SuppressWarnings("unchecked")
	private void exploreState(final IPredicate state, final NestedWord<CodeBlock> word) {
		mLogger.debug(
				"Explore path: " + state.toString() + " wordLen: " + word.length() + " pathLen: " + mActualPath.size());
		mStackState = new ArrayList<IPredicate>();
		mStackIterator = new ArrayList<Iterator<ITransitionlet<CodeBlock, IPredicate>>>();
		mStackEdgeType = new ArrayList<Integer>();
		mStackHier = new ArrayList<Iterator<IPredicate>>();
		mStackWord = new ArrayList<NestedWord<CodeBlock>>();

		// determins if we found a path, then we back off
		IPredicate s = state;
		// hierarchical predecessors
		Iterator<IPredicate> hierPreds = null;
		@SuppressWarnings("rawtypes")
		Iterator iter = mNestedAbstraction.internalSuccessors(s).iterator();
		Integer edgeType = 0;
		NestedWord<CodeBlock> actualWord = word;

		while (true) {
			mLogger.debug("iterate: " + s.toString() + " wordLen: " + actualWord.length() + " pathLen: "
					+ mActualPath.size());

			// check if there is another undiscovered edge
			if (!iter.hasNext()) {
				edgeType++;
				switch (edgeType) {
				case 1:
					if (hierPreds == null) {
						// if we have not looked at the hierarchical
						// predecessors yet
						hierPreds = mDoubleDeckerAbstraction.getDownStates(s).iterator();
					}
					if (hierPreds.hasNext()) {
						final IPredicate hier = hierPreds.next();
						if (mAnnotatedStates.contains(hier)) {
							mLogger.debug("iterate through hier" + hier.toString());
							iter = mNestedAbstraction.returnSuccessorsGivenHier(s, hier).iterator();
							edgeType = 0; // there might still be hierPreds left
						} else {
							continue;
						}
					} else {
						// if we gone through all hierPreds we set to null for
						// the next
						// iteration
						hierPreds = null;
						continue;
					}
				case 2:
					iter = mNestedAbstraction.callSuccessors(s).iterator();
					continue;
				case 3:
					// go back
					final int index = mStackState.size() - 1;
					if (index < 0) {
						// no state to go back, we explored everything
						return;
					}
					s = mStackState.get(index);
					hierPreds = mStackHier.get(index);
					iter = mStackIterator.get(index);
					edgeType = mStackEdgeType.get(index);
					actualWord = mStackWord.get(index);
					mStackState.remove(index);
					mStackHier.remove(index);
					mStackIterator.remove(index);
					mStackEdgeType.remove(index);
					mStackWord.remove(index);
					// remove the last element, since it did not "work"
					mActualPath.remove(mActualPath.size() - 1);
					continue;
				}
			}

			// obtain the next edge
			// and add the letter to the path and explore edge
			IPredicate target;
			NestedWord<CodeBlock> newWord;
			switch (edgeType) {
			case 0:
				final OutgoingInternalTransition<CodeBlock, IPredicate> e_int =
						(OutgoingInternalTransition<CodeBlock, IPredicate>) iter.next();
				target = e_int.getSucc();
				newWord = actualWord
						.concatenate(new NestedWord<CodeBlock>(e_int.getLetter(), NestedWord.INTERNAL_POSITION));
				break;
			case 1:
				final OutgoingReturnTransition<CodeBlock, IPredicate> e_out =
						(OutgoingReturnTransition<CodeBlock, IPredicate>) iter.next();
				target = e_out.getSucc();
				newWord =
						actualWord.concatenate(new NestedWord<CodeBlock>(e_out.getLetter(), NestedWord.MINUS_INFINITY));
				break;
			case 2:
				final OutgoingCallTransition<CodeBlock, IPredicate> e_ret =
						(OutgoingCallTransition<CodeBlock, IPredicate>) iter.next();
				target = e_ret.getSucc();
				newWord =
						actualWord.concatenate(new NestedWord<CodeBlock>(e_ret.getLetter(), NestedWord.PLUS_INFINITY));
				break;
			default:
				throw new Error();
			}

			// Check if we have already been here.
			// This prevents the addition of path-internal loops.
			// Do not check with the actual state, so self-loops are OK.
			boolean ignoreEdge = false;
			for (int i = 0; i < mActualPath.size() - 1; i++) {
				if (s == mActualPath.get(i)) {
					ignoreEdge = true;
					break;
				}
			}
			if (ignoreEdge) {
				continue;
			}

			// Try to add the target state of the edge (temporarily).
			// Do not forget to remove it, when exiting loop and not exiting
			// explorePath(...)!
			mActualPath.add(target);

			// if the target state is already added, we completed a path ...
			if (mAnnotatedStates.contains(target)) {
				mLogger.debug("Found an annotated state");
				final IPredicate pre = mEpimorphism.getMapping(mActualStartingState);
				final IPredicate post = mEpimorphism.getMapping(target);

				if (checkAndAddPath(newWord, pre, post)) {
					// If we found a path, we can stop the search here, we will
					// return soon, bc the actual state was added in
					// mannotatedStates
					return;
				}

				// remove the last element, since it did not "work"
				mActualPath.remove(mActualPath.size() - 1);
			} else {
				// if not reached a state on the path, go further
				// save actual state on the stack
				mStackState.add(s);
				mStackHier.add(hierPreds);
				mStackIterator.add(iter);
				mStackEdgeType.add(edgeType);
				mStackWord.add(actualWord);
				s = target;
				iter = mNestedAbstraction.internalSuccessors(target).iterator();
				edgeType = 0;
				actualWord = newWord;
			}
		}
	}

	/**
	 * Check if the actual path is feasible to add into the interpolant automaton and return true if it was possible.
	 * 
	 * @param word
	 *            the edges along the path
	 * @param pre
	 *            the precondition of the path
	 * @param post
	 *            the postcondition of the path
	 * @return true if interpolants were found
	 */
	private boolean checkAndAddPath(final NestedWord<CodeBlock> word, final IPredicate pre, final IPredicate post) {
		mLogger.debug("Try to add trace: " + pre.toString() + " -- " + word + " --> " + post);

		final SortedMap<Integer, IPredicate> pendingContexts = new TreeMap<Integer, IPredicate>();
		for (final Entry<Integer, CodeBlock> e : word.getPendingReturns().entrySet()) {
			final int pos = e.getKey();
			final IPredicate target = mActualPath.get(pos + 1);
			final IPredicate source = mActualPath.get(pos);
			for (final IncomingReturnTransition<CodeBlock, IPredicate> irt : mNestedAbstraction
					.returnPredecessors(target, word.getSymbolAt(pos))) {
				if (irt.getLinPred() == source) {
					final IPredicate interp = mEpimorphism.getMapping(irt.getHierPred());
					// assert (interp != null);
					if (interp == null) {
						return false;
					}
					// interp = irt.getHierPred();
					pendingContexts.put(pos, interp);
				}
			}
		}
		// test if we found a new path which can be added
		final InterpolatingTraceCheckerCraig traceChecker = new InterpolatingTraceCheckerCraig(pre, post,
				pendingContexts, word, mSmtManager, mRootNode.getRootAnnot().getModGlobVarManager(),
				/*
				 * TODO: When Matthias introduced this parameter he set the argument to
				 * AssertCodeBlockOrder.NOT_INCREMENTALLY. Check if you want to set this to another value.
				 */AssertCodeBlockOrder.NOT_INCREMENTALLY, mServices, false, mPredicateUnifier, mPref.interpolation(),
				true, mXnfConversionTechnique, mSimplificationTechnique);

		mInterpolantGenerator = traceChecker;
		if (traceChecker.isCorrect() == LBool.UNSAT) {
			mLogger.debug("Accepted");
			addPath(word, mActualPath, traceChecker.getInterpolants(), pre, post, pendingContexts);
			mnofAdditionalPaths++;
			return true;
		}
		// else if (mTraceChecker.isCorrect() == LBool.SAT)
		// {
		// }
		else {
			mLogger.debug("Declined");
			mnofDeclinedPaths++;
			return false;
		}
	}

	/**
	 * Adds the path given from the trace checker. Assumes that the first and last state is already added. Adds edges
	 * states and interpolants
	 * 
	 * sorry, but eclipses auto format always messes up the following "graph", meh... s0
	 * 
	 * <pre>
	 * e0 s1 I0 e1 s2 I1 e2 s3 <post>
	 * 
	 * @param edges
	 *            Contains the edges along the path
	 * @param states
	 *            Holds all states (0, ..., n-1)
	 * @param interpolants
	 *            The interpolants along the path for the states 1, ..., n-2
	 * @param pre
	 *            the formula for the state 0
	 * @param post
	 *            the formula for the state n-1
	 */
	private void addPath(final NestedWord<CodeBlock> edges, final ArrayList<IPredicate> states,
			final IPredicate[] interpolants, final IPredicate pre, final IPredicate post,
			final SortedMap<Integer, IPredicate> pendingContexts) {
		mLogger.debug("Add path: numEdges:" + edges.length() + " numStates:" + states.size() + " numInterpol:"
				+ interpolants.length);

		mLogger.debug("edges:");
		for (int i = 0; i < edges.length(); i++) {
			mLogger.debug("<" + edges.getSymbol(i).toString() + ">");
		}
		mLogger.debug("states:");
		for (int i = 0; i < states.size(); i++) {
			mLogger.debug("<" + states.get(i).toString() + ">");
		}
		mLogger.debug("interp:");
		for (int i = 0; i < interpolants.length; i++) {
			mLogger.debug("<" + interpolants[i].toString() + ">");
		}

		final ArrayList<IPredicate> callPredecessors = new ArrayList<IPredicate>();

		// Add all edges
		for (int i = 0; i < edges.length(); i++) {
			final CodeBlock e = edges.getSymbolAt(i);
			final IPredicate targetS = states.get(i + 1);

			final IPredicate sourceI = (i == 0) ? pre : interpolants[i - 1];
			final IPredicate targetI = (i == edges.length() - 1) ? post : interpolants[i];

			// Add all states in the sequence, but the first and last.
			if (i < edges.length() - 1) {
				// targetS can(may) not be in mAddedStates
				mAnnotatedStates.add(targetS);
				// since the interpolant formula might not be unique
				if (!mInterpolAutomaton.getStates().contains(targetI)) {
					mInterpolAutomaton.addState(targetI == mAbstractionInitialState, targetI == mAbstractionFinalState,
							targetI);
				}
				mEpimorphism.insert(targetS, targetI);
			}

			// add the respective edge into the abstraction automaton
			if (edges.isInternalPosition(i)) {
				boolean exists = false;
				for (final OutgoingInternalTransition<CodeBlock, IPredicate> t : mInterpolAutomaton
						.internalSuccessors(sourceI, e)) {
					if (t.getSucc().equals(targetI)) {
						exists = true;
					}
					break;
				}
				if (!exists) {
					mInterpolAutomaton.addInternalTransition(sourceI, e, targetI);
				}
			} else {
				if (edges.isCallPosition(i)) {
					// pendingContexts.put(arg0, arg1)
					callPredecessors.add(sourceI);
					mInterpolAutomaton.addCallTransition(sourceI, e, targetI);
				} else // isReturnPosition(i)
				{
					IPredicate hier;
					if (callPredecessors.size() <= 0) {
						hier = pendingContexts.get(i);
					} else {
						final int lastIndex = callPredecessors.size() - 1;
						hier = callPredecessors.get(lastIndex);
						callPredecessors.remove(lastIndex);
					}
					mLogger.debug("hier is: " + hier);
					mInterpolAutomaton.addReturnTransition(sourceI, hier, e, targetI);
				}
			}
		}
	}

	/**
	 * Construct the new program abstraction by subtraction the interpolant automaton from the abstraction
	 * 
	 * @return true if the trace of mCounterexample (which was accepted by the old mAbstraction) is not accepted by the
	 *         mAbstraction.
	 * @throws AutomataLibraryException
	 */
	@Override
	protected boolean refineAbstraction() throws AutomataLibraryException {
		final SuperDifference<CodeBlock, IPredicate> diff = new SuperDifference<CodeBlock, IPredicate>(
				new AutomataLibraryServices(mServices), mNestedAbstraction, mInterpolAutomaton, mEpimorphism, false);

		mAbstraction = diff.getResult();

		// assert(!accepts(diff.getResult(), mCounterexample.getWord()));

		mLogger.debug("Actualized abstraction.");

		// s_Logger.debug("ERROR_PATH_HISTORY");
		// for (int i = 0; i < mErrorPathHistory.size(); i++) {
		// s_Logger.debug("[" + i + "]: " + mErrorPathHistory.get(i));
		// }

		mCegarLoopBenchmark.reportAbstractionSize(mAbstraction.size(), mIteration);

		mLogger.info("Abstraction has " + mNestedAbstraction.sizeInformation());
		mLogger.info("Interpolant automaton has " + mInterpolAutomaton.sizeInformation());

		final Minimization minimization = mPref.minimize();
		switch (minimization) {
		case NONE:
			break;
		case MINIMIZE_SEVPA:
		case SHRINK_NWA:
			// s_Logger.debug("Minimizing interpolant automaton.");

			// RemoveUnreachable<CodeBlock, IPredicate> removeUnreachable = new
			// RemoveUnreachable<CodeBlock, IPredicate>(
			// (INestedWordAutomatonSimple<CodeBlock, IPredicate>)
			// mAbstraction);
			// // mAbstraction = removeUnreachable.getResult();
			//
			// // RemoveDeadEnds<CodeBlock, IPredicate> removeDeadEnds = new
			// // RemoveDeadEnds<CodeBlock, IPredicate>(
			// // (INestedWordAutomatonOldApi<CodeBlock, IPredicate>)
			// // mAbstraction);
			// // mAbstraction = removeDeadEnds.getResult();
			//
			// // minimizeAbstraction(mStateFactoryForRefinement,
			// // mPredicateFactoryResultChecking, minimization);
			break;
		default:
			throw new AssertionError();
		}

		return true;
	}
}
