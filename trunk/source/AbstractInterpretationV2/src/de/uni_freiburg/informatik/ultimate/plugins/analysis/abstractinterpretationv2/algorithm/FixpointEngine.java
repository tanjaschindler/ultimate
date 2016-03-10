/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.model.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;
import de.uni_freiburg.informatik.ultimate.util.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class FixpointEngine<STATE extends IAbstractState<STATE, ACTION, VARDECL>, ACTION, VARDECL, LOCATION> {

	private final int mMaxUnwindings;
	private final int mMaxParallelStates;

	private final ITransitionProvider<ACTION, LOCATION> mTransitionProvider;
	private final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> mStateStorage;
	private final IAbstractDomain<STATE, ACTION, VARDECL> mDomain;
	private final IVariableProvider<STATE, ACTION, VARDECL, LOCATION> mVarProvider;
	private final ILoopDetector<ACTION> mLoopDetector;
	private final IDebugHelper<STATE, ACTION, VARDECL, LOCATION> mDebugHelper;
	private final IProgressAwareTimer mTimer;
	private final Logger mLogger;

	private AbstractInterpretationBenchmark<ACTION, LOCATION> mBenchmark;
	private AbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> mResult;

	public FixpointEngine(final IUltimateServiceProvider services, final IProgressAwareTimer timer,
			final FixpointEngineParameters<STATE, ACTION, VARDECL, LOCATION> params) {
		assert timer != null;
		assert services != null;
		assert params != null;

		mTimer = timer;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mTransitionProvider = params.getTransitionProvider();
		mStateStorage = params.getStorage();
		mDomain = params.getAbstractDomain();
		mVarProvider = params.getVariableProvider();
		mLoopDetector = params.getLoopDetector();
		mDebugHelper = params.getDebugHelper();

		final UltimatePreferenceStore ups = new UltimatePreferenceStore(Activator.PLUGIN_ID);
		mMaxUnwindings = ups.getInt(AbsIntPrefInitializer.LABEL_ITERATIONS_UNTIL_WIDENING);
		mMaxParallelStates = ups.getInt(AbsIntPrefInitializer.LABEL_STATES_UNTIL_MERGE);
	}

	public AbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> run(final ACTION start, final Script script,
			final Boogie2SMT bpl2smt,
			final AbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> intermediateResult) {
		mLogger.info("Starting fixpoint engine");
		mResult = (intermediateResult == null ? new AbstractInterpretationResult<>() : intermediateResult);
		mBenchmark = mResult.getBenchmark();
		calculateFixpoint(start);
		mResult.saveTerms(mStateStorage, start, script, bpl2smt);
		return mResult;
	}

	public AbstractInterpretationResult<STATE, ACTION, VARDECL, LOCATION> run(final ACTION start, final Script script,
			final Boogie2SMT bpl2smt) {
		return run(start, script, bpl2smt, new AbstractInterpretationResult<>());
	}

	private void calculateFixpoint(final ACTION start) {
		final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist = new ArrayDeque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>>();
		final IAbstractPostOperator<STATE, ACTION, VARDECL> post = mDomain.getPostOperator();
		final IAbstractStateBinaryOperator<STATE> wideningOp = mDomain.getWideningOperator();
		final IAbstractStateBinaryOperator<STATE> mergeOperator = mDomain.getMergeOperator();
		final Set<ACTION> reachedErrors = new HashSet<>();

		worklist.add(createInitialWorklistItem(start));

		while (!worklist.isEmpty()) {
			checkTimeout();

			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem = worklist.removeFirst();
			final STATE preState = currentItem.getPreState();
			final ACTION currentAction = currentItem.getAction();
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStateStorage = currentItem
					.getCurrentStorage();

			mBenchmark.addIteration(currentItem);

			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageCurrentTransition(preState, currentAction, currentItem.getCallStackDepth()));
			}

			// calculate the (abstract) effect of the current action by first
			// declaring variables in the prestate, and then calculating their
			// values
			final STATE preStateWithFreshVariables = mVarProvider.defineVariablesAfter(currentAction, preState,
					currentStateStorage);

			List<STATE> postStates;
			if (preState == preStateWithFreshVariables) {
				postStates = post.apply(preStateWithFreshVariables, currentAction);
			} else {
				// a context switch happened
				postStates = post.apply(preState, preStateWithFreshVariables, currentAction);
			}

			assert mDebugHelper.isPostSound(preStateWithFreshVariables, postStates,
					currentAction) : getLogMessageUnsoundPost(preStateWithFreshVariables, postStates, currentAction);

			if (postStates.isEmpty()) {
				// if there are no post states, we interpret this as bottom
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(getLogMessageEmptyIsBottom());
				}
				continue;
			}

			if (postStates.size() > mMaxParallelStates) {
				mLogger.warn("Domain produced too many abstract states during post: " + mMaxParallelStates
						+ " allowed, " + postStates.size() + " received.");
				postStates = Collections
						.singletonList(postStates.stream().reduce((a, b) -> mergeOperator.apply(a, b)).get());
			}

			for (STATE pendingNewPostState : postStates) {
				if (pendingNewPostState.isBottom()) {
					// if the new abstract state is bottom, we do not enter loops and we do not add
					// new actions to the worklist
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(getLogMessagePostIsBottom(pendingNewPostState));
					}
					continue;
				}

				if (mLoopDetector.isEnteringLoop(currentAction)) {
					// we are entering a loop
					loopEnter(currentItem);
				}

				// check if we should widen after entering a new scope
				if (mTransitionProvider.isEnteringScope(currentAction)) {
					pendingNewPostState = widenAtScopeEntry(currentItem, wideningOp, pendingNewPostState);
					// check if the resulting state is a fixpoint
					if (checkFixpointAtScopeEntry(currentItem, pendingNewPostState)) {
						// TODO: Add the summary successor here
						continue;
					}
				}

				final STATE newPostState = pendingNewPostState;

				if (currentItem.hasActiveLoop()) {
					// are we leaving a loop?
					final LOCATION currentLoopHead = mTransitionProvider.getTarget(currentAction);
					if (currentItem.isActiveLoopHead(currentLoopHead)) {
						// we are leaving a loop
						loopLeave(currentItem);
					}
				}

				// check if the current state is a fixpoint
				if (checkFixpoint(currentStateStorage, currentAction, newPostState)) {
					continue;
				}

				if (mLogger.isDebugEnabled()) {
					mLogger.debug(getLogMessageNewPostState(newPostState));
				}
				// add post state to this location
				currentStateStorage.addAbstractPostState(currentAction, newPostState);

				if (mTransitionProvider.isPostErrorLocation(currentAction, currentItem.getCurrentScope())
						&& !newPostState.isBottom() && reachedErrors.add(currentAction)) {
					if (mLogger.isDebugEnabled()) {
						mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT)
								.append(" Error state reached"));
					}
					mResult.reachedError(mTransitionProvider, currentItem, newPostState);
				}

				// now add successors
				addSuccessors(worklist, currentItem, wideningOp);
			}
		}
	}

	private void loopLeave(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem) {
		final int loopCounterValue = currentItem.leaveCurrentLoop();
		if (mLogger.isDebugEnabled()) {
			final ACTION current = currentItem.getAction();
			final LOCATION loopHead = mTransitionProvider.getTarget(current);
			mLogger.debug(getLogMessageLeaveLoop(loopCounterValue, loopHead));
		}
	}

	private void loopEnter(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem) {
		final LOCATION currentLoopHead = mTransitionProvider.getSource(currentItem.getAction());
		final int loopCounterValue = currentItem.enterLoop(currentLoopHead, currentItem.getPreState());
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageEnterLoop(loopCounterValue, currentLoopHead));
		}
	}

	private WorklistItem<STATE, ACTION, VARDECL, LOCATION> createInitialWorklistItem(final ACTION elem) {
		final WorklistItem<STATE, ACTION, VARDECL, LOCATION> startItem = new WorklistItem<STATE, ACTION, VARDECL, LOCATION>(
				getCurrentAbstractPreState(elem, mStateStorage), elem, mStateStorage);
		if (mTransitionProvider.isEnteringScope(elem)) {
			startItem.addScope(elem);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(
						new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering (initial) scope"));
			}
		}
		return startItem;
	}

	private void addSuccessors(final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist,
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final IAbstractStateBinaryOperator<STATE> widening) {
		final ACTION current = currentItem.getAction();
		final Collection<ACTION> successors = mTransitionProvider.getSuccessors(current, currentItem.getCurrentScope());

		if (successors.isEmpty()) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" No successors"));
			}
			return;
		}

		final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStateStorage = currentItem
				.getCurrentStorage();
		final Collection<STATE> availablePostStates = currentStateStorage.getAbstractPostStates(current);

		// check if we have to merge before adding successors
		if (availablePostStates.size() > mMaxParallelStates) {
			final STATE mergedState = merge(worklist, current, successors, currentStateStorage, availablePostStates);
			availablePostStates.clear();
			availablePostStates.add(mergedState);
		}

		// check if we should widen at this location before adding new successors
		boolean skipLoopEntrySuccessors = false;
		final Pair<Integer, STATE> loopPair = currentItem.getLoopPair(mTransitionProvider.getTarget(current));
		if (loopPair != null && loopPair.getFirst() > mMaxUnwindings) {
			// we should widen with the last state at this loop head
			final STATE oldLoopState = loopPair.getSecond();

			// we have to ensure that there is only one state at this location for widening
			final STATE currentPostState;
			if (availablePostStates.size() > 1) {
				// no, we have to merge
				currentPostState = merge(worklist, current, successors, currentStateStorage, availablePostStates);
			} else if (availablePostStates.size() == 1) {
				currentPostState = availablePostStates.iterator().next();
			} else {
				throw new AssertionError("No post states available for widening");
			}
			// is the current state already a fixpoint?
			skipLoopEntrySuccessors = checkFixpoint(oldLoopState, currentPostState);

			if (!skipLoopEntrySuccessors) {
				// if it is no fixpoint, we really have to widen
				final STATE widenedState = widen(currentStateStorage, widening, current, oldLoopState,
						currentPostState);
				availablePostStates.clear();
				availablePostStates.add(widenedState);

				// check if the widened state is a fixpoint. If it is, we do not need to enter the loop again
				skipLoopEntrySuccessors = checkFixpoint(oldLoopState, widenedState);
			}
		}

		for (final STATE postState : availablePostStates) {
			for (final ACTION successor : successors) {
				if (skipLoopEntrySuccessors && mLoopDetector.isEnteringLoop(successor)) {
					continue;
				}

				final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem = new WorklistItem<STATE, ACTION, VARDECL, LOCATION>(
						postState, successor, currentItem);

				if (mLogger.isDebugEnabled()) {
					mLogger.debug(getLogMessageAddTransition(successorItem));
				}
				scopeEnterOrLeave(currentItem, successor, successorItem);
				worklist.add(successorItem);
			}
		}
	}

	private STATE widen(final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStateStorage,
			final IAbstractStateBinaryOperator<STATE> wideningOp, final ACTION current, final STATE oldPostState,
			final STATE currentPostState) {
		// TODO: Remove all worklist items that will be superseded by this widening operation, i.e. all abstract states
		// from the source of oldPostState
		// TODO: Remove all stored states that are superseded

		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwinding(oldPostState, currentPostState));
		}
		mBenchmark.addWiden();
		final STATE newPostState = currentStateStorage.widenPostState(current, wideningOp, oldPostState);
		assert oldPostState.getVariables().keySet()
				.equals(newPostState.getVariables().keySet()) : "Widening destroyed the state";
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwindingResult(newPostState));
		}
		return newPostState;
	}

	private STATE merge(final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist, final ACTION current,
			final Collection<ACTION> successors,
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStateStorage,
			final Collection<STATE> statesToMerge) {
		mBenchmark.addMerge(statesToMerge.size());
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageMergeStates(statesToMerge.size(), statesToMerge));
		}
		removeMergedStatesFromWorklist(worklist, statesToMerge, successors);
		final STATE newPostState = currentStateStorage.mergePostStates(current);
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageMergeResult(newPostState));
		}
		assert currentStateStorage.getAbstractPostStates(current).size() == 1;
		return newPostState;
	}

	private void removeMergedStatesFromWorklist(final Deque<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> worklist,
			final Collection<STATE> availablePostStates, final Collection<ACTION> successors) {
		final Iterator<WorklistItem<STATE, ACTION, VARDECL, LOCATION>> iter = worklist.iterator();
		final Set<ACTION> successorSet = new HashSet<>(successors);
		while (iter.hasNext()) {
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem = iter.next();
			// note that here the state has to be equal, i.e., the same instance
			if (successorSet.contains(currentItem.getAction())
					&& availablePostStates.contains(currentItem.getPreState())) {
				iter.remove();
				if (mLogger.isDebugEnabled()) {
					mLogger.debug(getLogMessageRemoveFromWorklistDuringMerge(currentItem));
				}
			}
		}
	}

	/**
	 * Check if a new scope has to be opened and if so, add the scope to the successor item.
	 * 
	 * Also checks if there is a fixpoint when entering a recursive function and returns false if no successors should
	 * be added because of this
	 */
	private boolean scopeEnterOrLeave(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final ACTION successor, final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		if (mTransitionProvider.isEnteringScope(successor)) {
			successorItem.addScope(successor);
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageEnterScope(successorItem));
			}
		} else if (mTransitionProvider.isLeavingScope(successor, currentItem.getCurrentScope())) {
			successorItem.removeCurrentScope();
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageLeaveScope(successorItem));
			}
		}
		return true;
	}

	private STATE widenAtScopeEntry(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final IAbstractStateBinaryOperator<STATE> widening, final STATE pendingPostState) {
		final ACTION currentAction = currentItem.getAction();

		// check for fixpoint and/or widening
		final Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> stackAtCallLocation = currentItem
				.getStack();
		// get all stack items in the correct order that contain only calls to the current scope
		final List<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> relevantStackItems = stackAtCallLocation
				.stream().sequential().filter(a -> a.getFirst() == currentAction || a.getFirst() == null)
				.collect(Collectors.toList());
		if (relevantStackItems.isEmpty()) {
			// cannot widen if there is no sequence
			return pendingPostState;
		}

		if (relevantStackItems.size() > mMaxUnwindings) {
			// we have to apply widening to the last state at this location and the new pending post state
			// the relevant stack contains
			final Optional<STATE> lastState = relevantStackItems.stream().sequential()
					.map(a -> a.getSecond().getAbstractPostStates(currentAction)).flatMap(a -> a.stream().sequential())
					.findFirst();
			if (lastState.isPresent()) {
				return widenAtScopeEntry(widening, lastState.get(), pendingPostState);
			}

			final Optional<STATE> lastAllState = stackAtCallLocation.stream().sequential()
					.map(a -> a.getSecond().getAbstractPostStates(currentAction)).flatMap(a -> a.stream().sequential())
					.findFirst();
			if (lastAllState.isPresent()) {
				mLogger.warn(AbsIntPrefInitializer.INDENT + " Widening uses all states");
				return widenAtScopeEntry(widening, lastAllState.get(), pendingPostState);
			}
			mLogger.warn("Could not widen at " + getHashCodeString(currentAction) + currentAction);
		}
		return pendingPostState;
	}

	private STATE widenAtScopeEntry(final IAbstractStateBinaryOperator<STATE> widening, final STATE oldPostState,
			final STATE pendingPostState) {
		// TODO: Do it similar to the "normal" widen
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwinding(oldPostState, pendingPostState));
		}
		mBenchmark.addWiden();
		final STATE newPostState = widening.apply(oldPostState, pendingPostState);
		assert oldPostState.getVariables().keySet()
				.equals(newPostState.getVariables().keySet()) : "Widening destroyed the state";
		if (mLogger.isDebugEnabled()) {
			mLogger.debug(getLogMessageUnwindingResult(newPostState));
		}
		return newPostState;
	}

	private boolean checkFixpoint(final STATE oldState, final STATE newState) {
		if (oldState.isEqualTo(newState)) {
			if (mLogger.isDebugEnabled()) {
				mLogger.debug(getLogMessageFixpointFound(oldState, newState));
			}
			mBenchmark.addFixpoint();
			return true;
		}
		return false;
	}

	private boolean checkFixpoint(final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> currentStorage,
			ACTION currentAction, STATE newPostState) {
		final Collection<STATE> oldPostStates = currentStorage.getAbstractPostStates(currentAction);
		return oldPostStates.stream().anyMatch(old -> checkFixpoint(old, newPostState));
	}

	private boolean checkFixpointAtScopeEntry(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> currentItem,
			final STATE pendingPostState) {
		final ACTION currentAction = currentItem.getAction();

		// get all calls at the current locations
		final Deque<Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>>> stackAtCallLocation = currentItem
				.getStack();

		if (stackAtCallLocation.isEmpty()) {
			// if there are no relevant stack items, there cannot be a fixpoint
			return false;
		}

		for (final Pair<ACTION, IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION>> stackItem : stackAtCallLocation) {
			final IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> stateStorage = stackItem.getSecond();
			if (checkFixpoint(stateStorage, currentAction, pendingPostState)) {
				// it is a fixpoint
				return true;
			}
		}
		return false;
	}

	private STATE getCurrentAbstractPreState(final ACTION current,
			IAbstractStateStorage<STATE, ACTION, VARDECL, LOCATION> stateStorage) {
		STATE preState = stateStorage.getCurrentAbstractPreState(current);
		if (preState == null) {
			preState = mDomain.createFreshState();
			preState = mVarProvider.defineVariablesBefore(current, preState);
			stateStorage.addAbstractPreState(current, preState);
		}
		return preState;
	}

	private void checkTimeout() {
		if (!mTimer.continueProcessing()) {
			mLogger.warn("Received timeout, aborting fixpoint engine");
			throw new ToolchainCanceledException(getClass(), "Got cancel request during abstract interpretation");
		}
	}

	private String getLogMessageUnsoundPost(STATE preStateWithFreshVariables, List<STATE> postStates,
			ACTION currentAction) {
		// TODO Auto-generated method stub
		return "Post is unsound";
	}

	private StringBuilder getLogMessageEmptyIsBottom() {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT)
				.append(" Skipping all successors because there was no post state (i.e., post is bottom)");
	}

	private StringBuilder getLogMessagePostIsBottom(final STATE pendingNewPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT)
				.append(" Skipping all successors because post state [").append(pendingNewPostState.hashCode())
				.append("] is bottom");
	}

	private StringBuilder getLogMessageLeaveScope(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(AbsIntPrefInitializer.INDENT)
				.append(" Successor transition [").append(successorItem.getAction().hashCode())
				.append("] leaves scope (new depth=").append(successorItem.getCallStackDepth()).append(")");
	}

	private StringBuilder getLogMessageEnterScope(final WorklistItem<STATE, ACTION, VARDECL, LOCATION> successorItem) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(AbsIntPrefInitializer.INDENT)
				.append(" Successor transition [").append(successorItem.getAction().hashCode())
				.append("] enters scope (new depth=").append(successorItem.getCallStackDepth()).append(")");
	}

	private StringBuilder getLogMessageFixpointFound(STATE oldPostState, final STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Found fixpoint state [")
				.append(oldPostState.hashCode()).append("] ").append(oldPostState.toLogString())
				.append(" -- replacing with [").append(newPostState.hashCode()).append("]");
	}

	private StringBuilder getLogMessageMergeResult(STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Merging resulted in [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageRemoveFromWorklistDuringMerge(
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> item) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Removing [")
				.append(item.getPreState().hashCode()).append("]").append(" --[").append(item.getAction().hashCode())
				.append("]-> from worklist during merge");
	}

	private StringBuilder getLogMessageMergeStates(final int availablePostStatesCount,
			Collection<STATE> availablePostStates) {
		final List<String> postStates = availablePostStates.stream().map(a -> "[" + String.valueOf(a.hashCode()) + "]")
				.collect(Collectors.toList());
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Merging ")
				.append(availablePostStatesCount).append(" states at target location: ")
				.append(String.join(",", postStates));
	}

	private StringBuilder getLogMessageNewPostState(STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding post state [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageEnterLoop(final int loopCounterValue, final LOCATION loopHead) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Entering loop ").append(loopHead)
				.append(" (").append(loopCounterValue).append(")");
	}

	private StringBuilder getLogMessageLeaveLoop(final int loopCounterValue, final LOCATION loopHead) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Leaving loop ").append(loopHead)
				.append(" (").append(loopCounterValue).append(")");
	}

	private StringBuilder getLogMessageUnwindingResult(STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Widening resulted in post state [")
				.append(newPostState.hashCode()).append("] ").append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageUnwinding(final STATE oldPostState, STATE newPostState) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Widening with old post state [")
				.append(oldPostState.hashCode()).append("] ").append(oldPostState.toLogString())
				.append(" and new post state [").append(newPostState.hashCode()).append("] ")
				.append(newPostState.toLogString());
	}

	private StringBuilder getLogMessageCurrentTransition(final STATE preState, final ACTION current, int depth) {
		final String preStateString = preState == null ? "NULL"
				: addHashCodeString(new StringBuilder(), preState).append(" ").append(preState.toLogString())
						.toString();
		return addHashCodeString(new StringBuilder(), current).append(" ")
				.append(mTransitionProvider.toLogString(current)).append(" processing for pre state ")
				.append(preStateString).append(" (depth=").append(depth).append(")");
	}

	private StringBuilder getLogMessageAddTransition(
			final WorklistItem<STATE, ACTION, VARDECL, LOCATION> newTransition) {
		return new StringBuilder().append(AbsIntPrefInitializer.INDENT).append(" Adding [")
				.append(newTransition.getPreState().hashCode()).append("]").append(" --[")
				.append(newTransition.getAction().hashCode()).append("]->");
	}

	private String getHashCodeString(final Object current) {
		return addHashCodeString(new StringBuilder(), current).toString();
	}

	private StringBuilder addHashCodeString(final StringBuilder builder, final Object current) {
		if (current == null) {
			return builder.append("[?]");
		}
		return builder.append("[").append(current.hashCode()).append("]");
	}
}
