package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.builders;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Boogie2SMT;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplicationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.XnfConversionTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Call;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.Return;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.predicates.SmtManager;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singleTraceCheck.PredicateUnifier;

public class AbsIntNonSmtInterpolantAutomatonBuilder implements IInterpolantAutomatonBuilder<CodeBlock, IPredicate> {

	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final NestedWordAutomaton<CodeBlock, IPredicate> mResult;
	private final IRun<CodeBlock, IPredicate> mCurrentCounterExample;
	private final PredicateFactory mPredicateFactory;
	private final Boogie2SMT mBoogie2Smt;

	public AbsIntNonSmtInterpolantAutomatonBuilder(final IUltimateServiceProvider services,
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction, final PredicateUnifier predUnifier,
			final SmtManager smtManager, final IRun<CodeBlock, IPredicate> currentCounterexample,
			final SimplicationTechnique simplificationTechnique, final XnfConversionTechnique xnfConversionTechnique) {
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		mCurrentCounterExample = currentCounterexample;
		mBoogie2Smt = smtManager.getBoogie2Smt();
		mPredicateFactory =
				new PredicateFactory(services, mBoogie2Smt, simplificationTechnique, xnfConversionTechnique);

		mResult = getPathProgramAutomaton(oldAbstraction, predUnifier);
	}

	@Override
	public NestedWordAutomaton<CodeBlock, IPredicate> getResult() {
		return mResult;
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getPathProgramAutomaton(
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction, final PredicateUnifier predicateUnifier) {
		return getPathProgramAutomatonNew(oldAbstraction, predicateUnifier);
		// return getPathProgramAutomatonOld(oldAbstraction, predicateUnifier);
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getPathProgramAutomatonOld(
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction, final PredicateUnifier predicateUnifier) {

		mLogger.info("Creating interpolant automaton from AI using only explored space.");

		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
				oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());
		IPredicate currentState = predicateUnifier.getTruePredicate();
		result.addState(true, false, currentState);

		final IPredicate falsePred = predicateUnifier.getFalsePredicate();

		// TODO: is it correct to go to length - 1 here? I assume that the last state is the error location and we don't
		// want anything to to with that as we are introducing this location in the end.
		for (int cexI = 0; cexI < mCurrentCounterExample.getLength() - 1; cexI++) {
			final IPredicate prevState = currentState;

			// Add state
			currentState = mPredicateFactory.newPredicate(mBoogie2Smt.getScript().term("true"));
			result.addState(false, false, currentState);

			// Add transition
			final CodeBlock currentSymbol = mCurrentCounterExample.getSymbol(cexI);
			if (currentSymbol instanceof Call) {
				result.addCallTransition(prevState, currentSymbol, currentState);
			} else if (currentSymbol instanceof Return) {
				final IPredicate heirState = mPredicateFactory.newPredicate(mBoogie2Smt.getScript().term("true"));
				result.addState(false, false, heirState);
				result.addReturnTransition(prevState, heirState, currentSymbol, currentState);
			} else {
				result.addInternalTransition(prevState, currentSymbol, currentState);
			}
		}

		// Add final state
		if (result.getFinalStates().isEmpty()) {
			final Word<CodeBlock> word = mCurrentCounterExample.getWord();
			final IPredicate finalState = predicateUnifier.getFalsePredicate();
			result.addState(false, true, finalState);
			// HERE GOES SOMETHING WRONG! length is strangely enough not equal to the counter example length?!
			result.addInternalTransition(currentState, word.getSymbol(word.length() - 1), finalState);
			// Add self-loop to the final state, annotated with the alphabet of the counterexample.
			oldAbstraction.getAlphabet().forEach(l -> result.addInternalTransition(finalState, l, finalState));
		}

		if (mLogger.isDebugEnabled()) {
			mLogger.debug("Resulting abstract interpretation automaton: " + result);
		}

		// TODO remove next line; debugging only!
		mLogger.info("Current abstraction: " + oldAbstraction);
		mLogger.info("AI interpolation automaton: " + result);

		return result;
	}

	private NestedWordAutomaton<CodeBlock, IPredicate> getPathProgramAutomatonNew(
			final INestedWordAutomaton<CodeBlock, IPredicate> oldAbstraction, final PredicateUnifier predicateUnifier) {
		mLogger.info("Creating interpolant automaton from AI using only explored space.");

		final NestedWordAutomaton<CodeBlock, IPredicate> result = new NestedWordAutomaton<>(
				new AutomataLibraryServices(mServices), oldAbstraction.getInternalAlphabet(),
				oldAbstraction.getCallAlphabet(), oldAbstraction.getReturnAlphabet(), oldAbstraction.getStateFactory());

		final NestedRun<CodeBlock, IPredicate> cex = (NestedRun<CodeBlock, IPredicate>) mCurrentCounterExample;
		final ArrayList<IPredicate> stateSequence = cex.getStateSequence();

		if (stateSequence.size() <= 1) {
			throw new AssertionError("Unexpected");
		}

		final Map<IPredicate, IPredicate> newStates = new HashMap<>();
		final Map<Call, IPredicate> callHierPreds = new HashMap<>();
		final Word<CodeBlock> word = cex.getWord();
		int i = 0;
		for (final CodeBlock symbol : word) {
			final IPredicate prevState = stateSequence.get(i);
			final IPredicate succState = stateSequence.get(i + 1);
			++i;

			IPredicate newPrevState = newStates.get(prevState);
			if (newPrevState == null) {
				newPrevState = mPredicateFactory.newPredicate(mBoogie2Smt.getScript().term("true"));
				newStates.put(prevState, newPrevState);
				if (i == 1) {
					// the initial state is initial
					result.addState(true, false, newPrevState);
				} else {
					result.addState(false, false, newPrevState);
				}
			}

			IPredicate newSuccState = newStates.get(succState);
			if (newSuccState == null) {
				if (i == stateSequence.size() - 1) {
					// the last state is always an error state
					newSuccState = predicateUnifier.getFalsePredicate();
					result.addState(false, true, newSuccState);
				} else {
					newSuccState = mPredicateFactory.newPredicate(mBoogie2Smt.getScript().term("true"));
					result.addState(false, false, newSuccState);
				}
				newStates.put(succState, newSuccState);
			}

			// Add transition
			if (symbol instanceof Call) {
				callHierPreds.put((Call) symbol, newPrevState);
				result.addCallTransition(newPrevState, symbol, newSuccState);
			} else if (symbol instanceof Return) {
				final Return returnSymbol = (Return) symbol;
				final IPredicate hierState = callHierPreds.get(returnSymbol.getCorrespondingCall());
				assert hierState != null : "Call has to be seen before return";
				result.addReturnTransition(newPrevState, hierState, symbol, newSuccState);
			} else {
				result.addInternalTransition(newPrevState, symbol, newSuccState);
			}
		}

		// Add self-loops to final state
		if (!result.getFinalStates().isEmpty()) {
			for (final IPredicate finalState : result.getFinalStates()) {
				oldAbstraction.getAlphabet().forEach(l -> result.addInternalTransition(finalState, l, finalState));
			}
		}

		return result;
	}

}