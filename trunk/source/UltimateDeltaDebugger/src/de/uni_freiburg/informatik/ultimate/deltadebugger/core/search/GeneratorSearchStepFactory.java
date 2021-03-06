package de.uni_freiburg.informatik.ultimate.deltadebugger.core.search;

import java.util.List;
import java.util.NoSuchElementException;
import java.util.Optional;

import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IChangeHandle;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.IVariantGenerator;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IDuplicateVariantTracker;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizer;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.search.minimizers.IMinimizerStep;
import de.uni_freiburg.informatik.ultimate.deltadebugger.core.util.ListUtils;

/**
 * Creates a GeneratorSearchStep that uses a given minimizer and duplicate tracker to search for the best set of active
 * changes supported by a VariantGenerator. Also includes the iteration over multiple chained VariantGenerators.
 */
public final class GeneratorSearchStepFactory {
	private final IMinimizer mMinimizer;
	
	private final IDuplicateVariantTrackerFactory mDuplicateTrackerFactory;
	
	/**
	 * Create a factory object that uses the specified minimizer and duplicate tracker.
	 *
	 * @param minimizer
	 *            minimization algorithm
	 * @param duplicateTrackerFactory
	 *            function to create a duplicate tracker for a certain input
	 */
	public GeneratorSearchStepFactory(final IMinimizer minimizer,
			final IDuplicateVariantTrackerFactory duplicateTrackerFactory) {
		mMinimizer = minimizer;
		mDuplicateTrackerFactory = duplicateTrackerFactory;
	}
	
	/**
	 * Factory method to create the initial state for a search over the variants generated by the given generator.
	 *
	 * @param generator
	 *            invariant generator
	 * @return initial search step
	 */
	public IGeneratorSearchStep create(final IVariantGenerator generator) {
		final GeneratorSearchStepContext context = new GeneratorSearchStepContext(generator);
		final IMinimizerStep<IChangeHandle> minimizerStep = mMinimizer.create(generator.getChanges());
		if (!minimizerStep.isDone()) {
			return context.new Step(minimizerStep);
		}
		
		return context.new CompletedStep(minimizerStep, context.complementOf(minimizerStep.getResult()));
	}
	
	/**
	 * Search step context of the generator.
	 */
	private final class GeneratorSearchStepContext {
		private final IVariantGenerator mGenerator;
		private final IDuplicateVariantTracker<IChangeHandle> mDuplicateTracker;
		
		private GeneratorSearchStepContext(final IVariantGenerator generator) {
			mGenerator = generator;
			mDuplicateTracker = mDuplicateTrackerFactory.create(mMinimizer, generator.getChanges());
		}
		
		List<IChangeHandle> complementOf(final List<IChangeHandle> changes) {
			return ListUtils.complementOfSubsequence(changes, mGenerator.getChanges());
		}
		
		/**
		 * A base step.
		 */
		private abstract class BaseStep implements IGeneratorSearchStep {
			protected final IMinimizerStep<IChangeHandle> mMinimizerStep;
			protected final List<IChangeHandle> mChanges;
			
			public BaseStep(final IMinimizerStep<IChangeHandle> minimizerStep, final List<IChangeHandle> changes) {
				mMinimizerStep = minimizerStep;
				mChanges = changes;
			}
			
			@Override
			public String getResult() {
				return mGenerator.apply(getActiveChanges());
			}
			
			@Override
			public IDuplicateVariantTracker<IChangeHandle> getDuplicateTracker() {
				return mDuplicateTracker;
			}
			
			@Override
			public IMinimizerStep<IChangeHandle> getMinimizerStep() {
				return mMinimizerStep;
			}
			
			@Override
			public IVariantGenerator getVariantGenerator() {
				return mGenerator;
			}
			
		}
		
		/**
		 * A completed (base) step.
		 */
		private final class CompletedStep extends BaseStep {
			private CompletedStep(final IMinimizerStep<IChangeHandle> minimizerStep,
					final List<IChangeHandle> finalActiveChanges) {
				super(minimizerStep, finalActiveChanges);
			}
			
			@Override
			public List<IChangeHandle> getActiveChanges() {
				return mChanges;
			}
			
			@Override
			public String getVariant() {
				throw new UnsupportedOperationException();
			}
			
			@Override
			public boolean isDone() {
				return true;
			}
			
			@Override
			public IGeneratorSearchStep next(final boolean keepVariant) {
				throw new NoSuchElementException();
			}
		}
		
		/**
		 * A step, a particular base step.
		 */
		private final class Step extends BaseStep {
			private Step(final IMinimizerStep<IChangeHandle> minimizerStep) {
				super(minimizerStep, complementOf(minimizerStep.getVariant()));
			}
			
			@Override
			public List<IChangeHandle> getActiveChanges() {
				return complementOf(mMinimizerStep.getResult());
			}
			
			@Override
			public String getVariant() {
				return mGenerator.apply(mChanges);
			}
			
			@Override
			public boolean isDone() {
				return false;
			}
			
			@Override
			public IGeneratorSearchStep next(final boolean keepVariant) {
				final IMinimizerStep<IChangeHandle> nextMinimizerStep =
						skipDuplicateSteps(mMinimizerStep.next(keepVariant));
				if (!nextMinimizerStep.isDone()) {
					return new Step(nextMinimizerStep);
				}
				
				final List<IChangeHandle> nextActiveChanges = complementOf(nextMinimizerStep.getResult());
				final Optional<IVariantGenerator> nextGenerator = mGenerator.next(nextActiveChanges);
				if (nextGenerator.isPresent()) {
					return create(nextGenerator.get());
				}
				
				return new CompletedStep(nextMinimizerStep, nextActiveChanges);
			}
			
			private IMinimizerStep<IChangeHandle> skipDuplicateSteps(final IMinimizerStep<IChangeHandle> step) {
				IMinimizerStep<IChangeHandle> current = step;
				while (!current.isDone() && mDuplicateTracker.contains(current.getVariant())) {
					current = current.next(false);
				}
				return current;
			}
		}
	}
}
