package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.states;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;

/**
 * Implementation of the Floyd-Warshall algorithm. Takes an undirected weighted graph as input, together with an
 * ordering of the edge weights and a "plus" operation for the edge weights.
 *
 * Returns (via getResult) a version of the graph where the triangle inequality holds (edge weights have been lowered
 * if necessary).
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 * @param <VERTEX>
 * @param <EDGELABEL>
 */
class FloydWarshall<VERTEX, EDGELABEL> {

	private final BiPredicate<EDGELABEL, EDGELABEL> mSmallerThan;
	private final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> mPlus;
	private final EDGELABEL mNullLabel;
	private final Map<Doubleton<VERTEX>, EDGELABEL> mInputGraph;

	private final Map<Doubleton<VERTEX>, EDGELABEL> mDist;
	private final List<VERTEX> mVertices;
	private boolean mPerformedChanges;

	/**
	 *
	 *
	 * @param smallerThan partial order operator (non-strict)
	 * @param plus
	 * @param nullLabel
	 * @param graph
	 * @param labelCloner
	 */
	public FloydWarshall(final BiPredicate<EDGELABEL, EDGELABEL> smallerThan,
			final BiFunction<EDGELABEL, EDGELABEL, EDGELABEL> plus,
			final EDGELABEL nullLabel,
			final Map<Doubleton<VERTEX>, EDGELABEL> graph,
			final Function<EDGELABEL, EDGELABEL> labelCloner) {
		mSmallerThan = smallerThan;
		mPlus = plus;
		mNullLabel = nullLabel;
		mInputGraph = graph;
		mPerformedChanges = false;

		// initialize with a deep copy of the graph
		mDist = new HashMap<>();
		final HashSet<VERTEX> verticeSet = new HashSet<>();
		for (final Entry<Doubleton<VERTEX>, EDGELABEL> en : graph.entrySet()) {
			verticeSet.add(en.getKey().getOneElement());
			verticeSet.add(en.getKey().getOtherElement());
			mDist.put(en.getKey(), labelCloner.apply(en.getValue()));
		}
		mVertices = new ArrayList<>(verticeSet);

		run();
	}

	public boolean performedChanges() {
		return mPerformedChanges;
	}

	/**
	 * execute the main loop of the Floyd-Warshall algorithm
	 */
	private void run() {
		for (int k = 0; k < mVertices.size(); k++) {
			for (int i = 0; i < mVertices.size(); i++) {
				if (i == k) {
					continue;
				}
				for (int j = 0; j < mVertices.size(); j++) {
					if (j == i || j == k) {
						continue;
					}
					final EDGELABEL distIj = getDist(i, j);
					final EDGELABEL distIk = getDist(i, k);
					final EDGELABEL distKj = getDist(k, j);
					final EDGELABEL ikPlusKj = mPlus.apply(distIk, distKj);

					if (!mSmallerThan.test(distIj, ikPlusKj)) {
						mDist.put(new Doubleton<>(mVertices.get(i), mVertices.get(j)), ikPlusKj);
						mPerformedChanges = true;
					}
				}
			}
		}
	}

	private EDGELABEL getDist(final int i, final int j) {
		EDGELABEL res = mDist.get(new Doubleton<>(mVertices.get(i), mVertices.get(j)));
		if (res == null) {
			res = mNullLabel;
		}
		return res;
	}

	public Map<Doubleton<VERTEX>, EDGELABEL> getResult() {
		return mDist;
	}
}