/*
 * Copyright (C) 2009-2016 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.InterpolatorClauseTermInfo.ProofPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Coercion;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.SymmetricPair;

/**
 * The interpolator for congruence-closure theory lemmata.
 * 
 * @author Jochen Hoenicke, Tanja Schindler
 *
 */
public class CCInterpolator {

	Interpolator mInterpolator;

	HashMap<SymmetricPair<Term>, ApplicationTerm> mEqualities;
	HashMap<SymmetricPair<Term>, PathInfo> mPaths;

	Theory mTheory;
	int mNumInterpolants;

	Set<Term>[] mInterpolants;

	/**
	 * Compute the parent partition. This is the next partition, whose subtree includes color.
	 */
	private int getParent(int color) {
		int parent = color + 1;
		while (mInterpolator.mStartOfSubtrees[parent] > color) {
			parent++;
		}
		return parent;
	}

	/**
	 * Compute the A-local child partition. This is the child, that is A-local to the occurrence. This function returns
	 * -1 if all children are in B.
	 */
	private int getChild(int color, Occurrence occur) {
		/* find A-local child of m_Color */
		int child = color - 1;
		while (child >= mInterpolator.mStartOfSubtrees[color]) {
			if (occur.isALocal(child)) {
				return child;
			}
			child = mInterpolator.mStartOfSubtrees[child] - 1;
		}
		return -1;
	}

	class PathInfo {
		Term[] mPath;

		/**
		 * The set of partitions for which there is an AB-shared path from start to end.
		 */
		BitSet mHasABPath;

		/**
		 * The first partition for which the path from start to end is A-local. This is m_numInterpolants, if there is
		 * no such partition. If m_hasABPath is not empty, this value is undefined; we set it to the root of the
		 * m_hasABPath tree, which equals the two mColor of the head and tail node.
		 */
		int mMaxColor;
		PathEnd mHead, mTail;

		/*
		 * max color is the maximum of all firstColor of all literals on the path.
		 * 
		 * Head color is the lastColor of the first literal before the first path change. If head color >= max color,
		 * then there is no path change.
		 * 
		 */
		boolean mComputed;

		class PathEnd {
			/**
			 * The first partition for which there is an A-local prefix of the path. If m_hasABPath is non-empty, this
			 * is the first partition that is not in m_hasABPath, i.e. the first for which only a continuous A-path but
			 * not a continuous B-path exists.
			 */
			int mColor;
			/**
			 * For each partition on the path from m_Color to m_MaxColor this gives the term that ends the first A-local
			 * chain of equalities.
			 */
			Term[] mTerm;
			/**
			 * For each partition on the path from m_Color to the root (m_numInterpolants) this gives B-summaries that
			 * are used to gap congruence proofs, where both ends are A-local.
			 */
			Set<Term>[] mPre;

			@SuppressWarnings("unchecked")
			public PathEnd() {
				mColor = mNumInterpolants;
				mTerm = new Term[mNumInterpolants];
				mPre = new Set[mNumInterpolants];
			}

			/**
			 * Close the A path for partition color. This is called when we add a term to the chain that is B-local for
			 * the current mColor. We set mColor to the parent node. We also close the open path on mColor or open a new
			 * one and increment mMaxColor if such a path was not yet open.
			 * 
			 * @param other
			 *            the other PathEnd
			 * @param boundaryTerm
			 *            the boundary term for opening/closing the path.
			 */
			public void closeSingleAPath(PathEnd other, Term boundaryTerm) {
				// this should be empty now, since we anded it with
				// occur.mInA and the occurrence is not in A for color.
				assert mHasABPath.isEmpty();
				final int color = mColor;
				mColor = getParent(color);
				if (color < mMaxColor) {
					addPre(color, Coercion.buildEq(boundaryTerm, mTerm[color]));
					addInterpolantClause(color, mPre[color]);
					mPre[color] = null;
					mTerm[color] = null;
				} else {
					assert (mMaxColor == color);
					other.mTerm[color] = boundaryTerm;
					if (mPre[color] != null) {
						other.mPre[color] = mPre[color];
						mPre[color] = null;
					}
					mMaxColor = getParent(color);
				}
			}

			/**
			 * Open a new A path. This is called when a term is added that is A local in child, where child is a child
			 * of mColor. We start a new A path on child. If we have still slack, since mHasABPath contains child, we
			 * don't have to open the path and just set mMaxColor to child.
			 * 
			 * @param other
			 *            the other path end.
			 * @param boundaryTerm
			 *            the term that starts the new A path.
			 * @param child
			 *            the child of mColor for which the added term is A local.
			 */
			public void openSingleAPath(PathEnd other, Term boundaryTerm, int child) {
				if (mHasABPath.get(child)) {
					mMaxColor = other.mColor = mColor = child;
					// compute all nodes below child excluding child itself
					final BitSet subtree = new BitSet();
					subtree.set(mInterpolator.mStartOfSubtrees[child], child);
					// keep only those below the current child.
					mHasABPath.and(subtree);
				} else {
					/* open a new A-path. */
					mTerm[child] = boundaryTerm;
					mColor = child;
				}
			}

			public void closeAPath(PathEnd other, Term boundaryTerm, Occurrence occur) {
				assert (other.mColor <= mMaxColor);
				mHasABPath.and(occur.mInA);
				while (mColor < mNumInterpolants && occur.isBLocal(mColor)) {
					closeSingleAPath(other, boundaryTerm);
				}
			}

			public void openAPath(PathEnd other, Term boundaryTerm, Occurrence occur) {
				while (true) {
					final int child = getChild(mColor, occur);
					/* if there is no A-local child, we are done. */
					if (child < 0) {
						break;
					}
					assert occur.isALocal(child);
					openSingleAPath(other, boundaryTerm, child);
				}
			}

			public Term getBoundTerm(int color) {
				if (color < mColor) {
					final Term first = this == mHead ? mPath[0] : mPath[mPath.length - 1];
					return first;
				} else if (color < mMaxColor) {
					return mTerm[color];
				} else {
					final Term last = this == mTail ? mPath[0] : mPath[mPath.length - 1];
					return last;
				}
			}

			public void addPre(int color, Term pre) {
				if (mPre[color] == null) {
					mPre[color] = new HashSet<Term>();
				}
				mPre[color].add(pre);
			}

			public void addAllPre(int color, PathEnd src) {
				final Set<Term> pre = src.mPre[color];
				if (pre == null) {
					return;
				}
				if (mPre[color] == null) {
					mPre[color] = new HashSet<Term>();
				}
				mPre[color].addAll(pre);
			}

			private void mergeCongPath(PathEnd other, ApplicationTerm start, ApplicationTerm end) {
				final FunctionSymbol func = start.getFunction();
				final int rightColor = mInterpolator.getOccurrence(end, null).getALocalColor();
				final Occurrence rightOccur = mInterpolator.new Occurrence();
				rightOccur.occursIn(rightColor);
				final Occurrence leftOccur = mInterpolator.new Occurrence();
				leftOccur.occursIn(mColor);
				final int numArgs = func.getParameterSorts().length;
				final PathInfo[] argPaths = new PathInfo[numArgs];
				final PathEnd[] head = new PathEnd[numArgs];
				final PathEnd[] tail = new PathEnd[numArgs];
				final boolean[] isReverse = new boolean[numArgs];
				final Term[] startArgs = start.getParameters();
				final Term[] endArgs = end.getParameters();
				for (int arg = 0; arg < numArgs; arg++) {
					argPaths[arg] = startArgs[arg] == endArgs[arg] ? new PathInfo(startArgs[arg])
							: mPaths.get(new SymmetricPair<Term>(startArgs[arg], endArgs[arg]));
					argPaths[arg].interpolatePathInfo();
					isReverse[arg] = (startArgs[arg] != argPaths[arg].mPath[0]);
					head[arg] = isReverse[arg] ? argPaths[arg].mTail : argPaths[arg].mHead;
					tail[arg] = isReverse[arg] ? argPaths[arg].mHead : argPaths[arg].mTail;
					final Term startTerm = startArgs[arg];
					head[arg].closeAPath(tail[arg], startTerm, leftOccur);
					head[arg].openAPath(tail[arg], startTerm, leftOccur);
					final Term endTerm = endArgs[arg];
					tail[arg].closeAPath(head[arg], endTerm, rightOccur);
					tail[arg].openAPath(head[arg], endTerm, rightOccur);
				}

				mHasABPath.and(rightOccur.mInA);
				while (rightOccur.isBLocal(mColor)) {
					final Term[] boundaryParams = new Term[numArgs];
					for (int i = 0; i < numArgs; i++) {
						boundaryParams[i] = head[i].getBoundTerm(mColor);
						addAllPre(mColor, tail[i]);
					}
					final Term boundaryTerm = Coercion.buildApp(func, boundaryParams);
					closeSingleAPath(other, boundaryTerm);
				}
				final int highColor = mColor;
				while (true) {
					/* find A-local child of m_Color */
					final int child = getChild(mColor, rightOccur);
					if (child < 0) {
						break;
					}
					final Term[] boundaryParams = new Term[numArgs];
					for (int i = 0; i < numArgs; i++) {
						boundaryParams[i] = tail[i].getBoundTerm(child);
						addAllPre(child, tail[i]);
					}
					final Term boundaryTerm = Coercion.buildApp(func, boundaryParams);
					openSingleAPath(other, boundaryTerm, child);
				}
				assert (mColor == rightColor);
				for (int color = highColor; color < mNumInterpolants; color = getParent(color)) {
					for (int i = 0; i < numArgs; i++) {
						if (color < argPaths[i].mMaxColor) {
							addPre(color,
									mTheory.not(Coercion.buildEq(head[i].getBoundTerm(color), tail[i].getBoundTerm(color))));
						}
						addAllPre(color, head[i]);
						addAllPre(color, tail[i]);
					}
				}
			}

			@Override
			public String toString() {
				final StringBuilder sb = new StringBuilder();
				String comma = "";
				sb.append(mColor).append(":[");
				for (int i = mColor; i < mMaxColor; i++) {
					sb.append(comma);
					if (mPre[i] != null) {
						sb.append(mPre[i]).append(" or ");
					}
					sb.append(mTerm[i]);
					comma = ",";
				}
				comma = "|";
				for (int i = mMaxColor; i < mNumInterpolants; i++) {
					if (mPre[i] != null) {
						sb.append(comma).append("pre").append(i).append(':');
						sb.append(mPre[i]);
						comma = ",";
					}
				}
				sb.append(']');
				return sb.toString();
			}
		}

		/*
		 * invariants: HeadTerm[p] != null exactly for p in [m_HeadColor, m_MaxColor-1] HeadPre[p] != null only for p in
		 * [m_HeadColor, numInterpolants] HeadColor is in between first and last color of head term. likewise for Tail.
		 * MaxColor is maximum of all first of all terms and literals involved in current path (but there may be bigger
		 * literals in congruence paths that were added to headPre/tailPre).
		 * 
		 * The partial interpolant of the current path is m_Interpolants && HeadPre ==> Lits[0] == m_HeadTerm && TailPre
		 * ==> m_TailTerm == lits[n] where HeadTerm = Lits[0] for partitions < HeadColor and TailTerm = Lits[n] for
		 * partitions < TailColor.
		 *
		 * For partitions >= maxColor, everything so far was in A, so the partial interpolant of the current path is
		 * m_Interpolants && TailPre ==> Lits[0] == lits[n]
		 */

		public PathInfo(Term[] path) {
			mPath = path;
			mHasABPath = new BitSet(mNumInterpolants);
			mHasABPath.set(0, mNumInterpolants);
			mMaxColor = mNumInterpolants;
		}

		public PathInfo(Term arg) {
			this(new Term[] { arg });
		}

		public void interpolatePathInfo() {
			if (mComputed) {
				return;
			}
			final Occurrence headOccur = mInterpolator.getOccurrence(mPath[0], null);

			mHead = new PathEnd();
			mTail = new PathEnd();
			mTail.closeAPath(mHead, null, headOccur);
			mTail.openAPath(mHead, null, headOccur);

			for (int i = 0; i < mPath.length - 1; i++) {
				final Term left = mPath[i];
				final Term right = mPath[i + 1];
				final ApplicationTerm lit = mEqualities.get(new SymmetricPair<Term>(left, right));
				if (lit == null) {
					mTail.mergeCongPath(mHead, (ApplicationTerm) left, (ApplicationTerm) right);
				} else {
					final LitInfo info = mInterpolator.getLiteralInfo(lit);
					Term boundaryTerm;
					boundaryTerm = mPath[i];
					if (info.getMixedVar() == null) {
						mTail.closeAPath(mHead, boundaryTerm, info);
						mTail.openAPath(mHead, boundaryTerm, info);
					} else {
						mTail.closeAPath(mHead, boundaryTerm, info);
						mTail.openAPath(mHead, boundaryTerm, info);
						final Occurrence occ = mInterpolator.getOccurrence(mPath[i + 1], null);
						boundaryTerm = info.getMixedVar();
						mTail.closeAPath(mHead, boundaryTerm, occ);
						mTail.openAPath(mHead, boundaryTerm, occ);
					}
				}
			}
			mComputed = true;
		}

		/**
		 * Build an interpolant clause and add it to the interpolant set.
		 * 
		 * @param pre
		 *            The disequalities summarizing the requirements from the B-part in skipped argument paths.
		 * @param lhsTerm
		 *            The end of the A-equality chain.
		 * @param rhsTerm
		 *            The start of the A-equality chain.
		 * @param isNegated
		 *            True, if there is a disequality in the chain.
		 */
		private void addInterpolantClause(int color, Set<Term> pre) {
			final Term clause = pre == null ? mTheory.mFalse : mTheory.or(pre.toArray(new Term[pre.size()]));
			mInterpolants[color].add(clause);
		}

		@Override
		public String toString() {

			return "PathInfo[" + Arrays.toString(mPath) + "," + mHead + ',' + mTail + "," + mMaxColor + "]";

		}

		public void addDiseq(ApplicationTerm diseq) {
			final LitInfo info = mInterpolator.getLiteralInfo(diseq);
			Term boundaryTailTerm, boundaryHeadTerm;
			boundaryHeadTerm = mPath[0];
			boundaryTailTerm = mPath[mPath.length - 1];
			if (info.getMixedVar() == null) {
				mTail.closeAPath(mHead, boundaryTailTerm, info);
				mTail.openAPath(mHead, boundaryTailTerm, info);
				mHead.closeAPath(mTail, boundaryHeadTerm, info);
				mHead.openAPath(mTail, boundaryHeadTerm, info);
			} else {
				final Occurrence occHead = mInterpolator.getOccurrence(mPath[0], null);
				mHead.closeAPath(mTail, boundaryHeadTerm, info);
				mHead.openAPath(mTail, boundaryHeadTerm, info);
				final Occurrence occTail = mInterpolator.getOccurrence(mPath[mPath.length - 1], null);
				mTail.closeAPath(mHead, boundaryTailTerm, info);
				mTail.openAPath(mHead, boundaryTailTerm, info);

				mHead.closeAPath(mTail, info.getMixedVar(), occTail);
				mTail.closeAPath(mHead, info.getMixedVar(), occHead);
			}
		}

		public void close() {
			while (mHead.mColor < mNumInterpolants || mTail.mColor < mNumInterpolants) {
				if (mHead.mColor < mTail.mColor) {
					mHead.addPre(mHead.mColor,
							Coercion.buildEq(mHead.getBoundTerm(mHead.mColor), mTail.getBoundTerm(mMaxColor)));
					addInterpolantClause(mHead.mColor, mHead.mPre[mHead.mColor]);
					mHead.mColor = getParent(mHead.mColor);
				} else if (mHead.mColor == mTail.mColor) {
					mHead.addAllPre(mHead.mColor, mTail);
					mTail.mPre[mTail.mColor] = null;
					if (mHead.mColor < mMaxColor) {
						mHead.addPre(mHead.mColor, mTheory.not(Coercion.buildEq(mHead.getBoundTerm(mHead.mColor),
								mTail.getBoundTerm(mHead.mColor))));
					}
					addInterpolantClause(mHead.mColor, mHead.mPre[mHead.mColor]);
					mHead.mColor = mTail.mColor = getParent(mHead.mColor);
				} else {
					mTail.addPre(mTail.mColor,
							Coercion.buildEq(mHead.getBoundTerm(mMaxColor), mTail.getBoundTerm(mTail.mColor)));
					addInterpolantClause(mTail.mColor, mTail.mPre[mTail.mColor]);
					mTail.mColor = getParent(mTail.mColor);
				}
			}
		}
	}

	@SuppressWarnings("unchecked")
	public CCInterpolator(Interpolator ipolator) {
		mInterpolator = ipolator;
		mNumInterpolants = ipolator.mNumInterpolants;
		mTheory = ipolator.mTheory;
		mPaths = new HashMap<SymmetricPair<Term>, PathInfo>();
		mInterpolants = new Set[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			mInterpolants[i] = new HashSet<Term>();
		}
	}

	public Term[] computeInterpolants(Term proofTerm) {
		mEqualities = new HashMap<SymmetricPair<Term>, ApplicationTerm>();
		final InterpolatorClauseTermInfo proofTermInfo = mInterpolator.getClauseTermInfo(proofTerm);
		for (final Term literal : proofTermInfo.getLiterals()) {
			final InterpolatorLiteralTermInfo litTermInfo = mInterpolator.getLiteralTermInfo(literal);
			if (litTermInfo.isNegated()) {
				final ApplicationTerm eq = (ApplicationTerm) litTermInfo.getAtom();
				mEqualities.put(new SymmetricPair<Term>(eq.getParameters()[0], eq.getParameters()[1]), eq);
			}
		}

		PathInfo mainPath = null;
		final ProofPath[] paths = proofTermInfo.getPaths();
		for (int i = 0; i < paths.length; i++) {
			final Term[] path = paths[i].getPath();
			final Term first = path[0];
			final Term last = path[path.length - 1];
			final PathInfo pathInfo = new PathInfo(path);
			mPaths.put(new SymmetricPair<Term>(first, last), pathInfo);
			if (i == 0) {
				mainPath = pathInfo;
			}
		}
		mainPath.interpolatePathInfo();
		final ApplicationTerm diseq = (ApplicationTerm) proofTermInfo.getDiseq();
		if (diseq != null) {
			mainPath.addDiseq(diseq);
		}
		mainPath.close();
		final Term[] interpolants = new Term[mNumInterpolants];
		for (int i = 0; i < mNumInterpolants; i++) {
			interpolants[i] = mTheory.and(mInterpolants[i].toArray(new Term[mInterpolants[i].size()]));
		}
		return interpolants;
	}

	@Override
	public String toString() {
		return Arrays.toString(mInterpolants);
	}
}
