/*
 * Copyright (C) 2015 Dirk Steinmetz
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * A simple {@link ILinearInequalityInvariantPatternStrategy}, generating
 * location-independent invariant patterns, each a disjunction composed of a
 * increasing number of conjunctions of a increasing number of inequalities over
 * all program variables.
 */
public abstract class LocationIndependentLinearInequalityInvariantPatternStrategy
		implements ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>> {

	private final int baseDisjuncts;
	private final int baseConjuncts;
	private final int disjunctsPerRound;
	private final int conjunctsPerRound;
	private final int maxRounds;
	protected final Set<IProgramVar> mAllProgramVariables;
	protected final Set<IProgramVar> mPatternVariables;
	protected int mPrefixCounter;

	/**
	 * Generates a simple linear inequality invariant pattern strategy.
	 * 
	 * @param baseDisjuncts
	 *            number of conjunctions within the outer disjunction in the
	 *            pattern, first iteration
	 * @param baseConjuncts
	 *            number of inequalities within each conjunction in the pattern,
	 *            first iteration
	 * @param disjunctsPerRound
	 *            number of conjunctions within the outer disjunction added
	 *            after each round
	 * @param conjunctsPerRound
	 *            number of inequalities within each conjunction added after
	 *            each round
	 * @param maxRounds
	 *            maximal number of rounds to be announced by
	 *            {@link #getMaxRounds()}.
	 * @param patternVariables 
	 * @param allProgramVariables 
	 */
	public LocationIndependentLinearInequalityInvariantPatternStrategy(
			final int baseDisjuncts, final int baseConjuncts,
			final int disjunctsPerRound, final int conjunctsPerRound,
			final int maxRounds, Set<IProgramVar> allProgramVariables, Set<IProgramVar> patternVariables) {
		this.baseConjuncts = baseConjuncts;
		this.baseDisjuncts = baseDisjuncts;
		this.disjunctsPerRound = disjunctsPerRound;
		this.conjunctsPerRound = conjunctsPerRound;
		this.maxRounds = maxRounds;
		mAllProgramVariables = allProgramVariables;
		mPatternVariables = patternVariables;
		mPrefixCounter = 0;
	}

//	/**
//	 * {@inheritDoc}
//	 */
//	@Override
//	public int[] getDimensions(final Location location, final int round) {
//		return new int[] { baseDisjuncts + round * disjunctsPerRound,
//				baseConjuncts + round * conjunctsPerRound };
//		// 2015-10-27: Use the following instead to obtain two disjuncts
//		// consisting of one strict-nonstrict conjunction pair each. 
////		return new int[] { 2, 1};
//	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return maxRounds;
	}
	
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location, int round, Script solver, String prefix) {
		return getInvariantPatternForLocation(location, round, solver, prefix, getPatternVariablesForLocation(location, round));
	}
	
	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location,
			int round, Script solver, String prefix, Set<IProgramVar> vars) {
		final int[] dimensions = getDimensions(location, round);
		// Build invariant pattern
		final Collection<Collection<AbstractLinearInvariantPattern>> disjunction = new ArrayList<>(dimensions[0]);
		for (int i = 0; i < dimensions[0]; i++) {
			final Collection<AbstractLinearInvariantPattern> conjunction = new ArrayList<>(
					dimensions[1]);
			for (int j = 0; j < dimensions[1]; j++) {
				final boolean[] invariantPatternCopies;
//				if (mAlwaysStrictAndNonStrictCopies ) {
//					invariantPatternCopies = new boolean[] { false, true }; 
//				} else {
					invariantPatternCopies = new boolean[] { false };
//				}
				for (final boolean strict : invariantPatternCopies) {
					final LinearPatternBase inequality = new LinearPatternBase (
							solver, vars, prefix + "_" + newPrefix(), strict);
//					Collection<Term> params = inequality.getCoefficients();
//					mPatternCoefficients.addAll(params);
					conjunction.add(inequality);
				}
			}
			disjunction.add(conjunction);
		}
		return disjunction;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int[] getDimensions(IcfgLocation location, int round) {
		return new int[] { baseDisjuncts + round * disjunctsPerRound,
				baseConjuncts + round * conjunctsPerRound };
		// 2015-10-27: Use the following instead to obtain two disjuncts
		// consisting of one strict-nonstrict conjunction pair each. 
//		return new int[] { 2, 1};
	}
	
	public void resetSettings() {
		mPrefixCounter = 0;
	}
	
	protected String newPrefix() {
		return Integer.toString(mPrefixCounter++);
	}

}
