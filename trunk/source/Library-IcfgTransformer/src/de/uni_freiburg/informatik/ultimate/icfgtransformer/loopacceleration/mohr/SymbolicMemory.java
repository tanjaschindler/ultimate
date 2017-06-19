/*
 * Copyright (C) 2017 Moritz Mohr (mohrm@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.icfgtransformer.loopacceleration.mohr;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormulaUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.Substitution;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

/**
 * Manages and summarizes value updates over multiple paths.
 *
 * @author Moritz Mohr
 *
 */
public class SymbolicMemory {

	private final ManagedScript mManagedScript;
	private final ILogger mLogger;

	private final Map<IProgramVar, List<Term>> mSymbolicMemory;
	private final Map<IProgramVar, Term> mIteratedSymbolicMemory;
	private final Map<IProgramVar, UpdateType> mUpdateTypeMap;
	private final List<TermVariable> mKappas;
	private final Map<TermVariable, TermVariable> mKappa2Tau;
	private final List<Term> mRangeTerms;
	private final Map<Integer, Set<IProgramVar>> mAssignedVars;
	private final Map<TermVariable, Set<Integer>> mAssigningPaths;
	private final Map<IProgramVar, TermVariable> mInVars;
	private final Map<Term, Term> mReplaceInV;
	private final Map<IProgramVar, TermVariable> mOutVars;
	private int mCurrentPath;

	/**
	 * Construct a new symbolic memory
	 *
	 * @param manScript
	 * @param logger
	 */
	public SymbolicMemory(ManagedScript manScript, ILogger logger) {
		mManagedScript = manScript;
		mLogger = logger;

		mSymbolicMemory = new HashMap<>();
		mIteratedSymbolicMemory = new HashMap<>();
		mUpdateTypeMap = new HashMap<>();
		mKappas = new ArrayList<>();
		mKappa2Tau = new HashMap<>();
		mRangeTerms = new ArrayList<>();
		mAssignedVars = new HashMap<>();
		mAssigningPaths = new HashMap<>();
		mInVars = new HashMap<>();
		mOutVars = new HashMap<>();
		mReplaceInV = new HashMap<>();
		mCurrentPath = -1;
	}

	/**
	 * Call when considering a new path
	 */
	public void newPath() {
		mCurrentPath++;
		mAssignedVars.put(mCurrentPath, new HashSet<>());
		final TermVariable k = mManagedScript.variable("kappa" + mCurrentPath, mManagedScript.getScript().sort("Int"));
		final TermVariable kappa = mManagedScript.constructFreshCopy(k);
		mKappas.add(k);
		final TermVariable t = mManagedScript.variable("tau" + mCurrentPath, mManagedScript.getScript().sort("Int"));
		mKappa2Tau.put(k, t);
		final Term range = Util.and(mManagedScript.getScript(),
				mManagedScript.getScript().term("<=", Rational.ZERO.toTerm(mManagedScript.getScript().sort("Int")), t),
				mManagedScript.getScript().term("<", t, k));
		mRangeTerms.add(range);
	}

	/**
	 * @param variable updated variable
	 * @param value value of the update
	 * @param st
	 */
	public void updateInc(IProgramVar variable, Term value, IIcfgSymbolTable st) {
		updateInOutVars(variable, st, value.getFreeVars());
		final Substitution varRepl = new Substitution(mManagedScript, mReplaceInV);
		final Term repValue = varRepl.transform(value);
		mAssignedVars.get(mCurrentPath).add(variable);
		final UpdateType ut = mUpdateTypeMap.get(variable);
		if (ut != null) {
			switch (ut) {
				case INCREMENTATION:
					mSymbolicMemory.get(variable).add(insertPathCounter((ApplicationTerm) repValue,
							mKappa2Tau.get(mKappas.get(mCurrentPath)), variable.getTermVariable()));
					break;
				case CONSTANT:
					updateUndefined(variable, st);
					break;
				case CONSTANT_WITH_SINGLE_PATHCOUNTER:
					updateUndefined(variable, st);
					break;
				case UNDEFINED:
					break;
			}
		} else {
			mSymbolicMemory.put(variable, new ArrayList<>());
			mSymbolicMemory.get(variable).add(insertPathCounter((ApplicationTerm) repValue,
					mKappa2Tau.get(mKappas.get(mCurrentPath)), variable.getTermVariable()));
			mUpdateTypeMap.put(variable, UpdateType.INCREMENTATION);
		}
	}

	/**
	 * @param variable updated variable
	 * @param value value of the update
	 * @param st
	 */
	public void updateConst(IProgramVar variable, Term value, IIcfgSymbolTable st) {
		updateInOutVars(variable, st, value.getFreeVars());
		final Substitution varRepl = new Substitution(mManagedScript, mReplaceInV);
		final Term repValue = varRepl.transform(value);
		mAssignedVars.get(mCurrentPath).add(variable);
		final UpdateType ut = mUpdateTypeMap.get(variable);
		if (ut != null) {
			switch (ut) {
				case INCREMENTATION:
					updateUndefined(variable, st);
					break;
				case CONSTANT:
					if (!repValue.equals(mSymbolicMemory.get(variable).get(0))) {
						updateUndefined(variable, st);
					}
					break;
				case CONSTANT_WITH_SINGLE_PATHCOUNTER:
					if (!repValue.equals(mSymbolicMemory.get(variable).get(0))) {
						updateUndefined(variable, st);
					}
					mUpdateTypeMap.put(variable, UpdateType.CONSTANT);
					break;
				case UNDEFINED:
					break;
			}
		} else {
			mSymbolicMemory.put(variable, new ArrayList<>());
			mSymbolicMemory.get(variable).add(repValue);
			mUpdateTypeMap.put(variable, UpdateType.CONSTANT_WITH_SINGLE_PATHCOUNTER);
		}
	}

	/**
	 * @param variable updated variable
	 * @param value value of the update
	 * @param st
	 */
	public void updateUndefined(IProgramVar variable, IIcfgSymbolTable st) {
		mInVars.remove(variable.getTermVariable());
		updateInOutVars(variable, st, (TermVariable[]) null);
		mAssignedVars.get(mCurrentPath).add(variable);
		mSymbolicMemory.put(variable, null);
		mUpdateTypeMap.put(variable, UpdateType.UNDEFINED);
	}

	/**
	 * Returns the summarizing term of the given path.
	 * Only call if you are finished updating symbolic memory.
	 *
	 * @param path 	Index of the path
	 * @param guard {@link TransFormula} with guarding asserts
	 * @return {@link TransFormula} which summarizes the effects of the path in the loop
	 */
	public Term getFormula(final int path, final TransFormula guard) {
		mLogger.debug(">--- Path: " + path);
		if (mIteratedSymbolicMemory.isEmpty()) {
			generateTerms();
		}

		for (final IProgramVar iv : guard.getInVars().keySet()) {
			if (!mReplaceInV.containsKey(iv.getTermVariable())) {
				mInVars.put(iv, mManagedScript.constructFreshCopy(iv.getTermVariable()));
			}
		}

		for (final IProgramVar ov : guard.getOutVars().keySet()) {
			if (!mOutVars.containsKey(ov)) {
				mOutVars.put(ov, mManagedScript.constructFreshCopy(ov.getTermVariable()));
			}
		}

		final Map<TermVariable, IProgramVar> revInVars = TransFormulaUtils.constructReverseMapping(guard.getInVars());

		final Map<Term, Term> symValueSubMap = new HashMap<>();
		for (final TermVariable freeVar : guard.getFormula().getFreeVars()) {
			final IProgramVar pv = revInVars.get(freeVar);
			if (mUpdateTypeMap.get(pv) != UpdateType.UNDEFINED) {
				symValueSubMap.put(freeVar, mIteratedSymbolicMemory.get(revInVars.get(freeVar)));
			}
		}
		final Substitution varSub = new Substitution(mManagedScript, symValueSubMap);
		final Term varReplacedGuard = varSub.transform(guard.getFormula());

		final Map<Term, Term> cleanSubMap = new HashMap<>();
		for (final Map.Entry<TermVariable, IProgramVar> revInEntry : revInVars.entrySet()) {
			cleanSubMap.put(revInEntry.getKey(), mReplaceInV.get(revInEntry.getValue().getTermVariable()));
		}
		final Substitution cleanSub = new Substitution(mManagedScript, cleanSubMap);
		final Term cleanReplacedGuard = cleanSub.transform(varReplacedGuard);

		final List<Term> conjTerms = new ArrayList<>();
		final TermVariable[] exitsTaus = new TermVariable[mKappas.size() - 1];
		int arrayIndex = 0;
		for (int i = 0; i < mKappas.size(); i++) {
			if (i != path) {
				conjTerms.add(mRangeTerms.get(i));
				exitsTaus[arrayIndex] = mKappa2Tau.get(mKappas.get(i));
				arrayIndex++;
			}
		}
		for (final IProgramVar var : mAssignedVars.get(path)) {
			conjTerms.add(mManagedScript.getScript().term("=", mOutVars.get(var), mIteratedSymbolicMemory.get(var)));
		}
		conjTerms.add(cleanReplacedGuard);
		conjTerms.add(mManagedScript.getScript().term(">=", mKappas.get(path),
				Rational.ZERO.toTerm(mManagedScript.getScript().sort("Int"))));
		final Term formulaTerm = Util.and(mManagedScript.getScript(), conjTerms.toArray(new Term[conjTerms.size()]));
		final Term ex = mCurrentPath > 1 ?
				mManagedScript.getScript().quantifier(0, exitsTaus, formulaTerm, (Term[]) null) : formulaTerm;
		final TermVariable[] allTaus = new TermVariable[1];
		allTaus[0] = mKappa2Tau.get(mKappas.get(path));
		final Term allTerm = mManagedScript.getScript().quantifier(1, allTaus,
				Util.implies(mManagedScript.getScript(), mRangeTerms.get(path), ex), (Term[]) null);
		mLogger.debug(allTerm.toStringDirect());
		return allTerm;
	}

	/** -- only call after {@link SymbolicMemory.getTransformula()}
	 * @return inVars of the whole loop.
	 */
	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	/** -- only call after {@link SymbolicMemory.getTransformula()}
	 * @return outVars of the whole loop.
	 */
	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}

	public Set<TermVariable> getKappas() {
		return new HashSet<>(mKappas);
	}

	public Set<TermVariable> getTaus() {
		return new HashSet<>(mKappa2Tau.values());
	}

	private void updateInOutVars(IProgramVar outVar, IIcfgSymbolTable symbolTable, TermVariable[] inVars) {
		for (final TermVariable iv : inVars) {
			if (!mReplaceInV.containsKey(iv)) {
				final TermVariable cp = mManagedScript.constructFreshCopy(iv);
				mReplaceInV.put(iv, cp);
				mInVars.put(symbolTable.getProgramVar(iv), cp);
			}
		}

		if (!mOutVars.containsKey(outVar)) {
			mOutVars.put(outVar, mManagedScript.constructFreshCopy(outVar.getTermVariable()));
			mAssigningPaths.put(outVar.getTermVariable(), new HashSet<>());
		}
		mAssigningPaths.get(outVar.getTermVariable()).add(mCurrentPath);
	}

	private void generateTerms() {
		// todo: rewrite to original paper algorithm
		for (final Map.Entry<IProgramVar, List<Term>> symEntry : mSymbolicMemory.entrySet()) {
			final IProgramVar pv = symEntry.getKey();
			switch (mUpdateTypeMap.get(pv)) {
				case INCREMENTATION:
					final List<Term> params = symEntry.getValue();
					params.add(mReplaceInV.get(pv.getTermVariable()));
					mIteratedSymbolicMemory.put(pv, mManagedScript.getScript().term("+", params.toArray(new Term[params.size()])));
					break;
				case CONSTANT:
					mIteratedSymbolicMemory.put(pv, generateConstantAssignment(UpdateType.CONSTANT, pv, symEntry.getValue()));
					break;
				case CONSTANT_WITH_SINGLE_PATHCOUNTER:
					final Term assignedTerm = symEntry.getValue().iterator().next();
					final int p = mAssigningPaths.get(symEntry.getKey().getTermVariable()).iterator().next();
					boolean cwsp = true;
					for (final TermVariable tv : assignedTerm.getFreeVars()) {
						if (mAssigningPaths.get(tv).size() > 1 || !mAssigningPaths.get(tv).contains(p)) {
							cwsp = false;
						}
					}
					if (cwsp) {
						mIteratedSymbolicMemory.put(pv,
								generateConstantAssignment(UpdateType.CONSTANT_WITH_SINGLE_PATHCOUNTER, pv, symEntry.getValue()));
					} else {
						mIteratedSymbolicMemory.put(pv, generateConstantAssignment(UpdateType.CONSTANT, pv, symEntry.getValue()));
					}
					break;
				case UNDEFINED:
					break;
			}
		}
	}

	private Term generateConstantAssignment(final UpdateType type, final IProgramVar pv, final List<Term> symEntry) {
		final Term result;
		// Check if invar of pv exists
		if (!mInVars.containsKey(pv)) {
			mInVars.put(pv, mManagedScript.constructFreshCopy(pv.getTermVariable()));
		}

		if (type == UpdateType.CONSTANT) {
			final List<TermVariable> assignTaus = new ArrayList<>();
			for (int i = 0; i < mKappas.size(); i++) {
				if (mAssignedVars.get(i).contains(pv)) {
					assignTaus.add(mKappa2Tau.get(mKappas.get(i)));
				}
			}
			final Term tauAdd = assignTaus.size() > 1 ?
					mManagedScript.getScript().term("+", assignTaus.toArray(new Term[assignTaus.size()])) :
						assignTaus.iterator().next();
			final Term cond = mManagedScript.getScript().term("<",
					Rational.ZERO.toTerm(mManagedScript.getScript().sort("Int")), tauAdd);
			result = Util.ite(mManagedScript.getScript(), cond, symEntry.get(0), mInVars.get(pv));

		} else if (type == UpdateType.CONSTANT_WITH_SINGLE_PATHCOUNTER) {
			int path = -1;
			for (int i = 0; i < mCurrentPath; i++) {
				if (mAssignedVars.get(i).contains(pv)) {
					path = 0;
				}
			}
			final Term cond = mManagedScript.getScript().term(">", mKappa2Tau.get(mKappas.get(path)),
					Rational.ZERO.toTerm(mManagedScript.getScript().sort("Int")));
			result = Util.ite(mManagedScript.getScript(), cond, mSymbolicMemory.get(pv).get(0), mInVars.get(pv));
		} else {
			result = null;
		}
		return result;
	}

	private Term insertPathCounter(ApplicationTerm t, TermVariable pathCounter, TermVariable assignedVar) {
		final List<Term> incValue = new ArrayList<>();
		incValue.add(pathCounter);
		for (final Term parameter : t.getParameters()) {
			if (!parameter.equals(mReplaceInV.get(assignedVar))) {
				incValue.add(parameter);
			}
		}
		return mManagedScript.getScript().term("*", incValue.toArray(new Term[incValue.size()]));
	}

	private enum UpdateType {
		UNDEFINED, INCREMENTATION, CONSTANT, CONSTANT_WITH_SINGLE_PATHCOUNTER
	}
}
