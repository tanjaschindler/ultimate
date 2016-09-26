/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker.termination;

import java.io.IOException;
import java.math.BigInteger;
import java.util.Collection;
import java.util.HashSet;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.core.model.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lassoranker.AffineTerm;
import de.uni_freiburg.informatik.ultimate.lassoranker.AnalysisType;
import de.uni_freiburg.informatik.ultimate.lassoranker.ILassoRankerPreferences;
import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.SMTSolver;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarUtils;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * Simplify the generated supporting invariants by testing the implication
 *
 * (/\_{i != j} SI_i) -> SI_j for every j and dropping SI_j if it is true.
 *
 * This implication is transformed using Motzkin's Theorem and checked for satisfiability using a new solver instance.
 *
 * @author Jan Leike
 */
class SupportingInvariantSimplifier {
	private final boolean mAnnotateTerms;

	/**
	 * This script is a new script of QF_LRA that belongs only to this object
	 */
	private Script mScript;

	/**
	 * Create a new TerminationArgumentSimplifier
	 *
	 * @param preferences
	 *            LassoRanker preferences regarding new SMT scripts
	 * @throws IOException
	 */
	public SupportingInvariantSimplifier(final ILassoRankerPreferences preferences,
			final IUltimateServiceProvider services, final IToolchainStorage storage) throws IOException {
		mAnnotateTerms = preferences.isAnnotateTerms();

		// Create a new QF_LRA script
		mScript = SMTSolver.newScript(preferences, "SimplifySIs", services, storage);
		mScript.setLogic(Logics.QF_LRA);
	}

	@Override
	protected void finalize() throws Throwable {
		if (mScript != null) {
			mScript.exit();
			mScript = null;
		}
		super.finalize();
	}

	/**
	 * Convert a supporting invariant into a LinearInequality with new variables
	 */
	private static LinearInequality SI2LI(final SupportingInvariant si) {
		final LinearInequality li = new LinearInequality();
		li.add(new AffineTerm(si.mconstant));
		for (final Map.Entry<IProgramVar, BigInteger> entry : si.mcoefficients.entrySet()) {
			li.add(ReplacementVarUtils.getDefinition(entry.getKey()), new AffineTerm(entry.getValue()));
		}
		li.setStrict(si.strict);
		return li;
	}

	/**
	 * Try to simplify the supporting invariants used by the template as well as the supporting invariants generated by
	 * RewriteArrays
	 */
	public Collection<SupportingInvariant> simplify(final Collection<SupportingInvariant> sis) {
		// for now we ignore SIs generated by rewrite arrays
		final Collection<SupportingInvariant> new_sis = new HashSet<>(sis);
		for (final SupportingInvariant si : sis) {
			mScript.push(1);
			final MotzkinTransformation motzkin =
					new MotzkinTransformation(mScript, AnalysisType.Linear, mAnnotateTerms);
			final LinearInequality li = SI2LI(si);
			li.negate();
			motzkin.add_inequality(li);
			for (final SupportingInvariant si2 : new_sis) {
				if (si2 == si) {
					continue;
				}
				final LinearInequality li2 = SI2LI(si2);
				motzkin.add_inequality(li2);
			}
			motzkin.annotation = "Simplifying supporting invariant";
			mScript.assertTerm(motzkin.transform(new Rational[0]));
			li.negate();
			if (mScript.checkSat().equals(LBool.SAT)) {
				new_sis.remove(si);
			}
			mScript.pop(1);
		}
		return new_sis;
	}
}
