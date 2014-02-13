/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;


/**
 * Creates and extracts supporting invariants.
 * This class is the counterpart of the RankingFunctionTemplate classes for
 * supporting invariants.
 * 
 * @author Jan Leike
 */
public class SupportingInvariantGenerator extends AffineFunctionGenerator {
	private static final String s_prefix = "si";
	
	/**
	 * Whether the inequality is strict ("<") versus non-strict ("<=")
	 */
	public boolean strict;
	
	/**
	 * @param script The SMTLib script
	 * @param variables A collection of all variables that are relevant for
	 *                   the supporting invariant
	 * @param strict is this invariant a strict inequality?
	 */
	SupportingInvariantGenerator(Script script,
			Collection<BoogieVar> variables, boolean strict) {
		super(script, variables, s_prefix
				+ (new InstanceCounting()).m_instance);
		this.strict = strict;
	}
	
	/**
	 * Generate the linear inequality
	 * @param vars a mapping from Boogie variables to TermVariables to be used
	 * @return Linear inequality corresponding to si(x)
	 */
	public LinearInequality generate(Map<BoogieVar, TermVariable> vars) {
		LinearInequality li = super.generate(vars);
		li.needs_motzkin_coefficient = false;
		li.setStrict(this.strict);
		return li;
	}
	
	/**
	 * Extract the supporting invariant from a model
	 * @return supporting invariant
	 * @throws SMTLIBException
	 */
	public SupportingInvariant extractSupportingInvariant(Map<Term, Rational> val)
			throws SMTLIBException {
		AffineFunction f = super.extractAffineFunction(val);
		SupportingInvariant si = new SupportingInvariant(f);
		si.strict = this.strict;
		return si;
	}
}