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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AffineFunction;


/**
 * An multiphase ranking function as generated by the multiphase template
 * 
 * @author Jan Leike
 */
public class MultiphaseRankingFunction extends RankingFunction {
	private static final long serialVersionUID = 5376322220596462295L;
	
	private List<AffineFunction> m_ranking;
	public final int phases;
	
	public MultiphaseRankingFunction(List<AffineFunction> ranking) {
		m_ranking = ranking;
		phases = ranking.size();
		assert(phases > 0);
	}
	
	@Override
	public Set<BoogieVar> getVariables() {
		Set<BoogieVar> vars = new HashSet<BoogieVar>();
		for (AffineFunction af : m_ranking) {
			vars.addAll(af.getVariables());
		}
		return vars;
	}
	
	public List<AffineFunction> getComponents() {
		return m_ranking;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(m_ranking.size());
		sb.append("-phase ranking function:\n");
		for (int i = 0; i < phases; ++i) {
			sb.append("  f" + i);
			sb.append(" = ");
			sb.append(m_ranking.get(i));
			if (i < phases - 1) {
				sb.append("\n");
			}
		}
		return sb.toString();
	}
	
	@Override
	public Term[] asLexTerm(Script script) throws SMTLIBException {
		BigInteger n = BigInteger.ZERO;
		Term phase = script.numeral(n);
		Term value = m_ranking.get(m_ranking.size() - 1).asTerm(script);
		for (int i = m_ranking.size() - 2; i >= 0; --i) {
			n = n.add(BigInteger.ONE);
			Term f_term = m_ranking.get(i).asTerm(script);
			Term cond = script.term(">", f_term,
					script.numeral(BigInteger.ZERO));
			phase = script.term("ite", cond, script.numeral(n), phase);
			value = script.term("ite", cond, f_term, value);
		}
		return new Term[] { phase, value };
	}
	
	@Override
	public Ordinal evaluate(Map<BoogieVar, Rational> assignment) {
		Ordinal o = Ordinal.ZERO;
		for (int i = 0; i < phases; ++i) {
			Rational r = m_ranking.get(i).evaluate(assignment);
			if (r.compareTo(Rational.ZERO) > 0) {
				return o.add(Ordinal.fromInteger(r.ceil().numerator()));
			}
			o = o.add(Ordinal.OMEGA);
		}
		assert(false);
		return o;
	}
}
