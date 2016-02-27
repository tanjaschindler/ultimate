/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 * 
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.BitvectorUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


/**
 * This represents an affine term in the form of
 * <pre>Σ c_i * x_i + c,</pre>
 * where c_i, c are rational constants
 * and x_i are variables. The variables x_i can be either TermVariables or
 * array read expressions.
 * 
 * Note that this call extends Term but is not supported by the solver.
 * We extend Term only that this can be returned by a TermTransformer.
 * 
 * Note that there is a class
 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.AffineTerm
 * which is similar but unusable in this case because it is closely
 * interweaved with the SMTLIB interiors.
 * 
 * @author Matthias Heizmann, Jan Leike
 */
public class AffineTerm extends Term {
	/**
	 * Map from Variables to coeffcients. Coefficient Zero is forbidden.
	 */
	private final Map<Term, Rational> m_Variable2Coefficient;
	
	/**
	 * Affine constant.
	 */
	private final Rational m_Constant;
	
	/**
	 * Sort of this term. E.g, "Int" or "Real".
	 */
	private final Sort m_Sort;
	
	/**
	 * AffineTerm that represents the Rational r of sort sort. 
	 */
	public AffineTerm(Sort s, Rational r) {
		super(0);
		m_Sort = s;
		m_Constant = r;
		m_Variable2Coefficient = Collections.emptyMap();
	}
	
	/**
	 * AffineTerm that consists of the single variable tv.
	 */
	public AffineTerm(TermVariable tv) {
		super(0);
		m_Sort = tv.getSort();
		m_Constant = Rational.ZERO;
		m_Variable2Coefficient = 
				Collections.singletonMap((Term) tv, Rational.ONE);
	}
	
	/**
	 * AffineTerm that consists of the single variable which is an application 
	 * term. 
	 */
	public AffineTerm(ApplicationTerm appTerm) {
		super(0);
		m_Sort = appTerm.getSort();
		m_Constant = Rational.ZERO;
		m_Variable2Coefficient = 
				Collections.singletonMap((Term) appTerm, Rational.ONE);

	}
	
	/**
	 * AffineTerm whose variables are given by an array of terms, whose 
	 * corresponding coefficients are given by the array coefficients, and
	 * whose constant term is given by the Rational constant.
	 */
	public AffineTerm(Sort s, Term[] terms, Rational[] coefficients, Rational constant) {
		super(0);
		m_Sort = s;
		m_Constant = constant;
		if (terms.length != coefficients.length) {
			throw new IllegalArgumentException(
					"numer of variables and coefficients different");
		}
		switch (terms.length) {
		case 0:
			m_Variable2Coefficient = Collections.emptyMap();
			break;
		case 1:
			Term variable = terms[0];
			checkIfTermIsLegalVariable(variable);
			if (coefficients[0].equals(Rational.ZERO)) {
				m_Variable2Coefficient = Collections.emptyMap();
			} else {
				m_Variable2Coefficient = 
						Collections.singletonMap(variable, coefficients[0]);
			}
			break;
		default:
			m_Variable2Coefficient = new HashMap<Term, Rational>();
			for (int i=0; i<terms.length; i++) {
				checkIfTermIsLegalVariable(terms[i]);
				if (!coefficients[i].equals(Rational.ZERO)) {
					m_Variable2Coefficient.put(terms[i], coefficients[i]);
				}
			}
		}
	}
	
	/**
	 * Check if term is of a type that may be a variable of an AffineTerm.
	 */
	public void checkIfTermIsLegalVariable(Term term) {
		if (term instanceof TermVariable || term instanceof ApplicationTerm) {
			// term is ok
		} else {
			throw new IllegalArgumentException(
					"Variable of AffineTerm has to be TermVariable or ApplicationTerm");
		}
	}
	
	
	/**
	 * AffineTerm that represents the sum of affineTerms.
	 */
	public AffineTerm(AffineTerm... affineTerms) {
		super(0);
		m_Sort = affineTerms[0].getSort();
		m_Variable2Coefficient = new HashMap<Term, Rational>();
		Rational constant = Rational.ZERO;
		for (AffineTerm affineTerm : affineTerms) {
			for (Map.Entry<Term, Rational> summand :
					affineTerm.m_Variable2Coefficient.entrySet()) {
				assert summand.getKey().getSort() == m_Sort : 
					"Sort mismatch: " + summand.getKey().getSort() + " vs. " + m_Sort;
				final Rational coeff = m_Variable2Coefficient.get(summand.getKey());
				if (coeff == null) {
					m_Variable2Coefficient.put(summand.getKey(), summand.getValue());
				} else {
					final Rational newCoeff;
					if (BitvectorUtils.isBitvectorSort(m_Sort)) {
						newCoeff = bringValueInRange(coeff.add(summand.getValue()), m_Sort);
					} else {
						newCoeff = coeff.add(summand.getValue());
					}
					if (newCoeff.equals(Rational.ZERO)) {
						m_Variable2Coefficient.remove(summand.getKey());
					} else {
						m_Variable2Coefficient.put(summand.getKey(), newCoeff);
					}
				}
			}
			if (BitvectorUtils.isBitvectorSort(m_Sort)) {
				constant = bringValueInRange(constant.add(affineTerm.m_Constant), m_Sort);
			} else {
				constant = constant.add(affineTerm.m_Constant);
			}
		}
		m_Constant = constant;
	}

	/**
	 * AffineTerm that represents the product of affineTerm and multiplier.
	 */
	public AffineTerm(AffineTerm affineTerm, Rational multiplier) {
		super(0);
		if (multiplier.equals(Rational.ZERO)) {
			m_Sort = affineTerm.getSort();
			m_Constant = Rational.ZERO;
			m_Variable2Coefficient = Collections.emptyMap();
		} else {
			m_Variable2Coefficient = new HashMap<Term, Rational>();
			m_Sort = affineTerm.getSort();
			if (BitvectorUtils.isBitvectorSort(m_Sort)) {
				m_Constant = bringValueInRange(affineTerm.m_Constant.mul(multiplier), m_Sort);
			} else {
				assert m_Sort.isNumericSort();
				m_Constant = affineTerm.m_Constant.mul(multiplier);
			}
			for (Map.Entry<Term, Rational> summand :
				affineTerm.m_Variable2Coefficient.entrySet()) {
				m_Variable2Coefficient.put(summand.getKey(), summand.getValue().mul(multiplier));
			}
		}
	}

	/**
	 * Use modulo operation to bring Rational in the range of representable
	 * values.
	 * @param bv Rational that represents a bitvector
	 * @param sort bitvector sort
	 * @return bv % 2^sort.getIndices[0]
	 */
	private static Rational bringValueInRange(Rational bv, Sort sort) {
		assert BitvectorUtils.isBitvectorSort(sort);
		assert sort.getIndices().length == 1;
		assert bv.isIntegral();
		final int bitsize = sort.getIndices()[0].intValueExact();
		final BigInteger bvBigInt = bv.numerator();
		final BigInteger numberOfValues = BigInteger.valueOf(2).pow(bitsize);
		final BigInteger resultBigInt = BoogieUtils.euclideanMod(bvBigInt, numberOfValues);
		return Rational.valueOf(resultBigInt, BigInteger.ONE);
	}

	/**
	 * Auxiliary affine term that represents an error during the translation
	 * process, e.g., if original term was not linear.
	 */
	public AffineTerm() {
		super(0);
		m_Variable2Coefficient = null;
		m_Constant = null;
		m_Sort = null;
	}
	
	/**
	 * True if this represents not an affine term but an error during the 
	 * translation process, e.g., if original term was not linear.
	 */
	public boolean isErrorTerm() {
		if (m_Variable2Coefficient == null) {
			assert m_Constant == null;
			assert m_Sort == null;
			return true;
		} else {
			assert m_Constant != null;
			assert m_Sort != null;
			return false;
		}
	}
	

	/**
	 * @return whether this affine term is just a constant
	 */
	public boolean isConstant() {
		return m_Variable2Coefficient.isEmpty();
	}
	
	/**
	 * @return whether this affine term is zero
	 */
	public boolean isZero() {
		return m_Constant.equals(Rational.ZERO)
				&& m_Variable2Coefficient.isEmpty();
	}
	
	/**
	 * @return the constant summand of this affine term
	 */
	public Rational getConstant() {
		return m_Constant;
	}
	
	/**
	 * @return unmodifiable map where each variable is mapped to its coefficient. 
	 */
	public Map<Term, Rational> getVariable2Coefficient() {
		return Collections.unmodifiableMap(m_Variable2Coefficient);
	}
	
	/**
	 * Transforms this AffineTerm into a Term that is supported by the solver.
	 * @param script Script for that this term is constructed.
	 */
	public Term toTerm(Script script) {
		Term[] summands;
		if (m_Constant.equals(Rational.ZERO)) {
			summands = new Term[m_Variable2Coefficient.size()];
		} else {
			summands = new Term[m_Variable2Coefficient.size() + 1];
		}
		int i = 0;
		for (Map.Entry<Term, Rational> entry :
				m_Variable2Coefficient.entrySet()) {
			assert !entry.getValue().equals(Rational.ZERO) : 
								"zero is no legal coefficient in AffineTerm";
			if (entry.getValue().equals(Rational.ONE)) {
				summands[i] = entry.getKey();
			} else {
				Term coeff = SmtUtils.rational2Term(script, entry.getValue(), m_Sort);
				summands[i] = SmtUtils.mul(script, m_Sort, coeff, entry.getKey()); 
			}
			++i;
		}
		if (!m_Constant.equals(Rational.ZERO)) {
			assert m_Constant.isIntegral() || m_Sort.getName().equals("Real");
			summands[i] = SmtUtils.rational2Term(script, m_Constant, m_Sort);
		}
		Term result = SmtUtils.sum(script, m_Sort, summands);
		return result;
	}
	
	@Override
	public String toString() {
		if (isErrorTerm()) {
			return "auxilliaryErrorTerm";
		}
		StringBuilder sb = new StringBuilder();
		for (Map.Entry<Term, Rational> entry :
				m_Variable2Coefficient.entrySet()) {
			sb.append(entry.getValue().isNegative() ? " - " : " + ");
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
		}
		if (!m_Constant.equals(Rational.ZERO) || sb.length() == 0) {
			if (m_Constant.isNegative() || sb.length() > 0) {
				sb.append(m_Constant.isNegative() ? " - " : " + ");
			}
			sb.append(m_Constant.abs());
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}
		
		return result;
	}
	
	@Override
	public Sort getSort() {
		return m_Sort;
	}
	
	@Override
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		throw new UnsupportedOperationException(
				"This is an auxilliary Term and not supported by the solver");
	}
	
	public static AffineTerm applyModuloToAllCoefficients(Script script, AffineTerm affineTerm, BigInteger divident) {
		assert affineTerm.getSort().getName().equals("Int");
		Map<Term, Rational> map = affineTerm.getVariable2Coefficient();
		Term[] terms = new Term[map.size()];
		Rational[] coefficients = new Rational[map.size()];
		int offset = 0;
		for (Entry<Term, Rational> entry : map.entrySet()) {
			terms[offset] = entry.getKey();
			coefficients[offset] = SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(entry.getValue()),divident));
			offset++;
		}
		Rational constant = SmtUtils.toRational(BoogieUtils.euclideanMod(SmtUtils.toInt(affineTerm.getConstant()),divident));
		return new AffineTerm(affineTerm.getSort(), terms, coefficients, constant );
	}
}
