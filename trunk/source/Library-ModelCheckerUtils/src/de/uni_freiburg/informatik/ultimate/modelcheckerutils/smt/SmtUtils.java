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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieUtils;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.LoggingScript;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.bdd.SimplifyBdd;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineRelation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineSubtermNormalizer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTerm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.AffineTermTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.NotAffineException;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.CnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.DnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.normalForms.NnfTransformer.QuantifierHandling;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.DebugMessage;

public final class SmtUtils {

	private static final String ERROR_MESSAGE_UNKNOWN_ENUM_CONSTANT = "unknown enum constant ";
	private static final String ERROR_MSG_UNKNOWN_SORT = "unknown sort ";
	/**
	 * Avoid the construction of "bvadd" with more than two arguments and use nested "bvadd" terms instead.
	 */
	private static final boolean BINARY_BITVECTOR_SUM_WORKAROUND = false;

	/**
	 * Name of a non-standard FloatingPoint extension that is supported by Z3.
	 */
	public static final String FP_TO_IEEE_BV_EXTENSION = "fp.to_ieee_bv";

	public enum XnfConversionTechnique {
		BDD_BASED, BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION
	}

	public enum SimplificationTechnique {
		SIMPLIFY_BDD_PROP, SIMPLIFY_BDD_FIRST_ORDER, SIMPLIFY_QUICK, SIMPLIFY_DDA, NONE
	}

	private SmtUtils() {
		// Prevent instantiation of this utility class
	}

	public static Term simplify(final ManagedScript script, final Term formula, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique) {
		final ILogger logger = services.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		if (logger.isDebugEnabled()) {
			logger.debug(new DebugMessage("simplifying formula of DAG size {0}", new DagSizePrinter(formula)));
		}
		final long startTime = System.nanoTime();
		final Term simplified;
		switch (simplificationTechnique) {
		case SIMPLIFY_BDD_PROP:
			simplified = new SimplifyBdd(services, script).transform(formula);
			break;
		case SIMPLIFY_BDD_FIRST_ORDER:
			simplified = new SimplifyBdd(services, script).transformWithImplications(formula);
			break;
		case SIMPLIFY_DDA:
			simplified = new SimplifyDDAWithTimeout(script.getScript(), services).getSimplifiedTerm(formula);
			break;
		case SIMPLIFY_QUICK:
			simplified = new SimplifyQuick(script.getScript(), services).getSimplifiedTerm(formula);
			break;
		case NONE:
			return formula;
		default:
			throw new AssertionError(ERROR_MESSAGE_UNKNOWN_ENUM_CONSTANT + simplificationTechnique);
		}
		if (logger.isDebugEnabled()) {
			logger.debug(new DebugMessage("DAG size before simplification {0}, DAG size after simplification {1}",
					new DagSizePrinter(formula), new DagSizePrinter(simplified)));
		}
		final long endTime = System.nanoTime();
		final long overallTimeMs = (endTime - startTime) / 1_000_000;
		if (formula.equals(simplified) && overallTimeMs >= 100) {
			logger.warn("Spent " + overallTimeMs + "ms on a formula simplification that was a NOOP. DAG size: "
					+ new DagSizePrinter(formula));
		} else if (overallTimeMs >= 100) {
			logger.warn("Spent " + overallTimeMs + "ms on a formula simplification. DAG size of input: "
					+ new DagSizePrinter(formula) + " DAG size of output " + new DagSizePrinter(simplified));

		}
		return simplified;
	}

	public static ExtendedSimplificationResult simplifyWithStatistics(final ManagedScript script, final Term formula,
			final IUltimateServiceProvider services, final SimplificationTechnique simplificationTechnique) {
		final long startTime = System.nanoTime();
		final long sizeBefore = new DAGSize().treesize(formula);
		final Term simplified = simplify(script, formula, services, simplificationTechnique);
		final long sizeAfter = new DAGSize().treesize(simplified);
		final long endTime = System.nanoTime();
		final ExtendedSimplificationResult result =
				new ExtendedSimplificationResult(simplified, endTime - startTime, sizeBefore - sizeAfter, ((double) sizeAfter) / sizeBefore * 100);
		return result;
	}

	public static class ExtendedSimplificationResult {
		private final Term mSimplifiedTerm;
		private final long mSimplificationTimeNano;
		private final long mReductionOfTreeSize;
		private final double mReductionRatioInPercent;

		public ExtendedSimplificationResult(final Term simplifiedTerm, final long simplificationTimeNano,
				final long reductionOfTreeSize, final double reductionRatioPercent) {
			super();
			mSimplifiedTerm = simplifiedTerm;
			mSimplificationTimeNano = simplificationTimeNano;
			mReductionOfTreeSize = reductionOfTreeSize;
			mReductionRatioInPercent = reductionRatioPercent;
		}

		public Term getSimplifiedTerm() {
			return mSimplifiedTerm;
		}

		public long getSimplificationTimeNano() {
			return mSimplificationTimeNano;
		}

		public long getReductionOfTreeSize() {
			return mReductionOfTreeSize;
		}

		public double getReductionRatioInPercent() {
			return mReductionRatioInPercent;
		}
		
		

	}

	public static LBool checkSatTerm(final Script script, final Term formula) {
		return Util.checkSat(script, formula);
	}

	/**
	 * If term is a conjunction return all conjuncts, otherwise return term.
	 */
	public static Term[] getConjuncts(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if ("and".equals(appTerm.getFunction().getName())) {
				return appTerm.getParameters();
			}
		}
		final Term[] result = new Term[1];
		result[0] = term;
		return result;
	}

	/**
	 * If term is a disjunction return all disjuncts, otherwise return term.
	 */
	public static Term[] getDisjuncts(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if ("or".equals(appTerm.getFunction().getName())) {
				return appTerm.getParameters();
			}
		}
		final Term[] result = new Term[1];
		result[0] = term;
		return result;
	}

	/**
	 * Takes an ApplicationTerm with pairwise function symbol (e.g. distinct) or chainable function symbol (e.g.
	 * equality) and return a conjunction of pairwise applications of the function symbol. E.g. the ternary equality (=
	 * a b c) becomes (and (= a b) (= a c) (= b c)).
	 */
	public static Term binarize(final Script script, final ApplicationTerm term) {
		final FunctionSymbol functionSymbol = term.getFunction();
		if (!functionSymbol.isPairwise() && !functionSymbol.isChainable()) {
			throw new IllegalArgumentException("can only binarize pairwise terms");
		}
		final String functionName = functionSymbol.getApplicationString();
		final Term[] params = term.getParameters();
		assert params.length > 1;
		final List<Term> conjuncts = new ArrayList<>();
		for (int i = 0; i < params.length; i++) {
			for (int j = i + 1; j < params.length; j++) {
				conjuncts.add(script.term(functionName, params[i], params[j]));
			}
		}
		return SmtUtils.and(script, conjuncts.toArray(new Term[conjuncts.size()]));
	}

	public static boolean firstParamIsBool(final ApplicationTerm term) {
		final Term[] params = term.getParameters();
		return SmtSortUtils.isBoolSort(params[0].getSort());
	}

	public static boolean allParamsAreBool(final ApplicationTerm term) {
		return Arrays.stream(term.getParameters()).map(a -> a.getSort()).allMatch(SmtSortUtils::isBoolSort);
	}

	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is equivalent to (= lhs rhs) but uses only the
	 * boolean connectives "and" and "or".
	 */
	public static Term binaryBooleanEquality(final Script script, final Term lhs, final Term rhs) {
		assert SmtSortUtils.isBoolSort(lhs.getSort());
		assert SmtSortUtils.isBoolSort(rhs.getSort());
		final Term bothTrue = SmtUtils.and(script, lhs, rhs);
		final Term bothFalse = SmtUtils.and(script, SmtUtils.not(script, lhs), SmtUtils.not(script, rhs));
		return SmtUtils.or(script, bothTrue, bothFalse);
	}

	/**
	 * Given Term lhs and Term rhs of Sort "Bool". Returns a Term that is equivalent to (not (= lhs rhs)) but uses only
	 * the boolean connectives "and" and "or".
	 */
	public static Term binaryBooleanNotEquals(final Script script, final Term lhs, final Term rhs) {
		assert SmtSortUtils.isBoolSort(lhs.getSort());
		assert SmtSortUtils.isBoolSort(rhs.getSort());
		final Term oneIsTrue = SmtUtils.or(script, lhs, rhs);
		final Term oneIsFalse = SmtUtils.or(script, SmtUtils.not(script, lhs), SmtUtils.not(script, rhs));
		return SmtUtils.and(script, oneIsTrue, oneIsFalse);
	}

	/**
	 * Given a list of Terms term1, ... ,termn returns a new list that contains (not term1), ... ,(not termn) in this
	 * order.
	 */
	public static List<Term> negateElementwise(final Script script, final List<Term> terms) {
		final List<Term> result = new ArrayList<>(terms.size());
		for (final Term term : terms) {
			result.add(SmtUtils.not(script, term));
		}
		return result;
	}

	/**
	 * Returns the term that selects the element at index from (possibly) multi dimensional array a. E.g. If the array
	 * has Sort (Int -> Int -> Int) and index is [23, 42], this method returns the term ("select" ("select" a 23) 42).
	 */
	public static Term multiDimensionalSelect(final Script script, final Term a, final ArrayIndex index) {
		assert a.getSort().isArraySort();
		Term result = a;
		for (int i = 0; i < index.size(); i++) {
			result = script.term("select", result, index.get(i));
		}
		return result;
	}

	/**
	 * Returns the term that stores the element at index from (possibly) multi dimensional array a. E.g. If the array
	 * has Sort (Int -> Int -> Int) and we store the value val at index [23, 42], this method returns the term (store a
	 * 23 (store (select a 23) 42 val)).
	 */
	public static Term multiDimensionalStore(final Script script, final Term a, final ArrayIndex index,
			final Term value) {
		assert !index.isEmpty();
		assert a.getSort().isArraySort();
		Term result = value;
		for (int i = index.size() - 1; i >= 0; i--) {
			final Term selectUpToI = multiDimensionalSelect(script, a, index.getFirst(i));
			result = script.term("store", selectUpToI, index.get(i), result);
		}
		return result;
	}

	/**
	 * Returns true iff each key and each value is non-null.
	 */
	public static <K, V> boolean neitherKeyNorValueIsNull(final Map<K, V> map) {
		for (final Entry<K, V> entry : map.entrySet()) {
			if (entry.getKey() == null || entry.getValue() == null) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Given the array of terms [lhs_1, ..., lhs_n] and the array of terms [rhs_1, ..., rhs_n], return the conjunction
	 * of the following equalities lhs_1 = rhs_1, ... , lhs_n = rhs_n.
	 */
	public static Term pairwiseEquality(final Script script, final List<Term> lhs, final List<Term> rhs) {
		if (lhs.size() != rhs.size()) {
			throw new IllegalArgumentException("must have same length");
		}
		final Term[] equalities = new Term[lhs.size()];
		for (int i = 0; i < lhs.size(); i++) {
			equalities[i] = binaryEquality(script, lhs.get(i), rhs.get(i));
		}
		return SmtUtils.and(script, equalities);
	}

	/**
	 * Construct the following term. (index1 == index2) ==> (value1 == value2)
	 */
	public static Term indexEqualityImpliesValueEquality(final Script script, final ArrayIndex index1,
			final ArrayIndex index2, final Term value1, final Term value2) {
		assert index1.size() == index2.size();
		final Term lhs = pairwiseEquality(script, index1, index2);
		final Term rhs = binaryEquality(script, value1, value2);
		return SmtUtils.or(script, not(script, lhs), rhs);
	}

	/**
	 * Return term that represents the sum of all summands. Return the neutral element for sort sort if summands is
	 * empty.
	 */
	public static Term sum(final Script script, final Sort sort, final Term... summands) {
		assert SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBitvecSort(sort);
		if (summands.length == 0) {

			if (SmtSortUtils.isIntSort(sort)) {
				return script.numeral(BigInteger.ZERO);
			} else if (SmtSortUtils.isRealSort(sort)) {
				return script.decimal(BigDecimal.ZERO);
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				return BitvectorUtils.constructTerm(script, BigInteger.ZERO, sort);
			} else {
				throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
			}
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			if (SmtSortUtils.isNumericSort(sort)) {
				return script.term("+", summands);
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				if (BINARY_BITVECTOR_SUM_WORKAROUND) {
					return binaryBitvectorSum(script, sort, summands);
				}
				return script.term("bvadd", summands);
			} else {
				throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
			}
		}
	}

	/**
	 * Construct nested binary "bvadd" terms.
	 *
	 * @param sort
	 *            bitvector sort of the arguments (required if summands is empty)
	 * @param summands
	 *            bitvector terms that each have the same sort
	 */
	public static Term binaryBitvectorSum(final Script script, final Sort sort, final Term... summands) {
		if (summands.length == 0) {
			return BitvectorUtils.constructTerm(script, BigInteger.ZERO, sort);
		} else if (summands.length == 1) {
			return summands[0];
		} else {
			Term result = script.term("bvadd", summands[0], summands[1]);
			for (int i = 2; i < summands.length; i++) {
				result = script.term("bvadd", result, summands[i]);
			}
			return result;
		}
	}

	/**
	 * Return term that represents the product of all factors. Return the neutral element for sort sort if factors is
	 * empty.
	 */
	public static Term mul(final Script script, final Sort sort, final Term... factors) {
		assert SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBitvecSort(sort);
		if (factors.length == 0) {
			if (SmtSortUtils.isIntSort(sort)) {
				return script.numeral(BigInteger.ONE);
			} else if (SmtSortUtils.isRealSort(sort)) {
				return script.decimal(BigDecimal.ONE);
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				return BitvectorUtils.constructTerm(script, BigInteger.ONE, sort);
			} else {
				throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
			}
		} else if (factors.length == 1) {
			return factors[0];
		} else {
			if (SmtSortUtils.isNumericSort(sort)) {
				return script.term("*", factors);
			} else if (SmtSortUtils.isBitvecSort(sort)) {
				return script.term("bvmul", factors);
			} else {
				throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
			}
		}
	}

	/**
	 * Return sum, in affine representation if possible.
	 *
	 * @param funcname
	 *            either "+" or "bvadd".
	 */
	public static Term sum(final Script script, final String funcname, final Term... summands) {
		assert "+".equals(funcname) || "bvadd".equals(funcname);
		final Term sum = script.term(funcname, summands);
		final AffineTerm affine = (AffineTerm) new AffineTermTransformer(script).transform(sum);
		if (affine.isErrorTerm()) {
			return sum;
		}
		return affine.toTerm(script);
	}

	/**
	 * Return term that represents negation (unary minus).
	 */
	public static Term neg(final Script script, final Sort sort, final Term operand) {
		assert SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBitvecSort(sort);
		if (SmtSortUtils.isNumericSort(sort)) {
			return script.term("-", operand);
		} else if (SmtSortUtils.isBitvecSort(sort)) {
			return script.term("bvneg", operand);
		} else {
			throw new UnsupportedOperationException(ERROR_MSG_UNKNOWN_SORT + sort);
		}
	}

	/**
	 * Return term that represents negation of boolean term.
	 */
	public static Term not(final Script script, final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			if ("distinct".equals(appTerm.getFunction().getName()) && appTerm.getParameters().length == 2) {
				return SmtUtils.binaryEquality(script, appTerm.getParameters()[0], appTerm.getParameters()[1]);
			}
			return Util.not(script, term);
		}
		return Util.not(script, term);
	}

	/**
	 * Returns the equality ("=" lhs rhs), or true resp. false if some simple checks detect validity or unsatisfiablity
	 * of the equality.
	 */
	public static Term binaryEquality(final Script script, final Term lhs, final Term rhs) {
		if (lhs == rhs) {
			return script.term("true");
		} else if (lhs.getSort().isNumericSort()) {
			return numericEquality(script, lhs, rhs);
		} else if (SmtSortUtils.isBoolSort(lhs.getSort())) {
			return booleanEquality(script, lhs, rhs);
		} else if (SmtSortUtils.isBitvecSort(lhs.getSort())) {
			return bitvectorEquality(script, lhs, rhs);
		} else if (SmtSortUtils.isArraySort(lhs.getSort())) {
			return arrayEquality(script, lhs, rhs);
		} else {
			return script.term("=", lhs, rhs);
		}
	}

	/**
	 * Returns the negated equality (not ("=" lhs rhs)), or true resp. false if some simple checks detect validity or
	 * unsatisfiablity of the equality. We deliberately do not return the "distinct" function from SMT-LIB. In Ultimate
	 * we prefer explicit negations, because these can help us detect inconsitencies between terms syntactically.
	 */
	public static Term distinct(final Script script, final Term lhs, final Term rhs) {
		return SmtUtils.not(script, binaryEquality(script, lhs, rhs));
	}

	/**
	 * Returns the equality ("=" lhs rhs), but checks if one of the arguments is true/false and simplifies accordingly.
	 */
	private static Term booleanEquality(final Script script, final Term lhs, final Term rhs) {
		if (isTrue(lhs)) {
			return rhs;
		} else if (isFalse(lhs)) {
			return SmtUtils.not(script, rhs);
		} else if (isTrue(rhs)) {
			return lhs;
		} else if (isFalse(rhs)) {
			return SmtUtils.not(script, lhs);
		} else {
			return script.term("=", lhs, rhs);
		}
	}

	/**
	 * Returns the equality ("=" lhs rhs), for inputs of sort BitVec. Simplifies if both inputs are literals.
	 */
	private static Term bitvectorEquality(final Script script, final Term lhs, final Term rhs) {
		if (!SmtSortUtils.isBitvecSort(lhs.getSort())) {
			throw new UnsupportedOperationException("need BitVec sort");
		}
		if (!SmtSortUtils.isBitvecSort(rhs.getSort())) {
			throw new UnsupportedOperationException("need BitVec sort");
		}
		final BitvectorConstant fstbw = BitvectorUtils.constructBitvectorConstant(lhs);
		if (fstbw != null) {
			final BitvectorConstant sndbw = BitvectorUtils.constructBitvectorConstant(rhs);
			if (sndbw != null) {
				if (fstbw.equals(sndbw)) {
					return script.term("true");
				}
				return script.term("false");
			}
		}
		return script.term("=", lhs, rhs);
	}

	/**
	 * Returns the equality ("=" lhs rhs), for inputs of numeric sort (int, real) Simplifies if both inputs are
	 * literals.
	 */
	private static Term numericEquality(final Script script, final Term lhs, final Term rhs) {
		if (!lhs.getSort().isNumericSort()) {
			throw new UnsupportedOperationException("need numeric sort");
		}
		if (!rhs.getSort().isNumericSort()) {
			throw new UnsupportedOperationException("need numeric sort");
		}
		if (!(lhs instanceof ConstantTerm)) {
			return script.term("=", lhs, rhs);
		}
		if (!(rhs instanceof ConstantTerm)) {
			return script.term("=", lhs, rhs);
		}
		final ConstantTerm lhsConst = (ConstantTerm) lhs;
		final ConstantTerm rhsConst = (ConstantTerm) rhs;
		final Rational lhsValue = convertConstantTermToRational(lhsConst);
		final Rational rhsValue = convertConstantTermToRational(rhsConst);
		if (!lhsValue.getClass().isAssignableFrom(rhsValue.getClass())
				&& rhsValue.getClass().isAssignableFrom(lhs.getClass())) {
			throw new UnsupportedOperationException("Incompatible classes. " + "First value is "
					+ lhsValue.getClass().getSimpleName() + " second value is " + rhsValue.getClass().getSimpleName());
		}
		if (lhsValue.equals(rhsValue)) {
			return script.term("true");
		}
		return script.term("false");
	}
	
	/**
	 * Returns the equality ("=" lhs rhs), for inputs of array sort. 
	 * If the term if of the form ("=" a ("store" a k v)) it is simplified to
	 * ("=" ("select" a k) v).
	 * Rationale: the latter term is simpler than the first term for our algorithms
	 */
	private static Term arrayEquality(final Script script, final Term lhs, final Term rhs) {
		if (!lhs.getSort().isArraySort()) {
			throw new UnsupportedOperationException("need array sort");
		}
		if (!rhs.getSort().isArraySort()) {
			throw new UnsupportedOperationException("need array sort");
		}
		if (lhs instanceof ApplicationTerm) {
			final ApplicationTerm appLhs = (ApplicationTerm) lhs;
			if (appLhs.getFunction().getName().equals("store")) {
				if (appLhs.getParameters()[0] == rhs) {
					return setArrayCellValue(script, appLhs.getParameters()[0], appLhs.getParameters()[1],
							appLhs.getParameters()[2]);
				}
			}
		}
		if (rhs instanceof ApplicationTerm) {
			final ApplicationTerm appRhs = (ApplicationTerm) rhs;
			if (appRhs.getFunction().getName().equals("store")) {
				if (appRhs.getParameters()[0] == lhs) {
					return setArrayCellValue(script, appRhs.getParameters()[0], appRhs.getParameters()[1],
							appRhs.getParameters()[2]);
				}
			}
		}
		return script.term("=", lhs, rhs);
	}

	/**
	 * @return ("=" ("select" array index) value)
	 */
	private static Term setArrayCellValue(final Script script, final Term array, final Term index, final Term value) {
		final Term select = script.term("select", array, index);
		return SmtUtils.binaryEquality(script, select, value);
	}

	public static List<Term> substitutionElementwise(final List<Term> subtituents, final Substitution subst) {
		final List<Term> result = new ArrayList<>();
		for (int i = 0; i < subtituents.size(); i++) {
			result.add(subst.transform(subtituents.get(i)));
		}
		return result;
	}

	/**
	 * Removes vertical bars from a String. In SMT-LIB identifiers can be quoted using | (vertical bar) and vertical
	 * bars must not be nested.
	 */
	public static String removeSmtQuoteCharacters(final String string) {
		final String result = string.replaceAll("\\|", "");
		return result;
	}

	public static Map<Term, Term> termVariables2Constants(final Script script,
			final Collection<TermVariable> termVariables, final boolean declareConstants) {
		final Map<Term, Term> mapping = new HashMap<>();
		for (final TermVariable tv : termVariables) {
			final Term constant = termVariable2constant(script, tv, declareConstants);
			mapping.put(tv, constant);
		}
		return mapping;
	}

	public static Term termVariable2constant(final Script script, final TermVariable tv,
			final boolean declareConstant) {
		final String name = removeSmtQuoteCharacters(tv.getName());
		if (declareConstant) {
			final Sort resultSort = tv.getSort();
			script.declareFun(name, new Sort[0], resultSort);
		}
		return script.term(name);
	}

	/**
	 * Returns true, iff the term contains an application of the given functionName
	 */
	public static boolean containsFunctionApplication(final Term term, final String functionName) {
		return containsFunctionApplication(term, Arrays.asList(functionName));
	}

	/**
	 * Returns true, iff the term contains an application of at least one of the the given functionNames
	 */
	public static boolean containsFunctionApplication(final Term term, final Iterable<String> functionNames) {
		for (final String f : functionNames) {
			if (!new ApplicationTermFinder(f, true).findMatchingSubterms(term).isEmpty()) {
				return true;
			}
		}
		return false;
	}

	public static boolean containsArrayVariables(final Term... terms) {
		for (final Term term : terms) {
			for (final TermVariable tv : term.getFreeVars()) {
				if (tv.getSort().isArraySort()) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Returns true, iff the term is array-free. This is the case, if no array variables, no select- and no
	 * store-expressions are found in it.
	 */
	public static boolean isArrayFree(final Term term) {
		return !containsArrayVariables(term) && !containsFunctionApplication(term, Arrays.asList("select", "store"));
	}

	/**
	 * Returns true, iff the term contains an UF-application
	 */
	public static boolean containsUninterpretedFunctionApplication(final Term term) {
		for (final NonTheorySymbol<?> s : new NonTheorySymbolFinder().findNonTheorySymbols(term)) {
			if (s instanceof NonTheorySymbol.Function) {
				return true;
			}
		}
		return false;
	}

	public static boolean isFalse(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fun = appTerm.getFunction();
			return "false".equals(fun.getApplicationString());
		}
		return false;
	}

	public static boolean isTrue(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			final FunctionSymbol fun = appTerm.getFunction();
			return "true".equals(fun.getApplicationString());
		}
		return false;
	}

	/**
	 * A constant is an ApplicationTerm with zero parameters whose function symbol is not intern.
	 */
	public static boolean isConstant(final Term term) {
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) term;
			return appTerm.getParameters().length == 0 && !appTerm.getFunction().isIntern();
		}
		return false;
	}

	/**
	 * Returns true iff the given term is an atomic formula, which means it does not contain any logical symbols (and,
	 * or, not, quantifiers)
	 */
	public static boolean isAtomicFormula(final Term term) {
		if (isTrue(term) || isFalse(term) || isConstant(term)) {
			return true;
		}
		if (term instanceof ApplicationTerm) {
			return !allParamsAreBool((ApplicationTerm) term);
		}
		return term instanceof TermVariable;
	}

	/**
	 * Returns true iff the given term is in NNF (only {@code and}, {@code or} and {@code not} as logical operators,
	 * where only atoms occurs after a {@code not}).
	 */
	public static boolean isNNF(final Term term) {
		for (final String f : Arrays.asList("=", "=>", "xor", "distinct", "ite")) {
			for (final ApplicationTerm a : new ApplicationTermFinder(f, true).findMatchingSubterms(term)) {
				if (allParamsAreBool(a)) {
					return false;
				}
			}
		}
		for (final ApplicationTerm a : new ApplicationTermFinder("not", true).findMatchingSubterms(term)) {
			if (!isAtomicFormula(a.getParameters()[0])) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Return all free TermVariables that occur in a set of Terms.
	 */
	public static Set<TermVariable> getFreeVars(final Collection<Term> terms) {
		final Set<TermVariable> freeVars = new HashSet<>();
		for (final Term term : terms) {
			freeVars.addAll(Arrays.asList(term.getFreeVars()));
		}
		return freeVars;
	}

	public static Term and(final Script script, final Term... terms) {
		return Util.and(script, terms);
	}

	public static Term and(final Script script, final Collection<Term> terms) {
		return Util.and(script, terms.toArray(new Term[terms.size()]));
	}
	
	public static Term or(final Script script, final Term... terms) {
		return Util.or(script, terms);
	}

	public static Term or(final Script script, final Collection<Term> terms) {
		return Util.or(script, terms.toArray(new Term[terms.size()]));
	}
	
	public static Term and_NewVersion(final Script script, final Collection<Term> terms) {
		final Set<Term> resultJuncts = new HashSet<>();
		final Set<Term> negativeJuncts = new HashSet<>();
		final String connective = "and";
		final Predicate<Term> isNeutral = (x -> SmtUtils.isTrue(x));
		final Predicate<Term> isAbsorbing = (x -> SmtUtils.isFalse(x));
		final boolean resultIsAbsorbingElement = recursiveAndOrSimplificationHelper(script, connective, isNeutral,
				isAbsorbing, terms, resultJuncts, negativeJuncts);
		if (resultIsAbsorbingElement) {
			return script.term("false");
		} else {
			if (resultJuncts.isEmpty()) {
				return script.term("true");
			} else if (resultJuncts.size() == 1) {
				return resultJuncts.iterator().next();
			} else {
				return script.term(connective, resultJuncts.toArray(new Term[resultJuncts.size()]));
			}
		}
	}
	
	public static Term or_NewVersion(final Script script, final Collection<Term> terms) {
		final Set<Term> resultJuncts = new HashSet<>();
		final Set<Term> negativeJuncts = new HashSet<>();
		final String connective = "or";
		final Predicate<Term> isNeutral = (x -> SmtUtils.isFalse(x));
		final Predicate<Term> isAbsorbing = (x -> SmtUtils.isTrue(x));
		final boolean resultIsAbsorbingElement = recursiveAndOrSimplificationHelper(script, connective, isNeutral,
				isAbsorbing, terms, resultJuncts, negativeJuncts);
		if (resultIsAbsorbingElement) {
			return script.term("true");
		} else {
			if (resultJuncts.isEmpty()) {
				return script.term("false");
			} else if (resultJuncts.size() == 1) {
				return resultJuncts.iterator().next();
			} else {
				return script.term(connective, resultJuncts.toArray(new Term[resultJuncts.size()]));
			}
		}
	}

	/**
	 * Auxiliary method for constructing simplified versions of conjunctions and disjunctions.
	 * Does the following simplications
	 * <ul>
	 *   <li> if some junct is neutral element, we can omit it
	 *   (e.g., we can drop "true" from conjunctions)
	 *   <li> if some junct is absorbing element, result is equivalent to absorbing element
	 *   (e.g., "x=0 /\ false" is equivalent to "false")
	 *   <li> if some junct is has the same connective, we can flatten it
	 *   (e.g., "((A /\ B) /\ C)" is equivalent to "(A /\ B /\ C)")
	 *   <li> if some junct and its negation occur, the result is equivalent to the absorbing element
	 *   (e.g., "A /\ (not A)" is equivalent to "false")
	 *   <li> if some junct occurs twice we can drop one occurrence.
	 *   (e.g., "A /\ A" is equivalent to "A")
	 * </ul>
	 * @param connective either "and" or "or"
	 * @param isNeutral {@link Predicate} that is true iff input is the neutral element wrt. the connective
	 * 			("true" is neutral for "and", "false" is neutral for "or")
	 * @param isAbsorbing {@link Predicate} that is true iff input is the absorbing element wrt. the connective
	 * 			("false" is absorbing for "and", "true" is absorbing for "or")
	 * @param inputJuncts disjuncts or conjuncts that are the input to this simplification
	 * @param resultJuncts disjuncts or conjuncts that will belong to the final output
	 * @param negatedJuncts arguments of juncts whose connective is "not"
	 * @return true iff we detected that the result is equivalent to the absorbing element of the connective
	 */
	private static boolean recursiveAndOrSimplificationHelper(final Script script, final String connective,
			final Predicate<Term> isNeutral, final Predicate<Term> isAbsorbing, final Collection<Term> inputJuncts,
			final Set<Term> resultJuncts, final Set<Term> negatedJuncts) {
		for (final Term junct : inputJuncts) {
			if (isNeutral.test(junct)) {
				// do nothing, junct will not contribute to result
				continue;
			} else if (isAbsorbing.test(junct)) {
				// result will be equivalent to absorbing element
				return true;
			} else {
				if (junct instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) junct;
					if (appTerm.getFunction().getName().equals(connective)) {
						// current junct has same connective as result
						// descend recusively to check and add its subjuncts
						final boolean resultIsAbsorbingElement = recursiveAndOrSimplificationHelper(script, connective,
								isNeutral, isAbsorbing, Arrays.asList(appTerm.getParameters()), resultJuncts, negatedJuncts);
						if (resultIsAbsorbingElement) {
							return true;
						} else {
							// the recursive all added all subjuncts,
							// no need to add the junct itself
							continue;
						}
					} else if (appTerm.getFunction().getName().equals("not")) {
						if (resultJuncts.contains(appTerm.getParameters()[0])) {
							// we already have the argument of this not term in the resultJuncts, 
							// hence the result will be equivalent to the absorbing element
							return true;
						} else {
							negatedJuncts.add(appTerm.getParameters()[0]);
						}
					}
				} 
			}
			if (negatedJuncts.contains(junct)) {
				// we already have the negation of this junct in the resultJuncts, 
				// hence the result will be equivalent to the absorbing element
				return true;
			} else {
				resultJuncts.add(junct);
			}
		}
		return false;
	}

	/**
	 * @return term that is equivalent to lhs <= rhs
	 */
	public static Term leq(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "<=", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs >= rhs
	 */
	public static Term geq(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, ">=", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs < rhs
	 */
	public static Term less(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, "<", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs > rhs
	 */
	public static Term greater(final Script script, final Term lhs, final Term rhs) {
		return comparison(script, ">", lhs, rhs);
	}

	/**
	 * @return term that is equivalent to lhs X rhs where X is either leq, less, geq, or greater.
	 */
	private static Term comparison(final Script script, final String functionSymbol, final Term lhs, final Term rhs) {
		final Term rawTerm = script.term(functionSymbol, lhs, rhs);
		try {
			final AffineRelation ar = new AffineRelation(script, rawTerm);
			return ar.positiveNormalForm(script);
		} catch (final NotAffineException e) {
			return rawTerm;
		}
	}

	/**
	 * Declare and return a new constant. A constant is a 0-ary application term.
	 *
	 * @param name
	 *            name of the resulting constant
	 * @param sort
	 *            the sort of the resulting constant
	 * @return resulting constant as a ApplicationTerm
	 * @throws SMTLIBException
	 *             if declaration of constant fails, e.g. the name is already defined
	 */
	public static ApplicationTerm buildNewConstant(final Script script, final String name, final String sortname)
			throws SMTLIBException {
		script.declareFun(name, new Sort[0], script.sort(sortname));
		return (ApplicationTerm) script.term(name);
	}

	/**
	 * Convert a BigDecimal into a Rational. Stolen from Jochen's code
	 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.ConvertFormula.
	 */
	private static Rational decimalToRational(final BigDecimal d) {
		Rational rat;
		if (d.scale() <= 0) {
			final BigInteger num = d.toBigInteger();
			rat = Rational.valueOf(num, BigInteger.ONE);
		} else {
			final BigInteger num = d.unscaledValue();
			final BigInteger denom = BigInteger.TEN.pow(d.scale());
			rat = Rational.valueOf(num, denom);
		}
		return rat;
	}

	/**
	 * Convert a constant term to Rational.
	 *
	 * @param ct
	 *            constant term that represents a Rational
	 * @return Rational from the value of ct
	 * @throws IllegalArgumentException
	 *             if ct does not represent a Rational.
	 * @deprecated replace this method by convertConstantTermToRational()
	 */
	@Deprecated
	public static Rational convertCT(final ConstantTerm ct) throws IllegalArgumentException {
		if (SmtSortUtils.isRealSort(ct.getSort())) {
			if (ct.getValue() instanceof Rational) {
				return (Rational) ct.getValue();
			} else if (ct.getValue() instanceof BigDecimal) {
				return decimalToRational((BigDecimal) ct.getValue());
			} else {
				throw new UnsupportedOperationException("ConstantTerm's value has to be either Rational or BigDecimal");
			}
		} else if (SmtSortUtils.isIntSort(ct.getSort())) {
			if (ct.getValue() instanceof Rational) {
				return (Rational) ct.getValue();
			}
			final Rational r = Rational.valueOf((BigInteger) ct.getValue(), BigInteger.ONE);
			return r;
		} else {
			throw new IllegalArgumentException("Trying to convert a ConstantTerm of unknown sort." + ct);
		}
	}

	/**
	 * Construct term but simplify it using lightweight simplification techniques if applicable.
	 */
	public static Term termWithLocalSimplification(final Script script, final String funcname,
			final BigInteger[] indices, final Term... params) {
		final Term result;
		switch (funcname) {
		case "and":
			result = SmtUtils.and(script, params);
			break;
		case "or":
			result = SmtUtils.or(script, params);
			break;
		case "not":
			if (params.length != 1) {
				throw new IllegalArgumentException("no not term");
			}
			result = SmtUtils.not(script, params[0]);
			break;
		case "=":
			if (params.length != 2) {
				throw new UnsupportedOperationException("not yet implemented");
			}
			result = binaryEquality(script, params[0], params[1]);
			break;
		case "distinct":
			if (params.length != 2) {
				throw new UnsupportedOperationException("not yet implemented");
			}
			result = SmtUtils.distinct(script, params[0], params[1]);
			break;
		case "=>":
			result = Util.implies(script, params);
			break;
		case "ite":
			if (params.length != 3) {
				throw new IllegalArgumentException("no ite");
			}
			result = Util.ite(script, params[0], params[1], params[2]);
			break;
		case "+":
		case "bvadd":
			result = SmtUtils.sum(script, funcname, params);
			break;
		case "div":
			if (params.length != 2) {
				throw new IllegalArgumentException("no div");
			}
			result = div(script, params[0], params[1]);
			break;
		case "mod":
			if (params.length != 2) {
				throw new IllegalArgumentException("no mod");
			}
			result = mod(script, params[0], params[1]);
			break;
		case ">=":
		case "<=":
		case ">":
		case "<":
			if (params.length != 2) {
				throw new IllegalArgumentException("no comparison");
			}
			result = comparison(script, funcname, params[0], params[1]);
			break;
		// case "store": {
		// final Term array = params[0];
		// final Term idx = params[1];
		// final Term nestedIdx = getArrayStoreIdx(array);
		// if (nestedIdx != null) {
		// // Check for store-over-store
		// if (nestedIdx.equals(idx)) {
		// // Found store-over-store => ignore inner store
		// final ApplicationTerm appArray = (ApplicationTerm) array;
		// result = script.term(funcname,
		// appArray.getParameters()[0], params[1], params[2]);
		// } else {
		// result = script.term(funcname, indices, null, params);
		// }
		// } else {
		// result = script.term(funcname, indices, null, params);
		// }
		// break;
		// }
		// case "select": {
		// final Term array = params[0];
		// final Term idx = params[1];
		// final Term nestedIdx = getArrayStoreIdx(array);
		// if (nestedIdx != null) {
		// // Check for store-over-store
		// if (nestedIdx.equals(idx)) {
		// // Found store-over-store => ignore inner store
		// final ApplicationTerm appArray = (ApplicationTerm) array;
		// // => transform into value
		// result = appArray.getParameters()[2];
		// } else {
		// result = script.term(funcname, indices, null, params);
		// }
		// } else {
		// result = script.term(funcname, indices, null, params);
		// }
		// break;
		// }
		case "zero_extend":
		case "extract":
		case "bvsub":
		case "bvmul":
		case "bvudiv":
		case "bvurem":
		case "bvsdiv":
		case "bvsrem":
		case "bvand":
		case "bvor":
		case "bvxor":
		case "bvnot":
		case "bvneg":
		case "bvshl":
		case "bvlshr":
		case "bvashr":
		case "bvult":
		case "bvule":
		case "bvugt":
		case "bvuge":
		case "bvslt":
		case "bvsle":
		case "bvsgt":
		case "bvsge":
			result = BitvectorUtils.termWithLocalSimplification(script, funcname, indices, params);
			break;
		default:
			// if (BitvectorUtils.allTermsAreBitvectorConstants(params)) {
			// throw new AssertionError("wasted optimization " + funcname);
			// }
			result = script.term(funcname, indices, null, params);
			break;
		}
		return result;
	}

	/**
	 * @return idx if array has form (store a idx v) return null if array has a different form
	 */
	private final static Term getArrayStoreIdx(final Term array) {
		if (array instanceof ApplicationTerm) {
			final ApplicationTerm appArray = (ApplicationTerm) array;
			final FunctionSymbol arrayFunc = appArray.getFunction();
			if (arrayFunc.isIntern() && arrayFunc.getName().equals("store")) {
				// (store a i v)
				return appArray.getParameters()[1];
			}
		}
		return null;
	}

	/**
	 * Returns a possibly simplified version of the Term (div dividend divisor). If dividend and divisor are both
	 * literals the returned Term is a literal which is equivalent to the result of the operation
	 */
	public static Term div(final Script script, final Term dividend, final Term divisor) {
		if (dividend instanceof ConstantTerm && dividend.getSort().isNumericSort() && divisor instanceof ConstantTerm
				&& divisor.getSort().isNumericSort()) {
			final Rational dividentAsRational = convertConstantTermToRational((ConstantTerm) dividend);
			final Rational divisorAsRational = convertConstantTermToRational((ConstantTerm) divisor);
			final Rational quotientAsRational = dividentAsRational.div(divisorAsRational);
			Rational result;
			if (divisorAsRational.isNegative()) {
				result = quotientAsRational.ceil();
			} else {
				result = quotientAsRational.floor();
			}
			return result.toTerm(dividend.getSort());
		}
		return script.term("div", dividend, divisor);
	}

	/**
	 * Returns a possibly simplified version of the Term (mod dividend divisor). If dividend and divisor are both
	 * literals the returned Term is a literal which is equivalent to the result of the operation. If only the divisor
	 * is a literal we apply modulo to all coefficients of the dividend (helpful simplification in case where
	 * coefficient becomes zero).
	 */
	public static Term mod(final Script script, final Term divident, final Term divisor) {
		final AffineTerm affineDivident = (AffineTerm) new AffineTermTransformer(script).transform(divident);
		final AffineTerm affineDivisor = (AffineTerm) new AffineTermTransformer(script).transform(divisor);
		if (affineDivident.isErrorTerm() || affineDivisor.isErrorTerm()) {
			return script.term("mod", divident, divisor);
		}
		if (affineDivisor.isZero()) {
			// pass the problem how to deal with division by zero to the
			// subsequent analysis
			return script.term("mod", divident, divisor);
		}
		if (affineDivisor.isConstant()) {
			final BigInteger bigIntDivisor = toInt(affineDivisor.getConstant());
			if (affineDivident.isConstant()) {
				final BigInteger bigIntDivident = toInt(affineDivident.getConstant());
				final BigInteger modulus = BoogieUtils.euclideanMod(bigIntDivident, bigIntDivisor);
				return script.numeral(modulus);
			}
			final Term simplifiedNestedModulo = simplifyNestedModulo(script, divident, bigIntDivisor);
			if (simplifiedNestedModulo == null) {
				// no simplification was possible, continue
			} else {
				return simplifiedNestedModulo;
			}
			final AffineTerm moduloApplied =
					AffineTerm.applyModuloToAllCoefficients(script, affineDivident, bigIntDivisor);
			return script.term("mod", moduloApplied.toTerm(script), affineDivisor.toTerm(script));
		}
		return script.term("mod", affineDivident.toTerm(script), affineDivisor.toTerm(script));
	}

	/**
	 * Check if a divident of an modulo operation with constant divisor is itself a modulo operation. If this is the
	 * case we might be able to apply some simplifications.
	 *
	 * @param divident
	 *            Divident of an outer modulo operation
	 * @param bigIntDivisor
	 *            Divisor of an outer modulo operation
	 * @return Simplified version of the outer modulo operation or null (null in case where we could not apply
	 *         simplifications.)
	 */
	private static Term simplifyNestedModulo(final Script script, final Term divident, final BigInteger bigIntDivisor) {
		if (divident instanceof ApplicationTerm) {
			final ApplicationTerm appTerm = (ApplicationTerm) divident;
			if ("mod".equals(appTerm.getFunction().getApplicationString())) {
				final Term innerDivident = appTerm.getParameters()[1];
				final AffineTerm affineInnerDivisor =
						(AffineTerm) new AffineTermTransformer(script).transform(innerDivident);
				if (!affineInnerDivisor.isErrorTerm() && affineInnerDivisor.isConstant()) {
					final BigInteger bigIntInnerDivisor = toInt(affineInnerDivisor.getConstant());
					if (bigIntInnerDivisor.mod(bigIntDivisor).equals(BigInteger.ZERO)
							|| bigIntDivisor.mod(bigIntInnerDivisor).equals(BigInteger.ZERO)) {
						final BigInteger min = bigIntInnerDivisor.min(bigIntDivisor);
						final Term innerDivisor = appTerm.getParameters()[0];
						final Term result = mod(script, innerDivisor, script.numeral(min));
						return result;
					}
				}
			}
		}
		return null;
	}

	public static BigInteger toInt(final Rational integralRational) {
		if (!integralRational.isIntegral()) {
			throw new IllegalArgumentException("divident has to be integral");
		}
		if (!integralRational.denominator().equals(BigInteger.ONE)) {
			throw new IllegalArgumentException("denominator has to be zero");
		}
		return integralRational.numerator();
	}

	public static Rational toRational(final BigInteger bigInt) {
		return Rational.valueOf(bigInt, BigInteger.ONE);
	}

	public static Term rational2Term(final Script script, final Rational rational, final Sort sort) {
		if (SmtSortUtils.isNumericSort(sort)) {
			return rational.toTerm(sort);
		} else if (SmtSortUtils.isBitvecSort(sort)) {
			if (rational.isIntegral() && rational.isRational()) {
				return BitvectorUtils.constructTerm(script, rational.numerator(), sort);
			}
			throw new IllegalArgumentException("unable to convert rational to bitvector if not integer");
		} else {
			throw new AssertionError("unknown sort " + sort);
		}
	}

	/**
	 * Check if {@link Term} which may contain free {@link TermVariable}s is satisfiable with respect to the current
	 * assertion stack of {@link Script}. Compute unsat core if unsatisfiable. Use {@link LoggingScript} to see the
	 * input. TODO: Show values of satisfying assignment (including array access) if satisfiable.
	 *
	 * @param term
	 *            may contain free variables
	 */
	public static LBool checkSatDebug(final Script script, final Term term, final ILogger logger) {
		script.push(1);
		try {
			final TermVariable[] vars = term.getFreeVars();
			final Map<Term, Term> substitutionMapping = new HashMap<>();
			for (final TermVariable var : vars) {
				final Term substituent = termVariable2PseudofreshConstant(script, var);
				substitutionMapping.put(var, substituent);
			}
			final Map<Term, Term> ucMapping = new HashMap<>();
			final Term[] conjuncts = getConjuncts(term);
			for (int i = 0; i < conjuncts.length; i++) {
				final Term conjunct = new Substitution(script, substitutionMapping).transform(conjuncts[i]);
				final String name = "conjunct" + i;
				final Annotation annot = new Annotation(":named", name);
				final Term annotTerm = script.annotate(conjunct, annot);
				ucMapping.put(script.term(name), conjuncts[i]);
				script.assertTerm(annotTerm);
			}
			final LBool result = script.checkSat();
			if (result == LBool.UNSAT) {
				final Term[] ucTerms = script.getUnsatCore();
				for (final Term ucTerm : ucTerms) {
					final Term conjunct = ucMapping.get(ucTerm);
					logger.debug("in uc: " + conjunct);
				}
			}
			script.pop(1);
			return result;
		} catch (final Exception e) {
			// unable to recover because assertion stack is modified
			// doing the script.pop(1) in finally block does not make sense
			// since the solver might not be able to respond this will raise
			// another Exception, and we will not see Exception e any more.
			throw new AssertionError("Exception during satisfiablity check: " + e.getMessage());
		}
	}

	private static Term termVariable2PseudofreshConstant(final Script script, final TermVariable tv) {
		final String name = tv.getName() + "_const_" + tv.hashCode();
		final Sort resultSort = tv.getSort();
		script.declareFun(name, new Sort[0], resultSort);
		return script.term(name);
	}

	/**
	 * Convert a {@link ConstantTerm} which has numeric {@link Sort} into a {@literal Rational}.
	 *
	 * @return a Rational which represents the input constTerm
	 * @throws UnsupportedOperationException
	 *             if ConstantTerm cannot converted to Rational
	 */
	public static Rational convertConstantTermToRational(final ConstantTerm constTerm) {
		Rational rational;
		assert SmtSortUtils.isNumericSort(constTerm.getSort());
		final Object value = constTerm.getValue();
		if (SmtSortUtils.isIntSort(constTerm.getSort())) {
			if (value instanceof BigInteger) {
				rational = Rational.valueOf((BigInteger) value, BigInteger.ONE);
			} else if (value instanceof Rational) {
				rational = (Rational) value;
			} else {
				throw new UnsupportedOperationException();
			}
		} else if (SmtSortUtils.isRealSort(constTerm.getSort())) {
			if (value instanceof BigDecimal) {
				rational = decimalToRational((BigDecimal) value);
			} else if (value instanceof Rational) {
				rational = (Rational) value;
			} else {
				throw new UnsupportedOperationException();
			}
		} else {
			throw new UnsupportedOperationException();
		}
		return rational;
	}

	/**
	 * @return true iff tv does not occur in appTerm, or appTerm has two parameters, tv is the left parameter and tv
	 *         does not occur in the right prarameter.
	 */
	public static boolean occursAtMostAsLhs(final TermVariable tv, final ApplicationTerm appTerm) {
		if (appTerm.getParameters().length != 2) {
			return !Arrays.asList(appTerm.getFreeVars()).contains(tv);
		}
		if (Arrays.asList(appTerm.getParameters()[1].getFreeVars()).contains(tv)) {
			// occurs on rhs
			return false;
		}
		if (appTerm.getParameters()[0].equals(tv)) {
			return true;
		}
		return !Arrays.asList(appTerm.getParameters()[0].getFreeVars()).contains(tv);
	}

	/**
	 * Returns quantified formula. Drops quantifiers for variables that do not occur in formula. If subformula is
	 * quantified formula with same quantifier both are merged.
	 */
	public static Term quantifier(final Script script, final int quantifier, final Collection<TermVariable> vars,
			final Term body) {
		if (vars.isEmpty()) {
			return body;
		}
		final Collection<TermVariable> resultVars = filterToVarsThatOccurFreelyInTerm(vars, body);
		if (resultVars.isEmpty()) {
			return body;
		}
		final QuantifiedFormula innerQuantifiedFormula = isQuantifiedFormulaWithSameQuantifier(quantifier, body);
		if (innerQuantifiedFormula == null) {
			return script.quantifier(quantifier, resultVars.toArray(new TermVariable[resultVars.size()]), body);
		}
		final Set<TermVariable> resultQuantifiedVars =
				new HashSet<>(Arrays.asList(innerQuantifiedFormula.getVariables()));
		resultQuantifiedVars.addAll(vars);
		return script.quantifier(quantifier,
				resultQuantifiedVars.toArray(new TermVariable[resultQuantifiedVars.size()]),
				innerQuantifiedFormula.getSubformula());
	}

	/**
	 * Returns a new {@link Set} that contains all variables that are contained in vars and occur freely in term.
	 */
	public static Set<TermVariable> filterToVarsThatOccurFreelyInTerm(final Collection<TermVariable> vars,
			final Term term) {
		final HashSet<TermVariable> result = new HashSet<>();
		for (final TermVariable tv : Arrays.asList(term.getFreeVars())) {
			if (vars.contains(tv)) {
				result.add(tv);
			}
		}
		return result;
	}

	/**
	 * If term is QuantifiedFormula whose quantifier is quant we return term as QuantifiedFormula otherwise we return
	 * null;
	 */
	public static QuantifiedFormula isQuantifiedFormulaWithSameQuantifier(final int quant, final Term term) {
		if (term instanceof QuantifiedFormula) {
			final QuantifiedFormula quantifiedFormula = (QuantifiedFormula) term;
			if (quant == quantifiedFormula.getQuantifier()) {
				return quantifiedFormula;
			}
		}
		return null;
	}

	/**
	 * Given a quantified formula, rename all variables that are bound by the quantifier and occur in the set toRename
	 * to fresh variables.
	 *
	 * @param freshVarPrefix
	 *            prefix of the fresh variables
	 */
	public static Term renameQuantifiedVariables(final ManagedScript mgdScript, final QuantifiedFormula qFormula,
			final Set<TermVariable> toRename, final String freshVarPrefix) {
		final Map<Term, Term> substitutionMapping = new HashMap<>();
		for (final TermVariable var : toRename) {
			final TermVariable freshVariable = mgdScript.constructFreshTermVariable(freshVarPrefix, var.getSort());
			substitutionMapping.put(var, freshVariable);
		}
		final Term newBody = new Substitution(mgdScript, substitutionMapping).transform(qFormula.getSubformula());

		final TermVariable[] vars = new TermVariable[qFormula.getVariables().length];
		for (int i = 0; i < vars.length; i++) {
			final TermVariable renamed = (TermVariable) substitutionMapping.get(qFormula.getVariables()[i]);
			if (renamed != null) {
				vars[i] = renamed;
			} else {
				vars[i] = qFormula.getVariables()[i];
			}
		}
		final Term result = mgdScript.getScript().quantifier(qFormula.getQuantifier(), vars, newBody);
		return result;
	}

	/**
	 * @return true iff term is {@link ApplicationTerm} with functionName.
	 */
	public static boolean isFunctionApplication(final Term term, final String functionName) {
		if (term instanceof ApplicationTerm) {
			final FunctionSymbol fun = ((ApplicationTerm) term).getFunction();
			if (fun.getName().equals(functionName)) {
				return true;
			}
		}
		return false;
	}

	/**
	 * @return logically equivalent term in disjunctive normal form (DNF)
	 */
	public static Term toDnf(final IUltimateServiceProvider services, final ManagedScript mgdScript, final Term term,
			final XnfConversionTechnique xnfConversionTechnique) {
		final Term result;
		switch (xnfConversionTechnique) {
		case BDD_BASED:
			result = new SimplifyBdd(services, mgdScript).transformToDNF(term);
			break;
		case BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION:
			result = new DnfTransformer(mgdScript, services).transform(term);
			break;
		default:
			throw new AssertionError(ERROR_MESSAGE_UNKNOWN_ENUM_CONSTANT + xnfConversionTechnique);
		}
		return result;
	}

	/**
	 * @return logically equivalent term in negation normal form (NNF)
	 */
	public static Term toNnf(final IUltimateServiceProvider services, final ManagedScript mgdScript, final Term term) {
		return new NnfTransformer(mgdScript, services, QuantifierHandling.PULL).transform(term);
	}

	/**
	 * @return logically equivalent term in conjunctive normal form (CNF)
	 */
	public static Term toCnf(final IUltimateServiceProvider services, final ManagedScript mgdScript, final Term term,
			final XnfConversionTechnique xnfConversionTechnique) {
		final Term result;
		switch (xnfConversionTechnique) {
		case BDD_BASED:
			result = new SimplifyBdd(services, mgdScript).transformToCNF(term);
			break;
		case BOTTOM_UP_WITH_LOCAL_SIMPLIFICATION:
			result = new CnfTransformer(mgdScript, services).transform(term);
			break;
		default:
			throw new AssertionError(ERROR_MESSAGE_UNKNOWN_ENUM_CONSTANT + xnfConversionTechnique);
		}
		return result;
	}

	/**
	 * Returns true for {@link Sorts} for which we can obtain values. E.g. for arrays we cannot get values that our
	 * analysis can process, since arrays are infinite in general. However, if the range Sort of an array is bitvector
	 * sort we can get values for array cells (resp. the corresponding select term).
	 */
	public static boolean isSortForWhichWeCanGetValues(final Sort sort) {
		return SmtSortUtils.isNumericSort(sort) || SmtSortUtils.isBoolSort(sort) || SmtSortUtils.isBitvecSort(sort)
				|| SmtSortUtils.isFloatingpointSort(sort);
	}

	/**
	 * Get values from script and transform them try to simplify them.
	 *
	 * @param script
	 *            Script that is in a state where it can provide values, e.g., after a check-sat where the response was
	 *            sat.
	 * @param terms
	 *            Collection of term for which we want to have possible values in the current satisfying model
	 * @return Mapping that maps to each term for which we want a value a possible value in the current satisfying
	 *         model.
	 */
	public static Map<Term, Term> getValues(final Script script, final Collection<Term> terms) {
		if (terms.isEmpty()) {
			return Collections.emptyMap();
		}
		final Term[] asArray = terms.toArray(new Term[terms.size()]);
		final Map<Term, Term> mapFromSolver = script.getValue(asArray);
		/*
		 * Some solvers, e.g., Z3 return -1 not as a literal but as a unary minus of a positive literal. We use our
		 * affine term to obtain the negative literal.
		 */
		final Map<Term, Term> copyWithNiceValues = new HashMap<>();
		for (final Entry<Term, Term> entry : mapFromSolver.entrySet()) {
			copyWithNiceValues.put(entry.getKey(), makeAffineIfPossible(script, entry.getValue()));
		}
		return Collections.unmodifiableMap(copyWithNiceValues);
	}

	private static Term makeAffineIfPossible(final Script script, final Term term) {
		final AffineTerm affineTerm = (AffineTerm) new AffineTermTransformer(script).transform(term);
		if (affineTerm.isErrorTerm()) {
			return term;
		}
		return affineTerm.toTerm(script);
	}

	public static Term constructPositiveNormalForm(final Script script, final Term term) {
		final Term result = new AffineSubtermNormalizer(script).transform(term);
		assert Util.checkSat(script, script.term("distinct", term, result)) != LBool.SAT;
		return result;
	}

	/**
	 * @return the dual quantifier: - existential if input is universal, and - universal if input is existential
	 */
	public static int getOtherQuantifier(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return QuantifiedFormula.FORALL;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return QuantifiedFormula.EXISTS;
		} else {
			throw new AssertionError("unknown quantifier");
		}
	}

	/**
	 * @return "or" if input is existential quantifier and "and" if input is universal quantifier
	 */
	public static String getCorrespondingFiniteConnective(final int quantifier) {
		if (quantifier == QuantifiedFormula.EXISTS) {
			return "or";
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return "and";
		} else {
			throw new AssertionError("unknown quantifier");
		}
	}
}
