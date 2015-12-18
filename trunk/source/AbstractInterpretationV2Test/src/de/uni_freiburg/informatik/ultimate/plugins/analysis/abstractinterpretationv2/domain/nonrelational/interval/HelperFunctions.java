/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission 
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval;

import java.math.BigDecimal;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.model.boogie.ast.BinaryExpression.Operator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.evaluator.IEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainEvaluationResult;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalBinaryExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalSingletonValueExpressionEvaluator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalValue;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.util.LoggerInitializer;

/**
 * Helper functions for the interval test suite.
 * 
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 *
 */
public class HelperFunctions {
	protected static IntervalDomainValue createInterval(int lower, int upper) {
		return new IntervalDomainValue(new IntervalValue(new BigDecimal(lower)),
		        new IntervalValue(new BigDecimal(upper)));
	}

	protected static IntervalDomainValue createInterval() {
		return new IntervalDomainValue();
	}

	protected static IntervalBinaryExpressionEvaluator createBinaryEvaluator(IntervalDomainValue first,
	        IntervalDomainValue second, Operator operator) {

		final LoggerInitializer loggerInitializer = new LoggerInitializer();
		final Logger logger = loggerInitializer.getLogger(HelperFunctions.class.toGenericString());

		IntervalSingletonValueExpressionEvaluator value1Evaluator = new IntervalSingletonValueExpressionEvaluator(
		        first);
		IntervalSingletonValueExpressionEvaluator value2Evaluator = new IntervalSingletonValueExpressionEvaluator(
		        second);

		IntervalBinaryExpressionEvaluator binaryExpressionEvaluator = new IntervalBinaryExpressionEvaluator(logger);

		binaryExpressionEvaluator.setOperator(operator);
		binaryExpressionEvaluator.addSubEvaluator(value1Evaluator);
		binaryExpressionEvaluator.addSubEvaluator(value2Evaluator);

		return binaryExpressionEvaluator;
	}

	private static String getMethodName() {
		final StackTraceElement[] ste = Thread.currentThread().getStackTrace();

		return ste[4].getMethodName();
	}

	protected static boolean computeResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult, IntervalDomainValue evaluatorResult) {

		System.out.println(getMethodName());
		System.out.println("Result  : " + evaluatorResult.toString());
		System.out.println("Expected: " + expectedResult.toString());
		System.out.println();

		if (interval1.isBottom() || interval2.isBottom()) {
			return evaluatorResult.isEqualTo(expectedResult);
		}

		if (evaluatorResult.isBottom() && expectedResult.isBottom()) {
			return true;
		}

		if (evaluatorResult.isBottom() && !expectedResult.isBottom()) {
			return false;
		}

		final boolean lowerResult, upperResult;

		lowerResult = evaluatorResult.getLower().equals(expectedResult.getLower());
		upperResult = evaluatorResult.getUpper().equals(expectedResult.getUpper());

		return lowerResult && upperResult;
	}

	protected static boolean computeAdditionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> result = createBinaryEvaluator(interval1,
		        interval2, Operator.ARITHPLUS).evaluate(new IntervalDomainState());

		boolean ret = true;

		for (final IEvaluationResult<IntervalDomainEvaluationResult> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getResult().getEvaluatedValue());
		}

		return ret;
	}

	protected static boolean computeSubtractionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> result = createBinaryEvaluator(interval1,
		        interval2, Operator.ARITHMINUS).evaluate(new IntervalDomainState());

		boolean ret = true;

		for (final IEvaluationResult<IntervalDomainEvaluationResult> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getResult().getEvaluatedValue());
		}

		return ret;
	}

	protected static boolean computeMultiplicationResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final List<IEvaluationResult<IntervalDomainEvaluationResult>> result = createBinaryEvaluator(interval1,
		        interval2, Operator.ARITHMUL).evaluate(new IntervalDomainState());

		boolean ret = true;

		for (final IEvaluationResult<IntervalDomainEvaluationResult> res : result) {
			ret = ret && computeResult(interval1, interval2, expectedResult, res.getResult().getEvaluatedValue());
		}

		return ret;
	}

	protected static boolean computeIntersectionResult(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expectedResult) {

		final IntervalDomainValue result = interval1.intersect(interval2);

		return computeResult(interval1, interval2, expectedResult, result);
	}

	protected static boolean computeMergedInterval(IntervalDomainValue interval1, IntervalDomainValue interval2,
	        IntervalDomainValue expected) {

		final IntervalDomainValue computed = interval1.merge(interval2);

		return computeResult(interval1, interval2, expected, computed);
	}

	protected static boolean checkInclusion(IntervalDomainValue interval1, IntervalDomainValue interval2) {
		return interval1.isContainedIn(interval2);
	}
}
