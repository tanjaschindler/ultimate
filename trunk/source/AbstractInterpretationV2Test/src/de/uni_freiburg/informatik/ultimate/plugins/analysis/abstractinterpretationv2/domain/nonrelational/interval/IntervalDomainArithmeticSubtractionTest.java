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

import static org.junit.Assert.*;
import org.junit.Test;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainValue;

public class IntervalDomainArithmeticSubtractionTest {

	@Test
	public void testIntervalSimpleSubtraction() {
		
		// Interval [10, 20]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(10, 20);
		
		// Interval [10, 10]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(10, 10);
		
		// Expected Interval [0, 10]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval(0, 10);
		
		assertTrue(HelperFunctions.computeSubtractionResult(interval1, interval2, expectedResult));
	}
	
	@Test
	public void testIntervalNegativeSubtraction() {
		// Interval [1, 5]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 5);
		
		// Interval [-5, -1]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(-5, -1);
		
		// Expected Interval [0, 0]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval(2, 10);
		
		assertTrue(HelperFunctions.computeSubtractionResult(interval1, interval2, expectedResult));
	}
	
	@Test
	public void testIntervalMixedNegativeSubtraction() {
		// Interval [1, 5]
		IntervalDomainValue interval1 = HelperFunctions.createInterval(1, 5);
		
		// Interval [-5, -1]
		IntervalDomainValue interval2 = HelperFunctions.createInterval(-1, 5);
		
		// Expected Interval [0, 0]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval(-4, 6);
		
		assertTrue(HelperFunctions.computeSubtractionResult(interval1, interval2, expectedResult));
	}
	
	@Test
	public void testInfiniteIntervalSubtraction() {
		// Interval [-\infty, \infty]
		IntervalDomainValue interval1 = HelperFunctions.createInterval();
		
		// Interval [-\infty, \infty]
		IntervalDomainValue interval2 = HelperFunctions.createInterval();
		
		// Expected Interval [-\infty, \infty]
		IntervalDomainValue expectedResult = HelperFunctions.createInterval();
		
		assertTrue(HelperFunctions.computeSubtractionResult(interval1, interval2, expectedResult));
		
		
		// Interval [-\infty, \infty]
		IntervalDomainValue interval3 = HelperFunctions.createInterval();
		
		// Interval [-5, -1]
		IntervalDomainValue interval4 = HelperFunctions.createInterval(-5, -1);
		
		// Expected Interval [-\infty, \infty]
		IntervalDomainValue expectedResult2 = HelperFunctions.createInterval();
		
		assertTrue(HelperFunctions.computeSubtractionResult(interval3, interval4, expectedResult2));
		
		// Interval [10,20]
		IntervalDomainValue interval5 = HelperFunctions.createInterval(10, 20);
		
		// Expected Interval [-\infty, \infty]
		assertTrue(HelperFunctions.computeSubtractionResult(interval1, interval5, expectedResult));
	}
}
