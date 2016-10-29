/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.ModifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;


/**
 * Replace strict inequalities that compare terms of sort int by equivalent
 * non-strict inequalities. E.g., the term <i>x > 0</i> is replaced by the term
 * <i>x >= 1</i>.
 * 
 * @author Matthias Heizmann, Jan Leike
 */
public class RewriteStrictInequalities extends TransformerPreprocessor {
	
	public static final String s_Description = "Replace strict inequalities by non-strict inequalities";
	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	@Override
	protected boolean checkSoundness(Script script, ModifiableTransFormula oldTF,
			ModifiableTransFormula newTF) {
		final Term old_term = oldTF.getFormula();
		final Term new_term = newTF.getFormula();
		return LBool.SAT != Util.checkSat(script,
				script.term("distinct", old_term, new_term));
	}
	
	@Override
	protected TermTransformer getTransformer(Script script) {
		return new RewriteStrictInequalitiesTransformer(script);
	}
	
	/**
	 * Replace strict inequalities that compare terms of sort Int by equivalent
	 * non-strict inequalities.
	 *
	 */
	private class RewriteStrictInequalitiesTransformer extends TermTransformer {
		
		private final Script mScript;
		
		RewriteStrictInequalitiesTransformer(Script script) {
			assert script != null;
			mScript = script;
		}
		
		@Override
		protected void convert(Term term) {
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				final String functionSymbolName = appTerm.getFunction().getName();
				Term result = null;
				if (functionSymbolName.equals("<")) {
					result = computeCorrespondingInequality(appTerm);
				} else if (functionSymbolName.equals(">")) {
					result = computeCorrespondingInequality(appTerm);
				}
				if (result != null) {
					setResult(result);
					return;
				}
			}
			super.convert(term);
		}
		
		/**
		 * Requires that appTerm has function symbol "<" or ">" and that
		 * appTerm has two parameters.
		 * If the parameters are of Sort int, we return the corresponding 
		 * equivalent non-strict inequality.
		 * Otherwise we return null.
		 */
		private Term computeCorrespondingInequality(ApplicationTerm appTerm) {
			final String functionSymbolName = appTerm.getFunction().getName();
			if (appTerm.getParameters().length != 2) {
				throw new AssertionError("expected binary terms");
			}
			if (!appTerm.getParameters()[0].getSort().getName().equals("Int")) {
				return null;
			}
			final Term one = mScript.numeral(BigInteger.ONE);
			Term result;
			if (functionSymbolName.equals("<")) {
				result = mScript.term("<=",
						mScript.term("+",	appTerm.getParameters()[0], one), 
						appTerm.getParameters()[1]);
			} else if (functionSymbolName.equals(">")) {
				result = mScript.term(">=", 
						appTerm.getParameters()[0], 
						mScript.term("+", appTerm.getParameters()[1], one));
			} else {
				throw new AssertionError();
			}
			return result;
		}
	}
}
