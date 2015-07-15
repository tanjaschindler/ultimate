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
package de.uni_freiburg.informatik.ultimate.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.ReplacementVarFactory;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Replaces variables that have a used defined type by variables that have type
 * Int.
 * We detect these variables by their Sort. If a term does not have an
 * "internal" Sort, it originates from a user defined type.
 * 
 * @author Matthias Heizmann
 */
public class RewriteUserDefinedTypes extends RewriteTermVariables {
	public static final String s_Description = "Replace variables that have a used defined type";
	
	private static final String s_TermVariableSuffix = "udt";
	private static final String s_repVarSortName = "Int";
	
	@Override
	protected String getTermVariableSuffix() {
		return s_TermVariableSuffix;
	}
	@Override
	protected String getRepVarSortName() {
		return s_repVarSortName;
	}
	
	/**
	 * Create a new RewriteBooleans preprocessor
	 * @param rankVarCollector collecting the new in- and outVars
	 * @param script the Script for creating new variables
	 */
	public RewriteUserDefinedTypes(ReplacementVarFactory varFactory, Script script) {
		super(varFactory, script);
	}
	
	@Override
	protected boolean hasToBeReplaced(Term term) {
		return hasNonInternalSort(term);
	}

	/**
	 * return true iff sort of term is not an internal sort
	 */
	private static final boolean hasNonInternalSort(Term term) {
		return !term.getSort().getRealSort().isInternal();
	}
	
	@Override
	protected Term constructReplacementTerm(TermVariable newTv) {
		// return the new Tv
		return newTv;
	}

	
	@Override
	public String getDescription() {
		return s_Description;
	}
	
	/**
	 * TODO: at the moment we us the old definition.
	 * This is a problem if the variable indeed occurs in a ranking function.
	 * Solution: For each type we have to introduce an auxiliary uninterpreted
	 * function toInt(). We will then return toInt(definition).
	 * 
	 */
	@Override
	protected Term constructNewDefinitionForRankVar(RankVar oldRankVar) {
		Term definition = oldRankVar.getDefinition();
		return definition;
	}
	

}