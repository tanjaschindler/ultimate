package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.logic.simplification.SimplifyDDA;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt.PartialQuantifierElimination.EqualityInformation;

/**
 * 
 * TODO:
 * - elimination and output of remaining vars
 * - nested store
 * - storeTo and storeFrom (LBE)
 * - index equality testing
 * - documentation
 * @author Matthias Heizmann
 *
 */
public class ElimStore3 {
	
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);

	public ElimStore3(Script script) {
		super();
		m_Script = script;
	}
	
	private final int quantifier = QuantifiedFormula.EXISTS;
	private final Script m_Script;
	
	public Term elim(TermVariable oldArr, Term term, final Set<TermVariable> newAuxVars) {
		assert oldArr.getSort().isArraySort();
		Term[] conjuncts = PartialQuantifierElimination.getConjuncts(term);
		
		ArrayUpdate writeInto = null;
		ArrayUpdate writtenFrom = null;
		HashSet<Term> others = new HashSet<Term>();
		
		for (Term conjunct : conjuncts) {
			try {
				ArrayUpdate au = new ArrayUpdate(conjunct);
				if (au.getOldArray().equals(oldArr)) {
					if (writeInto != null) {
						throw new UnsupportedOperationException(
								"unsupported: write into several arrays");
					}
					writeInto = au;
					if (au.getNewArray().equals(oldArr)) {
						throw new UnsupportedOperationException(
								"unsupported: self update");
					}
				} else if (au.getNewArray().equals(oldArr)) {
					if (writtenFrom != null) {
						throw new UnsupportedOperationException(
								"unsupported: written from several arrayas");
					}
					writtenFrom = au;
					others.add(conjunct);
				} else {
					others.add(conjunct);
				}
			} catch (ArrayUpdateException e) {
				others.add(conjunct);
				assert (new ApplicationTermFinder("store")).
					findMatchingSubterms(conjunct).isEmpty() : "detected unsupported store";
			}
		}
		if (writtenFrom != null) {
			throw new UnsupportedOperationException("not yet implemented: written from");
		}
		
		Term othersT = Util.and(m_Script, others.toArray(new Term[0]));

		boolean write = (writeInto != null);
		
		Script script = m_Script;;
		IndicesAndValues iav = new IndicesAndValues(oldArr, conjuncts);

		SafeSubstitution subst = new SafeSubstitution(script, iav.getMapping());
		
		Term intermediateResult = subst.transform(othersT);
		if (write) {
			ArrayList<Term> additionalConjuncsFromStore = new ArrayList<Term>();
			for (int i=0; i<iav.getIndices().length; i++) {
				Term newSelect = buildMultiDimensionalSelect(writeInto.getNewArray(), iav.getIndices()[i]);
				IndexValueConnection ivc = new IndexValueConnection(iav.getIndices()
						[i], writeInto.getIndex(), iav.getValues()[i], newSelect, false);
				Term conjunct = ivc.getTerm();
				additionalConjuncsFromStore.add(conjunct);
				if (ivc.indexInequality() && !ivc.indexEquality()) {
					assert !ivc.indexInequality() : "term would be false!";
					// case where we have valueEquality hat is not true
					// do something useful...
					// e.g., mark newSelect as occurring or mark auxVar as 
					// equal to something
				}
			}
			Term newConjunctsFromStore = subst.transform(Util.and(script, additionalConjuncsFromStore.toArray(new Term[0])));
			Term newData = subst.transform(writeInto.getData());
			Term newWriteIndex[] = substitutionElementwise(writeInto.getIndex(), subst);
			Term writeSubstituent = m_Script.term("=", buildMultiDimensionalSelect(writeInto.getNewArray(), newWriteIndex), newData); 
			intermediateResult = Util.and(m_Script, intermediateResult, writeSubstituent, newConjunctsFromStore);
		}
		
		
		ArrayList<Term> additionalConjuncsFromSelect = new ArrayList<Term>();
		{
			Term[][] indices = new Term[iav.getIndices().length][];
			Term[] values = new Term[iav.getIndices().length];
			for (int i=0; i<iav.getIndices().length; i++) {
				indices[i] = substitutionElementwise(iav.getIndices()[i], subst);
				values[i] = subst.transform(iav.getValues()[i]);
			}
			
			for (int i=0; i<indices.length; i++) {
				Term newConjunct = 
						indexValueConnections(indices[i], values[i], indices, values, i+1, script);
				additionalConjuncsFromSelect.add(newConjunct);
			}
		}
		Term newConjunctsFromSelect = Util.and(m_Script, additionalConjuncsFromSelect.toArray(new Term[0]));
		Term result = Util.and(script, intermediateResult, newConjunctsFromSelect);
		
		result = (new SimplifyDDA(script)).getSimplifiedTerm(result);
		newAuxVars.addAll(iav.getNewAuxVars());
		
		return result;
	}
	
	private static Term[] substitutionElementwise(Term[] subtituents, SafeSubstitution subst) {
		Term[] result = new Term[subtituents.length];
		for (int i=0; i<subtituents.length; i++) {
			result[i] = subst.transform(subtituents[i]);
		}
		return result;
	}

	public static Term indexValueConnections(Term[] ourIndex, Term ourValue, 
			Term[][] othersIndices, Term[] othersValues, int othersPosition, Script script) {
		assert othersIndices.length == othersValues.length;
		ArrayList<Term> additionalConjuncs = new ArrayList<Term>();
		for (int i=othersPosition; i<othersIndices.length; i++) {
			Term[] othersIndex = othersIndices[i];
			assert ourIndex.length == othersIndex.length;
			Term indexEquality = Util.and(script, buildPairwiseEquality(ourIndex, othersIndices[i], null, script));
			Term valueEquality = UtilExperimental.binaryEquality(script, ourValue, othersValues[i]);
			Term conjunct = Util.or(script, Util.not(script, indexEquality),valueEquality);
			additionalConjuncs.add(conjunct);
		}
		Term result = Util.and(script, additionalConjuncs.toArray(new Term[0]));
		return result;
	}
	
	private class IndicesAndValues {
		private final Term m_SelectTerm[];
		private final Term m_Indices[][];
		private final Term m_Values[];
		private final Set<TermVariable> m_NewAuxVars;
		private final Map<Term, Term> m_SelectTerm2Value = new HashMap<Term, Term>();
		
		public IndicesAndValues(TermVariable array, Term[] conjunction) {
			ArrayRead[] arrayReads;
			{
				Term term = Util.and(m_Script, conjunction);
				Set<ApplicationTerm> selectTerms = 
						(new ApplicationTermFinder("select")).findMatchingSubterms(term);
				Map<Term[], ArrayRead> map = getArrayReads(array, selectTerms);
				arrayReads = map.values().toArray(new ArrayRead[0]);
			}
			m_SelectTerm = new Term[arrayReads.length];
			m_Indices = new Term[arrayReads.length][];
			m_Values = new Term[arrayReads.length];
			m_NewAuxVars = new HashSet<TermVariable>();
			for (int i=0; i<arrayReads.length; i++) {
				m_SelectTerm[i] = arrayReads[i].getSelectTerm();
				m_Indices[i] = arrayReads[i].getIndex();
				EqualityInformation eqInfo = PartialQuantifierElimination.getEqinfo(
						m_Script, arrayReads[i].getSelectTerm(), conjunction, array, quantifier); 
				if (eqInfo == null) {
					Term select = arrayReads[i].getSelectTerm();
					TermVariable auxVar = array.getTheory().createFreshTermVariable("arrayElim", select.getSort());
					m_NewAuxVars.add(auxVar);
					m_Values[i] = auxVar;
				} else {
					m_Values[i] = eqInfo.getTerm();
				}
				m_SelectTerm2Value.put(m_SelectTerm[i], m_Values[i]);
			}
		}

		public Term[] getSelectTerm() {
			return m_SelectTerm;
		}

		public Term[][] getIndices() {
			return m_Indices;
		}

		public Term[] getValues() {
			return m_Values;
		}

		public Set<TermVariable> getNewAuxVars() {
			return m_NewAuxVars;
		}
		
		public Map<Term, Term> getMapping() {
			return m_SelectTerm2Value;
		}
	}
	
	private class IndexValueConnection {
		private final Term[] m_fstIndex;
		private final Term[] m_sndIndex;
		private final Term m_fstValue;
		private final Term m_sndValue;
		private final boolean m_SelectConnection;
		private final Term m_IndexEquality;
		private final Term m_ValueEquality;
		
		public IndexValueConnection(Term[] fstIndex, Term[] sndIndex,
				Term fstValue, Term sndValue, boolean selectConnection) {
			m_fstIndex = fstIndex;
			m_sndIndex = sndIndex;
			m_fstValue = fstValue;
			m_sndValue = sndValue;
			m_SelectConnection = selectConnection;
			m_IndexEquality = Util.and(m_Script, buildPairwiseEquality(fstIndex, sndIndex, null, m_Script));
			m_ValueEquality = UtilExperimental.binaryEquality(m_Script, fstValue, sndValue);
		}
		
		/**
		 * Is equality of both indices already implied by context?
		 */
		public boolean indexEquality() {
			return m_IndexEquality.equals(m_Script.term("true"));
		}

		/**
		 * Is inequality of both indices already implied by context?
		 */
		public boolean indexInequality() {
			return m_IndexEquality.equals(m_Script.term("false"));
		}
		
		/**
		 * Is equality of both values already implied by context?
		 */
		public boolean valueEquality() {
			return m_ValueEquality.equals(m_Script.term("true"));
		}
		
		/**
		 * Is inequality of both values already implied by context?
		 */
		public boolean valueInequality() {
			return m_ValueEquality.equals(m_Script.term("false"));
		}

		public Term getTerm() {
			Term indexTerm = m_IndexEquality;
			if (m_SelectConnection) {
				indexTerm = Util.not(m_Script, indexTerm);
			}
			return Util.or(m_Script, indexTerm, m_ValueEquality);

		}
	}
	


	
	
	/**
	 * Return true if this is a nested select on arr.
	 * Throws exception if an index contains a select.
	 */
	private boolean isMultiDimensionalSelect(Term term, Term arr, int dimension) {
		Term subterm = term;
		for (int i=0; i<dimension; i++) {
			if (!(term instanceof ApplicationTerm)) {
				return false;
			}
			ApplicationTerm subtermApp = (ApplicationTerm) subterm;
			if (!subtermApp.getFunction().getName().equals("select")) {
				return false;
			}
			subterm = subtermApp.getParameters()[0];
			Term index = subtermApp.getParameters()[1];
			Set<ApplicationTerm> selectTermsInIndex = 
					(new ApplicationTermFinder("select")).findMatchingSubterms(index);
			if (!selectTermsInIndex.isEmpty()) {
				throw new UnsupportedOperationException("select in index not supported");
			}
		}
		return subterm.equals(arr);
	}
	
	
	private Term buildMultiDimensionalSelect(Term arr, Term[] index) {
		assert index.length > 0;
		assert arr.getSort().isArraySort();
		Term result = arr;
		for (int i=0; i<index.length; i++) {
			result = m_Script.term("select", result, index[i]);
		}
		return result;
	}


	/**
	 * Return all selectTerms that read from the array given by arrayTv.
	 * @param selectTerms a[i], 
	 * @return
	 */
	private static Map<Term[], ArrayRead> getArrayReads(TermVariable arrayTv,
			Set<ApplicationTerm> selectTerms) {
		Map<Term[],ArrayRead> arrayReads = new HashMap<Term[],ArrayRead>();
		for (ApplicationTerm selectTerm : selectTerms) {
			if (selectTerm.getFunction().getReturnSort().isArraySort()) {
				// this is only a select nested in some other select or store
				continue;
			}
			try {
				ArrayRead ar = new ArrayRead(selectTerm, arrayTv);
				arrayReads.put(ar.getIndex(), ar);
			} catch (ArrayReadException e) {
				// select on different array
				continue;
			}
		}
		return arrayReads;
	}
	
	
	/**
	 * Given two lists of terms and a subsitution subst
	 * return the following conjunctions
	 * subst(first_1) == subst(second_1), ... ,subst(first_n) == subst(second_n)
	 * if subst is null we use the identity function.  
	 */
	static Term[] buildPairwiseEquality(Term[] first, Term[] second, 
			SafeSubstitution subst, Script script) {
		assert first.length == second.length;
		Term[] equivalent = new Term[first.length];
		for (int i=0; i<first.length; i++) {
			Term firstTerm, secondTerm;
			if (subst == null) {
				firstTerm = first[i];
				secondTerm = second[i];
			} else {
				firstTerm = subst.transform(first[i]);
				secondTerm = subst.transform(second[i]);
			}
			equivalent[i] = script.term("=", firstTerm, secondTerm);
		}
		return equivalent;
	}
	
	/**
	 * assert term, replace TermVariable by constants in advance, replace
	 * by constants defined by mapping, if no constant defined by mapping
	 * declare constant and add to mapping
	 */
	public void assertTermWithTvs(Map<TermVariable, Term> mapping, Script script, Term term) {
		for (TermVariable tv :term.getFreeVars()) {
			if (!mapping.containsKey(tv)) {
				String name = "arrayElim_" + tv.getName();
				script.declareFun(name, new Sort[0], tv.getSort());
				Term constant = script.term(name);
				mapping.put(tv, constant);
			}
		}
		Term renamed = (new Substitution(mapping, script)).transform(term);
		m_Script.assertTerm(renamed);
	}
	
	/**
	 * Represents Term of the form a = ("store", a', k, data)
	 */
	private static class ArrayUpdate {
		private final TermVariable m_OldArray;
		private final TermVariable m_NewArray;
		private final Term[] m_Index;
		private final Term m_Data;
		
		private ArrayUpdate(Term term) throws ArrayUpdateException {

			if (!(term instanceof ApplicationTerm)) {
				throw new ArrayUpdateException("no ApplicationTerm");
			}
			ApplicationTerm eqAppTerm = (ApplicationTerm) term;
			if (!eqAppTerm.getFunction().getName().equals("=")) {
				throw new ArrayUpdateException("no equality");
			}
			if (!(eqAppTerm.getParameters().length == 2)) {
				throw new ArrayUpdateException("no binary equality");
			}
			Term lhs = eqAppTerm.getParameters()[0];
			Term rhs = eqAppTerm.getParameters()[1];
			ApplicationTerm allegedStoreTerm;
			if (isArrayTermVariable(lhs)) {
				if (isStoreTerm(rhs)) {
					m_NewArray = (TermVariable) lhs;
					allegedStoreTerm = (ApplicationTerm) rhs;
				} else {
					throw new ArrayUpdateException("no array update");
				}
			} else if (isArrayTermVariable(rhs)) {
				if (isStoreTerm(lhs)) {
					m_NewArray = (TermVariable) rhs;
					allegedStoreTerm = (ApplicationTerm) lhs;
				} else {
					throw new ArrayUpdateException("no array update");
				}
			} else {
				throw new ArrayUpdateException("no array update");
			}
			assert allegedStoreTerm.getFunction().getName().equals("store");
			assert allegedStoreTerm.getParameters().length == 3;
			assert m_NewArray.getSort() == allegedStoreTerm.getSort();
			int dimension = getDimension(m_NewArray.getSort());
			m_Index = new Term[dimension];
			m_Index[0] = allegedStoreTerm.getParameters()[1];
			if (dimension == 1) {
				m_OldArray = isArrayWithSort(
						allegedStoreTerm.getParameters()[0], m_NewArray.getSort());
				if (m_OldArray == null) {
					throw new ArrayUpdateException("oldArray no TermVariable");
				}
				m_Data = allegedStoreTerm.getParameters()[2];
			} else {
				if (dimension != 2) {
					throw new UnsupportedOperationException("dimension > 2 not implemented yet");
				}
				Term innnerStore = allegedStoreTerm.getParameters()[2];
				if (!(innnerStore instanceof ApplicationTerm)) {
					throw new ArrayUpdateException("no ApplicationTerm");
				}
				ApplicationTerm innerStoreApp = (ApplicationTerm) innnerStore;
				if (!allegedStoreTerm.getFunction().getName().equals("store")) {
					throw new ArrayUpdateException("no store term");
				}
				assert innerStoreApp.getParameters().length == 3;
				Term select = innerStoreApp.getParameters()[0];
				ApplicationTerm selectApp = (ApplicationTerm) select;
				if (!selectApp.getFunction().getName().equals("select")) {
					throw new ArrayUpdateException("no select term");
				}
				assert selectApp.getParameters().length == 2;
				m_OldArray = isArrayWithSort(
						selectApp.getParameters()[0], m_NewArray.getSort());
				if (m_OldArray == null) {
					throw new ArrayUpdateException("oldArray no TermVariable");
				}
				if (!selectApp.getParameters()[1].equals(m_Index[0])) {
					throw new ArrayUpdateException("different index");
				}
				m_Index[1] = innerStoreApp.getParameters()[1];
				m_Data = innerStoreApp.getParameters()[2];
			}
		}
		
		/**
		 * Returns true iff term is TermVariable and has array sort
		 */
		private boolean isArrayTermVariable(Term term) {
			if (term instanceof TermVariable) {
				if (term.getSort().isArraySort()) {
					return true;
				}
			}
			return false;
		}
		
		/**
		 * Returns true iff term is ApplicationTerm whose function symbol is
		 * "store".
		 */
		private boolean isStoreTerm(Term term) {
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (appTerm.getFunction().getName().equals("store")) {
					return true;
				}
			}
			return false;
		}

		/**
		 * If term is a term variable of Sort sort, return term as TermVariable,
		 * return null otherwise.
		 */
		TermVariable isArrayWithSort(Term term, Sort sort) {
			if (term instanceof TermVariable) {
				if (term.getSort().equals(sort)) {
					return (TermVariable) term;
				} else {
					return null;
				}
			} else {
				return null;
			}
		}
		public Term getOldArray() {
			return m_OldArray;
		}
		public Term getNewArray() {
			return m_NewArray;
		}
		public Term[] getIndex() {
			return m_Index;
		}
		public Term getData() {
			return m_Data;
		}
	}
	
	
	private static class ArrayUpdateException extends Exception {

		private static final long serialVersionUID = -5344050289008681972L;

		public ArrayUpdateException(String message) {
			super(message);
		}
	}
	
	
	public static int getDimension(Sort sort) {
		if (sort.isArraySort()) {
			Sort[] arg = sort.getArguments();
			assert arg.length == 2;
			return 1 + getDimension(arg[1]);
		} else {
			return 0;
		}
	}
	
	
	/**
	 * Given a (possibly nested) array a, this is a data structure for terms of
	 * the form  (select (select a i1) i2)  
	 *
	 */
	private static class ArrayRead {
		private final TermVariable m_Array;
		private final Term[] m_Index;
		private final ApplicationTerm m_SelectTerm;
		
		public ArrayRead(Term term, TermVariable tv) throws ArrayReadException {
			if (!(term instanceof ApplicationTerm)) {
				throw new ArrayReadException(false, "no ApplicationTerm");
			}
			m_SelectTerm = (ApplicationTerm) term;
			int dimension = getDimension(tv.getSort());
			m_Index = new Term[dimension];			
			for (int i = dimension-1; i>=0; i--) {
				if (!(term instanceof ApplicationTerm)) {
					throw new ArrayReadException(false, "no ApplicationTerm");
				}
				ApplicationTerm appTerm = (ApplicationTerm) term;
				if (!appTerm.getFunction().getName().equals("select")) {
					throw new ArrayReadException(false, "no select");
				}
				assert appTerm.getParameters().length == 2;
				m_Index[i] = appTerm.getParameters()[1];
				term = appTerm.getParameters()[0];
			}
			if (!tv.equals(term)) {
				throw new ArrayReadException(true, "different array");
			} else  {
				m_Array = tv;
			}
		}

		public TermVariable getArray() {
			return m_Array;
		}

		public Term[] getIndex() {
			return m_Index;
		}

		public ApplicationTerm getSelectTerm() {
			return m_SelectTerm;
		}
		
		@Override
		public String toString() {
			return m_SelectTerm.toString();
		}
		
		
	}
	
	
	
	private static class ArrayReadException extends Exception {

		private static final long serialVersionUID = -628021699371967800L;
		private final boolean m_DifferentArray;

		public ArrayReadException(boolean differentArray, String message) {
			super(message);
			m_DifferentArray = differentArray;
		}
		
		public boolean reasonIsDifferentArray() {
			return m_DifferentArray;
		}
	}
	
	
	
}
