/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Stack;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.ModelCheckerUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.ElimStore3.IndicesAndValues;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.EquivalenceRelationIterator.IExternalOracle;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.IncrementalPlicationChecker.Plication;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.ExtendedSimplificationResult;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayIndex;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.ArrayUpdate.ArrayUpdateExtractor;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSelect;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalStore;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.PrenexNormalForm;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierPusher.PqeTechniques;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierSequence;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.linearTerms.QuantifierSequence.QuantifiedVariables;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.partialQuantifierElimination.EqualityInformation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.DAGSize;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.Doubleton;
import de.uni_freiburg.informatik.ultimate.util.datastructures.EqualityStatus;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ThreeValuedEquivalenceRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TreeRelation;

/**
 * Let aElim be the array variable that we want to eliminate. We presume that
 * there is only one term of the form (store aElim storeIndex newValue), for
 * some index element storeIndex and some value element newValue.
 *
 * The basic idea is the following. Let Idx be the set of all indices of select
 * terms that have aElim as (first) argument. We introduce
 * <ul>
 * <li>a new array variable aNew that represents the store term
 * <li>a new value variable oldCell_i for each i∈Idx that represents the value
 * of the array cell before the update.
 * </ul>
 * We replace
 * <ul>
 * <li>(store aElim storeIndex newValue) by aNew, and
 * <li>(select aElim i) by oldCell_i for each i∈Idx.
 * </ul>
 * Furthermore, we add the following conjuncts for each i∈Idx. 
 * <ul>
 * <li> (i == storeIndex)==> (aNew[i] == newValue && ∀k∈Idx. i == k ==> oldCell_i == oldCell_k) 
 * <li> (i != storeIndex) ==> (aNew[i] == oldCell_i)
 * </ul>
 * 
 * Optimizations: 
 * <ul>
 * <li> Optim1: We check equality and disequality for each pair of
 * indices and evaluate (dis)equalities in the formula above directly. Each
 * equality/disequality that is not valid (i.e. only true in this context) has
 * to be added as an additional conjunct.
 * <li> Optim2: We do not work with all
 * indices but build equivalence classes and work only with the representatives.
 * (We introduce only one oldCell variable for each equivalence class) 
 * <li> Optim3: For each index i that is disjoint for the store index we do not introduce the
 * variable oldCell_i, but use aNew[i] instead. 
 * <li> Optim4: For each i∈Idx we check
 * the context if we find some term tEq that is equivalent to oldCell_i. In case
 * we found some we use tEq instead of oldCell_i. 
 * <li> Optim5: (Only sound in
 * combination with Optim3. For each pair i,k∈Idx that are both disjoint from
 * storeIndex, we can drop the "i == k ==> oldCell_i == oldCell_k" term.
 * Rationale: we use aNew[i] and aNew[k] instead of oldCell_i and oldCell_k,
 * hence the congruence information is already given implicitly.
 * </ul>
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *
 */
public class ElimStorePlain {

	private final Script mScript;
	private final ManagedScript mMgdScript;
	private final IUltimateServiceProvider mServices;
	private final ILogger mLogger;
	private final SimplificationTechnique mSimplificationTechnique;
	private static final String s_AUX_VAR_NEW_ARRAY = "arrayElimArr";
	private static final String s_AUX_VAR_INDEX = "arrayElimIndex";
	private static final String s_AUX_VAR_ARRAYCELL = "arrayElimCell";
	
	private static Comparator<Term> mFewerVariablesFirst = new Comparator<Term>() {

		@Override
		public int compare(final Term o1, final Term o2) {
			return o2.getFreeVars().length - o1.getFreeVars().length;
		}
	};

	public ElimStorePlain(final ManagedScript mgdScript, final IUltimateServiceProvider services,
			final SimplificationTechnique simplificationTechnique, final int quantifier) {
		super();
		mScript = mgdScript.getScript();
		mMgdScript = mgdScript;
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(ModelCheckerUtils.PLUGIN_ID);
		mSimplificationTechnique = simplificationTechnique;
	}

	public EliminationTask elimAll(final EliminationTask eTask) {

		final Stack<EliminationTask> taskStack = new Stack<>();
		final ArrayList<Term> resultDisjuncts = new ArrayList<>();
		final Set<TermVariable> resultEliminatees = new LinkedHashSet<>();
		{
			final EliminationTask eliminationTask = new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(),
					eTask.getTerm());
			pushTaskOnStack(eliminationTask, taskStack);
		}
		int numberOfRounds = 0;
		while (!taskStack.isEmpty()) {
			final EliminationTask currentETask = taskStack.pop();
			final TreeRelation<Integer, TermVariable> tr = classifyEliminatees(currentETask.getEliminatees());

			final LinkedHashSet<TermVariable> arrayEliminatees = getArrayTvSmallDimensionsFirst(tr);

			if (arrayEliminatees.isEmpty()) {
				// no array eliminatees left
				resultDisjuncts.add(currentETask.getTerm());
				resultEliminatees.addAll(currentETask.getEliminatees());
			} else {
				TermVariable thisIterationEliminatee;
				{
					final Iterator<TermVariable> it = arrayEliminatees.iterator();
					thisIterationEliminatee = it.next();
					it.remove();
				}

				final EliminationTask ssdElimRes = elim1(currentETask.getQuantifier(), thisIterationEliminatee,
						currentETask.getTerm());
				arrayEliminatees.addAll(ssdElimRes.getEliminatees());
				// also add non-array eliminatees
				arrayEliminatees.addAll(tr.getImage(0));
				final EliminationTask eliminationTask1 = new EliminationTask(ssdElimRes.getQuantifier(),
						arrayEliminatees, ssdElimRes.getTerm());
				final EliminationTask eliminationTask2 = applyNonSddEliminations(eliminationTask1,
						PqeTechniques.ALL_LOCAL);
				if (mLogger.isInfoEnabled()) {
					mLogger.info("Start of round: " + printVarInfo(tr) + " End of round: "
							+ printVarInfo(classifyEliminatees(eliminationTask2.getEliminatees())) + " and "
							+ PartialQuantifierElimination.getXjunctsOuter(eTask.getQuantifier(),
									eliminationTask2.getTerm()).length
							+ " xjuncts.");
				}

				pushTaskOnStack(eliminationTask2, taskStack);
			}
			numberOfRounds++;
		}
		mLogger.info("Needed " + numberOfRounds + " rounds to eliminate " + eTask.getEliminatees().size()
				+ " variables, produced " + resultDisjuncts.size() + " xjuncts");
		// return term and variables that we could not eliminate
		return new EliminationTask(eTask.getQuantifier(), resultEliminatees, PartialQuantifierElimination
				.applyCorrespondingFiniteConnective(mScript, eTask.getQuantifier(), resultDisjuncts));
	}

	private String printVarInfo(final TreeRelation<Integer, TermVariable> tr) {
		final StringBuilder sb = new StringBuilder();
		for (final Integer dim : tr.getDomain()) {
			sb.append(tr.getImage(dim).size() + " dim-" + dim + " vars, ");
		}
		return sb.toString();
	}

	private void pushTaskOnStack(final EliminationTask eTask, final Stack<EliminationTask> taskStack) {
		final Term term = eTask.getTerm();
		final Term[] disjuncts = PartialQuantifierElimination.getXjunctsOuter(eTask.getQuantifier(), term);
		if (disjuncts.length == 1) {
			taskStack.push(eTask);
		} else {
			for (final Term disjunct : disjuncts) {
				taskStack.push(new EliminationTask(eTask.getQuantifier(), eTask.getEliminatees(), disjunct));
			}
		}
	}

	private EliminationTask applyNonSddEliminations(final EliminationTask eTask, final PqeTechniques techniques)
			throws AssertionError {
		final Term quantified = SmtUtils.quantifier(mScript, eTask.getQuantifier(), eTask.getEliminatees(),
				eTask.getTerm());
		final Term pushed = new QuantifierPusher(mMgdScript, mServices, true, techniques).transform(quantified);

		final Term pnf = new PrenexNormalForm(mMgdScript).transform(pushed);
		final QuantifierSequence qs = new QuantifierSequence(mMgdScript.getScript(), pnf);
		final Term matrix = qs.getInnerTerm();
		final List<QuantifiedVariables> qvs = qs.getQuantifierBlocks();

		final Set<TermVariable> eliminatees1;
		if (qvs.size() == 0) {
			eliminatees1 = Collections.emptySet();
		} else if (qvs.size() == 1) {
			eliminatees1 = qvs.get(0).getVariables();
			if (qvs.get(0).getQuantifier() != eTask.getQuantifier()) {
				throw new UnsupportedOperationException("alternation not yet supported");
			}
		} else if (qvs.size() > 1) {
			throw new UnsupportedOperationException("alternation not yet supported");
		} else {
			throw new AssertionError();
		}
		return new EliminationTask(eTask.getQuantifier(), eliminatees1, matrix);
	}

	private LinkedHashSet<TermVariable> getArrayTvSmallDimensionsFirst(final TreeRelation<Integer, TermVariable> tr) {
		final LinkedHashSet<TermVariable> result = new LinkedHashSet<>();
		for (final Integer dim : tr.getDomain()) {
			if (dim != 0) {
				result.addAll(tr.getImage(dim));
			}
		}
		return result;
	}

	private TreeRelation<Integer, TermVariable> classifyEliminatees(final Collection<TermVariable> eliminatees) {
		final TreeRelation<Integer, TermVariable> tr = new TreeRelation<>();
		for (final TermVariable eliminatee : eliminatees) {
			final MultiDimensionalSort mds = new MultiDimensionalSort(eliminatee.getSort());
			tr.addPair(mds.getDimension(), eliminatee);
		}
		return tr;
	}

	public EliminationTask elim1(final int quantifier, final TermVariable eliminatee, final Term inputTerm) {
		final Term[] xjunctsOuter = PartialQuantifierElimination.getXjunctsOuter(quantifier, inputTerm);
		if (xjunctsOuter.length > 1) {
			throw new AssertionError("several disjuncts! " + inputTerm);
		}
		final List<MultiDimensionalStore> stores = extractStores(eliminatee, inputTerm);
		if (stores.size() > 1) {
			throw new AssertionError("not yet supported: multiple stores " + inputTerm);
		}
//		checkForUnsupportedSelfUpdate(eliminatee, inputTerm, mQuantifier);

		final Set<TermVariable> newAuxVars = new LinkedHashSet<>();
		final Term preprocessedInput;
		
		{
			//anti-DER preprocessing
			final ArrayEqualityExplicator aadk = new ArrayEqualityExplicator(mMgdScript, eliminatee, quantifier);
			final Term antiDerPreprocessed = aadk.transform(inputTerm);
			newAuxVars.addAll(aadk.getNewAuxVars());
			final DerPreprocessor dp = new DerPreprocessor(mServices, mMgdScript, eliminatee, quantifier);
			final Term withReplacement = dp.transform(antiDerPreprocessed);
			newAuxVars.addAll(dp.getNewAuxVars());
			final Term definitions = PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier, dp.getAuxVarDefinitions());
			preprocessedInput = PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier, withReplacement, definitions);
			if (dp.introducedDerPossibility()) {
				// do DER
				final EliminationTask afterDer = applyNonSddEliminations(new EliminationTask(quantifier, Collections.singleton(eliminatee), preprocessedInput), PqeTechniques.ONLY_DER);
				newAuxVars.addAll(afterDer.getEliminatees());
				return new EliminationTask(quantifier, newAuxVars, afterDer.getTerm());
			} 

		}

		final Orac oracB = new Orac(preprocessedInput);
		if (oracB.mIncrementalPlicationChecker.checkSat(mMgdScript.getScript().term("true"))== LBool.UNSAT) {
			mLogger.warn("input unsat");
			oracB.unlockSolver();
			return new EliminationTask(quantifier, Collections.emptySet(), mMgdScript.getScript().term("false"));
		}
		oracB.unlockSolver();

		final List<ApplicationTerm> selectTerms = extractSelects2(eliminatee, preprocessedInput);

		if (false && stores.isEmpty()) {
			if (!selectTerms.isEmpty()) {
				final IndicesAndValues iav = new IndicesAndValues(mMgdScript, quantifier, eliminatee, inputTerm);
				final Pair<List<ArrayIndex>, List<Term>> indicesAndValues =
						ElimStore3.buildIndicesAndValues(mMgdScript, iav);

				final ArrayList<Term> indexValueConstraintsFromEliminatee = ElimStore3.constructIndexValueConstraints(
						mMgdScript.getScript(), quantifier, indicesAndValues.getFirst(), indicesAndValues.getSecond());
				final Term indexValueConstraints = PartialQuantifierElimination.applyDualFiniteConnective(mScript,
						quantifier, indexValueConstraintsFromEliminatee);
				final Substitution subst = new SubstitutionWithLocalSimplification(mMgdScript, iav.getMapping());
				final Term replaced = subst.transform(inputTerm);
				final Term result = PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier,
						Arrays.asList(new Term[] { replaced, indexValueConstraints }));
				assert !Arrays.asList(result.getFreeVars()).contains(eliminatee) : "var is still there";
				return new EliminationTask(quantifier, iav.getNewAuxVars(), result);
			} else {
				throw new AssertionError("no case applies");
			}
		}

		final Term storeTerm;
		final Term storeIndex;
		final Term storeValue;
		if (stores.isEmpty()) {
			storeTerm = null;
			storeIndex = null;
			storeValue = null;
			// mLogger.info("store-free iteration");
		} else {
			final MultiDimensionalStore store = stores.iterator().next();
			storeTerm = store.getStoreTerm();
			storeIndex = store.getIndex().get(0);
			storeValue = ((ApplicationTerm) storeTerm).getParameters()[2];
			// mLogger.info("eliminating store to array of dimension " + new
			// MultiDimensionalSort(eliminatee.getSort()).getDimension());
		}

		final Set<Term> indices = new HashSet<>();
		final Set<Term> selectIndicesSet = new HashSet<>();
		
		if (!stores.isEmpty()) {
			indices.add(storeIndex);
		}
		
		final ThreeValuedEquivalenceRelation<Term> newEqualityInformation = collectComplimentaryEqualityInformation(
				quantifier, preprocessedInput, selectTerms, storeTerm, storeIndex, storeValue);
		
		for (final ApplicationTerm selectTerm : selectTerms) {
			final Term selectIndex = getIndexOfSelect(selectTerm);
			indices.add(selectIndex);
			selectIndicesSet.add(selectIndex);
		}
		
		
		newEqualityInformation.toString();
		final List<Term> selectIndices = new ArrayList<>(selectIndicesSet);
		
		final List<Term> sortedIndices = new ArrayList<>(indices);

		Collections.sort(sortedIndices, mFewerVariablesFirst);
		
		final Pair<ThreeValuedEquivalenceRelation<Term>, List<Term>> analysisResult =
				analyzeIndexEqualities(quantifier, indices, preprocessedInput, newEqualityInformation);
		final ThreeValuedEquivalenceRelation<Term> equalityInformation = analysisResult.getFirst();
		
		
		
		final List<Term> selectIndexRepresentatives = new ArrayList<>();
		final List<Term> allIndexRepresentatives = new ArrayList<>();
		for (final Term selectIndex : selectIndicesSet) {
			final Term selectIndexRepresentative = equalityInformation.getRepresentative(selectIndex);
			selectIndexRepresentatives.add(selectIndexRepresentative);
			allIndexRepresentatives.add(selectIndexRepresentative);
		}
		Term storeIndexRepresentative;
		if (storeIndex == null) {
			storeIndexRepresentative = null;
		} else {
			storeIndexRepresentative = equalityInformation.getRepresentative(storeIndex);
			allIndexRepresentatives.add(storeIndexRepresentative);
		}
		
		

		final Sort valueSort = eliminatee.getSort().getArguments()[1];

		final AuxVarConstructor auxVarConstructor = new AuxVarConstructor();
		final IndexMappingProvider imp = new IndexMappingProvider(allIndexRepresentatives, eliminatee, equalityInformation,
				auxVarConstructor, quantifier);

		final Map<Term, Term> indexMapping = imp.getIndexReplacementMapping();
		final List<Term> indexMappingDefinitions = imp.getIndexMappingDefinitions();

		final Term notEqualsDetectedBySolver = PartialQuantifierElimination.applyDualFiniteConnective(mScript,
				quantifier, analysisResult.getSecond());
		final Term indexDefinitionsTerm =
				PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier, indexMappingDefinitions);
		final Term term = PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier,
				Arrays.asList(new Term[] { indexDefinitionsTerm, preprocessedInput, notEqualsDetectedBySolver }));

		final Term newArray;
		{
			if (storeIndex == null) {
				newArray = null;
			} else {
				final EqProvider eqProvider = new EqProvider(preprocessedInput, eliminatee, quantifier);
				final Term eqArray = eqProvider.getEqTerm(storeTerm);
				if (eqArray != null) {
					newArray = eqArray;
				} else {
					newArray = auxVarConstructor.constructAuxVar(s_AUX_VAR_NEW_ARRAY, eliminatee.getSort());
				}
			}
		}
		


		
		final Map<Term, Term> oldCellMapping = constructOldCellValueMapping(selectIndexRepresentatives, storeIndex,
				equalityInformation, valueSort, selectIndexRepresentatives.contains(equalityInformation.getRepresentative(storeIndex)), newArray, indexMapping,
				auxVarConstructor, preprocessedInput, eliminatee, quantifier);
		newAuxVars.addAll(auxVarConstructor.getConstructedAuxVars());
		
		final IncrementalPlicationChecker iplc = new IncrementalPlicationChecker(Plication.IMPLICATION, mMgdScript, inputTerm);
		final List<Doubleton<Term>> uknowns = EquivalenceRelationIterator.buildListOfNonDisjointDoubletons(indices, equalityInformation);
		final ValueEqualityChecker vec = new ValueEqualityChecker(eliminatee, storeIndex, storeValue, equalityInformation, mMgdScript, 
				iplc, oldCellMapping);
		final List<Doubleton<Term>> relevant = new ArrayList<>();
		for (final Doubleton<Term> unk : uknowns) {
			final boolean dist = vec.isDistinguishworthyIndexPair(unk.getOneElement(), unk.getOtherElement());
			if (dist) {
				relevant.add(unk);
			}
		}
		iplc.unlockSolver();
		
		


		final Map<Term, Term> substitutionMapping = new HashMap<>();
		if (!stores.isEmpty()) {
			substitutionMapping.put(storeTerm, newArray);
		}
		for (final Term selectIndex : selectIndices) {
			final Term oldSelect = mMgdScript.getScript().term("select", eliminatee, selectIndex);
			final Term indexRepresentative = equalityInformation.getRepresentative(selectIndex);
			if (oldCellMapping.containsKey(indexRepresentative)) {
				substitutionMapping.put(oldSelect, oldCellMapping.get(indexRepresentative));
			} else {
				final Term newSelect = mMgdScript.getScript().term("select", newArray, indexRepresentative);
				substitutionMapping.put(oldSelect, newSelect);
			}
		}


		final Term storeValueRep;
		if (storeValue == null) {
			storeValueRep = null;
		} else {
			storeValueRep = new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(storeValue);
		}
		final Term wc;
		if (storeIndex == null) {
			wc = mMgdScript.getScript().term("true");
		} else {
			wc = constructWriteConstraints((ArrayList<Term>) selectIndexRepresentatives, equalityInformation,
					mMgdScript, indexMapping, oldCellMapping, eliminatee, quantifier, storeIndexRepresentative,
					newArray, storeValueRep);
		}
		final Term cc = constructIndexValueConnection((ArrayList<Term>) selectIndexRepresentatives, equalityInformation, mMgdScript,
				indexMapping, oldCellMapping, eliminatee, quantifier, storeIndex);

		final Term transformedTerm =
				new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(term);
		final Term valueEqualityTerm2 = mMgdScript.getScript().term("true");
//				PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier, vec.getValueEqualities());
		final Term storedValueInformation = constructStoredValueInformation(quantifier, eliminatee, stores, storeIndexRepresentative,
				storeValue, indexMapping, newArray, substitutionMapping);
		Term res = PartialQuantifierElimination.applyDualFiniteConnective(mScript, quantifier,
				transformedTerm, valueEqualityTerm2, storedValueInformation, wc, cc);
		assert !Arrays.asList(res.getFreeVars()).contains(eliminatee) : "var is still there: " + eliminatee
		+ " term size " + new DagSizePrinter(res);
		{
			final StringBuilder sb = new StringBuilder();
			sb.append("Elim1");
			if (inputTerm == preprocessedInput) {
				sb.append(" did not use preprocessing");
			} else {
				sb.append(" applied some preprocessing");
			}
			final int dim = new MultiDimensionalSort(eliminatee.getSort()).getDimension();
			sb.append(" eliminated variable of array dimension " + dim);
			if (storeIndex == null) {
				sb.append(", no store index");
			} else {
				sb.append(", one store index");
			}
			sb.append(", " + selectIndices.size() + " select indices");
			sb.append(", " + selectIndexRepresentatives.size() + " select index equivalence classes");
			final int indexPairs = (selectIndexRepresentatives.size() * selectIndexRepresentatives.size()
					- selectIndexRepresentatives.size()) / 2;
			sb.append(String.format(", %d disjoint index pairs (out of %d index pairs)",
					equalityInformation.getDisequalities().size(), indexPairs));
			sb.append(String.format(", introduced %d new quantified variables", newAuxVars.size()));
			sb.append(String.format(", treesize of input %d treesize of output %d",
					new DAGSize().treesize(inputTerm), new DAGSize().treesize(res)));
			mLogger.info(sb.toString());
		}
		final Term nonsimpl = res;
		final ExtendedSimplificationResult sws = SmtUtils.simplifyWithStatistics(mMgdScript, res, mServices, mSimplificationTechnique);
		res = sws.getSimplifiedTerm();
		mLogger.info(String.format("treesize reduction %d that is %2.1f percent of original size",
				sws.getReductionOfTreeSize(), sws.getReductionRatioInPercent()));
		mLogger.info("treesize after simplification " + new DAGSize().treesize(res));
		return new EliminationTask(quantifier, newAuxVars, res);

	}

	private ThreeValuedEquivalenceRelation<Term> collectComplimentaryEqualityInformation(final int quantifier,
			final Term preprocessedInput, final List<ApplicationTerm> selectTerms, final Term storeTerm,
			final Term storeIndex, final Term storeValue) {
		final ThreeValuedEquivalenceRelation<Term> newEqualityInformation = new ThreeValuedEquivalenceRelation<>();
		final Term[] context = PartialQuantifierElimination.getXjunctsInner(quantifier, preprocessedInput);
		for (final ApplicationTerm selectTerm : selectTerms) {
			final Term selectIndex = getIndexOfSelect(selectTerm);
			addComplimentaryEqualityInformation(context, selectIndex, newEqualityInformation);
			addComplimentaryEqualityInformation(context, selectTerm, newEqualityInformation);
		}
		if (storeTerm != null) {
			addComplimentaryEqualityInformation(context, storeIndex, newEqualityInformation);
			addComplimentaryEqualityInformation(context, storeValue, newEqualityInformation);
		}
		return newEqualityInformation;
	}

	/**
	 * Add equality information for term that are obtained from context by
	 * only looking at (dis)eqality terms. Add only the infor
	 * @param context
	 * @param forbiddenTerm
	 * @param term
	 * @param equalityInformation
	 */
	private void addComplimentaryEqualityInformation(final Term[] context,
			final Term term, final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		equalityInformation.addElement(term);
		final Pair<Set<Term>, Set<Term>> indexEqual = EqualityInformation.getEqTerms(mScript, term, context, null);
		for (final Term equal : indexEqual.getFirst()) {
			equalityInformation.addElement(equal);
			equalityInformation.reportEquality(term, equal);
		}
		for (final Term disequal : indexEqual.getSecond()) {
			equalityInformation.addElement(disequal);
			equalityInformation.reportDisequality(term, disequal);
		}
	}

	private Term constructStoredValueInformation(final int quantifier, final TermVariable eliminatee,
			final List<MultiDimensionalStore> stores, final Term storeIndex, final Term storeValue,
			final Map<Term, Term> indexMapping, final Term newArray, final Map<Term, Term> substitutionMapping)
			throws AssertionError {
		final Term storedValueInformation;
		if (stores.isEmpty()) {
			if (quantifier == QuantifiedFormula.EXISTS) {
				storedValueInformation = mScript.term("true");
			} else if (quantifier == QuantifiedFormula.FORALL) {
				storedValueInformation = mScript.term("false");
			} else {
				throw new AssertionError("unknown quantifier");
			}
		} else {
			final Term replacementIndex = indexMapping.get(storeIndex);
			storedValueInformation = PartialQuantifierElimination.equalityForExists(mScript, quantifier,
					mScript.term("select", newArray, replacementIndex),
					new SubstitutionWithLocalSimplification(mMgdScript, substitutionMapping).transform(storeValue));
		}
		return storedValueInformation;
	}

	private Pair<ThreeValuedEquivalenceRelation<Term>, List<Term>> analyzeIndexEqualities(final int mQuantifier,
			final Set<Term> indices, final Term inputTerm, final ThreeValuedEquivalenceRelation<Term> inputTveR) {

		final ThreeValuedEquivalenceRelation<Term> tver = new ThreeValuedEquivalenceRelation<>(inputTveR);
		for (final Term index : indices) {
			tver.addElement(index);
		}

		final List<Term> relationsDetectedViaSolver = new ArrayList<>();
		final ArrayList<Term> indicesList = new ArrayList<>(indices);
		final Plication plication;
		if (mQuantifier == QuantifiedFormula.EXISTS) {
			plication = Plication.IMPLICATION;
		} else if (mQuantifier == QuantifiedFormula.FORALL) {
			plication = Plication.EXPLICATION;
		} else {
			throw new AssertionError("unknown quantifier");
		}
		final IncrementalPlicationChecker iea = new IncrementalPlicationChecker(plication, mMgdScript, inputTerm);
		
		for (int i = 0; i < indicesList.size(); i++) {
			for (int j = i + 1; j < indicesList.size(); j++) {
				//TODO: try to obtain equal term with few variables
				final Term index1 = indicesList.get(i);
				final Term index2 = indicesList.get(j);
				if (tver.getEqualityStatus(index1, index2) != EqualityStatus.UNKNOWN) {
					// result already known we do not have to check
					continue;
					// TODO: for some the solver result might have been unknown
					// we should avoid to these are checked again
				}
				
				final Term eq = SmtUtils.binaryEquality(mScript, index1, index2);
				if (SmtUtils.isTrue(eq)) {
					tver.reportEquality(index1, index2);
					assert !tver.isInconsistent() : "inconsistent equality information";
				} else if (SmtUtils.isFalse(eq)) {
					tver.reportDisequality(index1, index2);
					assert !tver.isInconsistent() : "inconsistent equality information";
				} else {
					final Term neq = SmtUtils.not(mScript, eq);
					final Validity isEqual = iea.checkPlication(eq);
					if (isEqual == Validity.UNKNOWN && mLogger.isWarnEnabled()) {
						mLogger.warn("solver failed to check if following equality is implied: " + eq);
					}
					if (isEqual == Validity.VALID) {
						if (mQuantifier == QuantifiedFormula.EXISTS) {
							tver.reportEquality(index1, index2);
							assert !tver.isInconsistent() : "inconsistent equality information";
						} else if (mQuantifier == QuantifiedFormula.FORALL) {
							tver.reportDisequality(index1, index2);
							assert !tver.isInconsistent() : "inconsistent equality information";
						} else {
							throw new AssertionError("unknown quantifier");
						}
						relationsDetectedViaSolver.add(eq);
						mLogger.info("detected equality via solver");
					} else {
						final Validity notEqualsHolds = iea.checkPlication(neq);
						if (notEqualsHolds == Validity.UNKNOWN && mLogger.isWarnEnabled()) {
							mLogger.warn("solver failed to check if following not equals relation is implied: "
									+ eq);
						}

						if (notEqualsHolds == Validity.VALID) {
							if (mQuantifier == QuantifiedFormula.EXISTS) {
								tver.reportDisequality(index1, index2);
								assert !tver.isInconsistent() : "inconsistent equality information";
							} else if (mQuantifier == QuantifiedFormula.FORALL) {
								tver.reportEquality(index1, index2);
								assert !tver.isInconsistent() : "inconsistent equality information";
							} else {
								throw new AssertionError("unknown quantifier");
							}
							mLogger.info("detected not equals via solver");
							relationsDetectedViaSolver.add(neq);
						}
					}
				}
			}
		}
		iea.unlockSolver();
		return new Pair<>(tver, relationsDetectedViaSolver);
	}

	private void checkForUnsupportedSelfUpdate(final TermVariable eliminatee, final Term inputTerm,
			final int quantifier) {
		final Set<ApplicationTerm> equalities = new ApplicationTermFinder("=", false).findMatchingSubterms(inputTerm);
		final ArrayUpdateExtractor aue = new ArrayUpdateExtractor(quantifier == QuantifiedFormula.FORALL, false,
				equalities.toArray(new Term[equalities.size()]));
		for (final ArrayUpdate au : aue.getArrayUpdates()) {
			if (au.getNewArray().equals(eliminatee)) {
				if (Arrays.asList(au.getMultiDimensionalStore().getStoreTerm().getFreeVars()).contains(eliminatee)) {
					throw new UnsupportedOperationException("Want to eliminate " + eliminatee
							+ " but encountered yet unsupported self-update " + au.getArrayUpdateTerm());
				}
			}
		}
	}

	/**
	 * Let eliminatee be the array that is eliminated and (select eliminatee idx
	 * v) a select term. If idx contains eliminatee, we have to replace idx by
	 * an auxiliary variable. As an optimization, we only construct one
	 * auxiliary variable for each equivalence class of indices.
	 * 
	 * @param auxVarConstructor
	 */
	private Map<Term, TermVariable> constructIndexReplacementMapping(final Set<Term> indices,
			final TermVariable eliminatee, final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final AuxVarConstructor auxVarConstructor) throws AssertionError {
		final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

			@Override
			public TermVariable constructValue(final Term index) {
				final TermVariable indexReplacement = auxVarConstructor.constructAuxVar(s_AUX_VAR_INDEX,
						index.getSort());
				return indexReplacement;
			}

		};
		final ConstructionCache<Term, TermVariable> cc = new ConstructionCache<>(valueConstruction);
		final Map<Term, TermVariable> indexReplacementMapping = new HashMap<>();
		for (final Term index : indices) {
			if (Arrays.asList(index.getFreeVars()).contains(eliminatee)) {
				// need to replace index
				final Term indexRepresentative = equalityInformation.getRepresentative(index);
				final TermVariable indexReplacement = cc.getOrConstruct(indexRepresentative);
				indexReplacementMapping.put(index, indexReplacement);
			}
		}
		return indexReplacementMapping;
	}

	private void constructIndexReplacementIfNecessary(final int quantifier, final TermVariable eliminatee,
			final Set<TermVariable> newAuxVars, final Map<Term, Term> indexMapping,
			final List<Term> indexMappingDefinitions, final Term index) {
		if (Arrays.asList(index.getFreeVars()).contains(eliminatee)) {
			// need to replace index
			final TermVariable newAuxIndex = mMgdScript.constructFreshTermVariable(s_AUX_VAR_INDEX, index.getSort());
			newAuxVars.add(newAuxIndex);
			indexMapping.put(index, newAuxIndex);
			indexMappingDefinitions
					.add(PartialQuantifierElimination.equalityForExists(mScript, quantifier, newAuxIndex, index));
		}
	}

	private Term constructNewSelectWithPossiblyReplacedIndex(final Term newArray, final ApplicationTerm oldSelectTerm,
			final Map<Term, Term> indexMapping, final TermVariable eliminatee) {
		final Term newIndex = getNewIndex(getIndexOfSelect(oldSelectTerm), indexMapping, eliminatee);
		final Term newSelect = mMgdScript.getScript().term("select", newArray, newIndex);
		return newSelect;
	}

	private Term getNewIndex(final Term originalIndex, final Map<Term, Term> indexMapping,
			final TermVariable eliminatee) {
		final Term newIndex;
		final Term replacementIndex = indexMapping.get(originalIndex);
		if (replacementIndex == null) {
			newIndex = originalIndex;
			assert !Arrays.asList(originalIndex.getFreeVars()).contains(eliminatee);
		} else {
			newIndex = replacementIndex;
			assert Arrays.asList(originalIndex.getFreeVars()).contains(eliminatee);
		}
		return newIndex;
	}

	/**
	 * Let eliminatee be the array that is eliminated and (select eliminatee idx
	 * v) a select term. Construct mapping that assigns the select term an
	 * auxiliary variable the represents this array cell. If we know that the
	 * index of the store that we currently process is disjoint from idx, we do
	 * not add the auxiliary variable (the new cell will have same value as old
	 * cell). As an optimization, we only construct one auxiliary variable for
	 * each equivalence class of indices.
	 * 
	 * @param newAuxArray
	 * @param auxVarConstructor
	 * @param preprocessedInput
	 * @param eliminatee
	 * @param quantifier
	 */
	private Map<Term, Term> constructOldCellValueMapping(final List<Term> selectIndexRepresentatives,
			final Term storeIndex, final ThreeValuedEquivalenceRelation<Term> equalityInformation, final Sort valueSort,
			final boolean storeIndexIsAlsoSelectIndex, final Term newAuxArray,
			final Map<Term, Term> rawIndex2replacedIndex, final AuxVarConstructor auxVarConstructor,
			final Term preprocessedInput, final TermVariable eliminatee, final int quantifier) {
		final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

			@Override
			public TermVariable constructValue(final Term index) {
				final TermVariable oldCell = auxVarConstructor.constructAuxVar(s_AUX_VAR_ARRAYCELL, valueSort);
				return oldCell;
			}

		};
		final ConstructionCache<Term, TermVariable> cc = new ConstructionCache<>(valueConstruction);
		final EqProvider eqProvider = new EqProvider(preprocessedInput, eliminatee, quantifier);
		final Map<Term, Term> oldCellMapping = new HashMap<>();
		for (final Term selectIndexRepresentative : selectIndexRepresentatives) {
			if ((storeIndex != null) && equalityInformation.getEqualityStatus(selectIndexRepresentative,
					storeIndex) == EqualityStatus.NOT_EQUAL) {
//				if (storeIndexIsAlsoSelectIndex) {

					final Term replacementSelectIndex = rawIndex2replacedIndex.get(selectIndexRepresentative);
					final Term newSelect = mMgdScript.getScript().term("select", newAuxArray, replacementSelectIndex);
					oldCellMapping.put(selectIndexRepresentative, newSelect);
//				} else {
//					// do nothing
//				}
			} else {
				final Term oldSelectRep = findOldSelectRepresentative(equalityInformation, eliminatee,
						selectIndexRepresentative);
				final Term eqTerm = findNiceReplacementForRepresentative(oldSelectRep, eliminatee, equalityInformation);
				if (eqTerm != null) {
					oldCellMapping.put(selectIndexRepresentative, eqTerm);
				} else {
					final TermVariable oldCellVariable = cc.getOrConstruct(selectIndexRepresentative);
					oldCellMapping.put(selectIndexRepresentative, oldCellVariable);
				}
			}
		}
		return oldCellMapping;
	}

	private Term findOldSelectRepresentative(final ThreeValuedEquivalenceRelation<Term> equalityInformation,
			final TermVariable eliminatee, final Term selectIndexRepresentative) {
		for (final Term indexEquivalent : equalityInformation.getEquivalenceClass(selectIndexRepresentative)) {
			final Term oldSelectTerm = mMgdScript.getScript().term("select", eliminatee, indexEquivalent);
			final Term oldSelectRep = equalityInformation.getRepresentative(oldSelectTerm);
			if (oldSelectRep != null) {
				return oldSelectRep;
			}
		}
		throw new AssertionError("Did not find oldSelectRep for " + selectIndexRepresentative);
	}

	private void constructAndAddOldCellValueTermVariable(final Map<Term, TermVariable> oldCellMapping,
			final ApplicationTerm entry, final UnionFind<Term> indices) throws AssertionError {
		final Term indexRepresentative = indices.find(getIndexOfSelect(entry));
		TermVariable oldCell = oldCellMapping.get(indexRepresentative);
		if (oldCell == null) {
			oldCell = mMgdScript.constructFreshTermVariable(s_AUX_VAR_ARRAYCELL, entry.getSort());
			final Term oldValue = oldCellMapping.put(indexRepresentative, oldCell);
			if (oldValue != null) {
				throw new AssertionError("must not insert twice");
			}

		}

	}

	private Term getIndexOfSelect(final ApplicationTerm appTerm) {
		assert (appTerm.getParameters().length == 2) : "no select";
		assert (appTerm.getFunction().getName().equals("select")) : "no select";
		return appTerm.getParameters()[1];
	}

	private Term getArrayOfSelect(final ApplicationTerm appTerm) {
		assert (appTerm.getParameters().length == 2) : "no select";
		assert (appTerm.getFunction().getName().equals("select")) : "no select";
		return appTerm.getParameters()[0];
	}

	private List<MultiDimensionalStore> extractStores(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalStore> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("store", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(new MultiDimensionalStore(appTerm));
			}
		}
		return result;
	}

	private List<MultiDimensionalSelect> extractSelects(final TermVariable eliminatee, final Term term) {
		final List<MultiDimensionalSelect> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("select", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(new MultiDimensionalSelect(appTerm));
			}
		}
		return result;
	}

	private List<ApplicationTerm> extractSelects2(final TermVariable eliminatee, final Term term) {
		final List<ApplicationTerm> result = new ArrayList<>();
		final Set<ApplicationTerm> stores = new ApplicationTermFinder("select", false).findMatchingSubterms(term);
		for (final ApplicationTerm appTerm : stores) {
			if (appTerm.getParameters()[0].equals(eliminatee)) {
				result.add(appTerm);
			}
		}
		return result;
	}

	private static List<Doubleton<Term>> buildListOfNonDisjointDoubletons(final Collection<Term> indices,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		final List<Doubleton<Term>> doubeltons = new ArrayList<>();
		final List<Term> indexList = new ArrayList<>(indices);
		for (int i = 0; i < indexList.size(); i++) {
			if (!equalityInformation.isRepresentative(indexList.get(i))) {
				continue;
			}
			for (int j = i + 1; j < indexList.size(); j++) {
				if (!equalityInformation.isRepresentative(indexList.get(j))) {
					continue;
				}
				if (equalityInformation.getEqualityStatus(indexList.get(i),
						indexList.get(j)) == EqualityStatus.NOT_EQUAL) {
					// do nothing
				} else {
					doubeltons.add(new Doubleton<>(indexList.get(i), indexList.get(j)));
				}
			}
		}
		return doubeltons;
	}

	private class Orac implements IExternalOracle<Term> {

		IncrementalPlicationChecker mIncrementalPlicationChecker;

		public Orac(final Term inputTerm) {
			mIncrementalPlicationChecker = new IncrementalPlicationChecker(Plication.IMPLICATION, mMgdScript,
					inputTerm);
		}

		@Override
		public boolean isConsistent(final LinkedList<Boolean> stack,
				final List<Doubleton<Term>> nonDisjointDoubletons) {
			final List<Term> list = new ArrayList<>();
			for (int i = 0; i < stack.size(); i++) {
				Term equality;
				final Doubleton<Term> d = nonDisjointDoubletons.get(i);
				if (stack.get(i)) {
					equality = SmtUtils.binaryEquality(mScript, d.getOneElement(), d.getOtherElement());
				} else {
					equality = SmtUtils.distinct(mScript, d.getOneElement(), d.getOtherElement());
				}
				list.add(equality);
			}
			final Term conjunction = SmtUtils.and(mScript, list);
			final LBool lbool = mIncrementalPlicationChecker.checkSat(conjunction);
			mLogger.info("external oracle said: " + lbool + " " + stack
					+ (stack.size() == nonDisjointDoubletons.size() ? " full stack!" : ""));
			switch (lbool) {
			case SAT:
				return true;
			case UNKNOWN:
				// TODO: use same as sat
				throw new AssertionError("solver said unknown during conistency check");
			case UNSAT:
				return false;
			default:
				throw new AssertionError("unknown Lbool");
			}
		}

		public void unlockSolver() {
			mIncrementalPlicationChecker.unlockSolver();
		}

	}

	public class ValueEqualityChecker {
		final TermVariable mEliminatee;
		final Term mStoreIndex;
		final Term mStoreValue;
		final ThreeValuedEquivalenceRelation<Term> mIndices;
		final ManagedScript mMgdScript;
		final IncrementalPlicationChecker mIncrementalPlicationChecker;
		final Map<Term, Term> mOldCellMapping;
		final List<Term> mValueEqualities = new ArrayList<>();

		public ValueEqualityChecker(final TermVariable eliminatee, final Term storeIndex, final Term storeValue,
				final ThreeValuedEquivalenceRelation<Term> indices, final ManagedScript mgdScript,
				final IncrementalPlicationChecker incrementalPlicationChecker, final Map<Term, Term> oldCellMapping) {
			super();
			mEliminatee = eliminatee;
			mStoreIndex = storeIndex;
			mStoreValue = storeValue;
			mIndices = indices;
			mMgdScript = mgdScript;
			mIncrementalPlicationChecker = incrementalPlicationChecker;
			mOldCellMapping = oldCellMapping;
		}

		public boolean isDistinguishworthyIndexPair(final Term index1, final Term index2) {
			final Term select1 = mMgdScript.getScript().term("select", mEliminatee, index1);
			final Term select2 = mMgdScript.getScript().term("select", mEliminatee, index2);
			final Term eq = SmtUtils.binaryEquality(mMgdScript.getScript(), select1, select2);
			final Validity cellEqVal = mIncrementalPlicationChecker.checkPlication(eq);
			if (cellEqVal == Validity.VALID) {
				final boolean distinguishworthy1 = processStoreIndex(index1, index2, select2);
				final boolean distinguishworthy2 = processStoreIndex(index2, index1, select1);
				if (distinguishworthy1 && distinguishworthy2) {
					return true;
				} else {
					final Term cellEq = SmtUtils.binaryEquality(mMgdScript.getScript(), mOldCellMapping.get(index1),
							mOldCellMapping.get(index2));
					mValueEqualities.add(cellEq);
					return false;
				}
			} else {
				return true;
			}
		}

		private boolean processStoreIndex(final Term storeIndexCandidate, final Term otherIndex,
				final Term otherSelect) {
			if (isStoreIndex(storeIndexCandidate)) {
				final Term storeEq = SmtUtils.binaryEquality(mMgdScript.getScript(), mStoreValue, otherSelect);
				final Validity storeEqVal = mIncrementalPlicationChecker.checkPlication(storeEq);
				if (storeEqVal == Validity.VALID) {
					final Term storeCellEq = SmtUtils.binaryEquality(mMgdScript.getScript(), mStoreValue,
							mOldCellMapping.get(otherIndex));
					mValueEqualities.add(storeCellEq);
					return false;
				} else {
					return true;
				}
			} else {
				return false;
			}
		}

		boolean isStoreIndex(final Term index1) {
			if (mStoreIndex == null) {
				return false;
			} else {
				return mIndices.getRepresentative(index1).equals(mIndices.getRepresentative(mStoreIndex));
			}
		}

		public List<Term> getValueEqualities() {
			return mValueEqualities;
		}

	}

	private static Term constructWriteConstraints(final ArrayList<Term> selectIndexRepresentatives,
			final ThreeValuedEquivalenceRelation<Term> equalityInformation, final ManagedScript mgdScript,
			final Map<Term, Term> rawIndex2replacedIndex, final Map<Term, ? extends Term> index2value,
			final TermVariable eliminatee, final int quantifier, final Term storeIndex, final Term newAuxArray,
			final Term newValue) {
		final List<Term> resultConjuncts = new ArrayList<Term>();
		for (final Term selectIndexRepresentative : selectIndexRepresentatives) {
			assert equalityInformation.isRepresentative(selectIndexRepresentative) : "no representative: " + selectIndexRepresentative;
			final Term replacementStoreIndex = rawIndex2replacedIndex.get(storeIndex);
			assert !occursIn(eliminatee, replacementStoreIndex) : "var is still there";
			final Term replacementSelectIndex = rawIndex2replacedIndex.get(selectIndexRepresentative);
			assert !occursIn(eliminatee, replacementSelectIndex) : "var is still there";
			final Term indexEquality = PartialQuantifierElimination.equalityForExists(mgdScript.getScript(),
					quantifier, replacementStoreIndex, replacementSelectIndex);
			final Term newSelect = mgdScript.getScript().term("select", newAuxArray, replacementSelectIndex);
			final Term newValueInCell = PartialQuantifierElimination.equalityForExists(mgdScript.getScript(),
					quantifier, newSelect, newValue);
			final EqualityStatus eqStatus = equalityInformation.getEqualityStatus(storeIndex, selectIndexRepresentative);
			switch (eqStatus) {
			case EQUAL:
				resultConjuncts.add(newValueInCell);
				continue;
			case NOT_EQUAL:
				// case handled via substitution
				continue;
			case UNKNOWN: {
				final Term succedent = newValueInCell;
				final Term negatedAntecedent = SmtUtils.not(mgdScript.getScript(), indexEquality);
				final Term positiveCase = SmtUtils.or(mgdScript.getScript(), negatedAntecedent, succedent);
				resultConjuncts.add(positiveCase);
			}
			{
				final Term oldCellValue = index2value.get(selectIndexRepresentative);
				final Term oldValueInCell = PartialQuantifierElimination.equalityForExists(mgdScript.getScript(),
						quantifier, newSelect, oldCellValue);
				final Term negatedAntecedent = indexEquality;
				final Term negativeCase = SmtUtils.or(mgdScript.getScript(), negatedAntecedent, oldValueInCell);
				resultConjuncts.add(negativeCase);
				break;
			}
			default:
				throw new AssertionError();
			}

		}
		final Term resultConjunction = SmtUtils.and(mgdScript.getScript(), resultConjuncts);
		return resultConjunction;

	}

	public static Term constructIndexValueConnection(final ArrayList<Term> selectIndices,
			final ThreeValuedEquivalenceRelation<Term> indexEqualityInformation, final ManagedScript mgdScript,
			final Map<Term, Term> rawIndex2replacedIndex, final Map<Term, ? extends Term> index2value,
			final TermVariable eliminatee, final int quantifier, final Term storeIndex) {
		final List<Term> resultConjuncts = new ArrayList<Term>();
		for (int i = 0; i < selectIndices.size(); i++) {
			for (int j = i+1; j < selectIndices.size(); j++) {
				if (!indexEqualityInformation.isRepresentative(selectIndices.get(j))) {
					throw new AssertionError("representatives only");
				}
				final Term index1 = selectIndices.get(i);
				final Term index2 = selectIndices.get(j);

				if (storeIndex != null && 
						indexEqualityInformation.getEqualityStatus(index1, storeIndex) == EqualityStatus.NOT_EQUAL &&
						indexEqualityInformation.getEqualityStatus(index2, storeIndex) == EqualityStatus.NOT_EQUAL) {
					// If both indices are different from the store index we can
					// omit this conjunct. The corresponding old values of the array
					// will be represented by the new array, hence the congruence
					// information is already provided by the array theory.
					continue;
				}

				final Term indexEqualityTerm;
				final EqualityStatus eqStatus = indexEqualityInformation.getEqualityStatus(index1, index2);
				switch (eqStatus) {
				case EQUAL:
					indexEqualityTerm = mgdScript.getScript().term("true");
					break;
				case NOT_EQUAL:
					indexEqualityTerm = mgdScript.getScript().term("false");
					break;
				case UNKNOWN:
					final Term replacementIndex1 = rawIndex2replacedIndex.get(index1);
					assert !occursIn(eliminatee, replacementIndex1) : "var is still there";
					final Term replacementIndex2 = rawIndex2replacedIndex.get(index2);
					assert !occursIn(eliminatee, replacementIndex2) : "var is still there";
					indexEqualityTerm = SmtUtils.binaryEquality(mgdScript.getScript(), replacementIndex1,
							replacementIndex2);
					break;
				default:
					throw new AssertionError();
				}
				if (SmtUtils.isFalse(indexEqualityTerm)) {
					// conjunct will become true
					continue;
				}
				final Term value1 = index2value.get(index1);
				assert !occursIn(eliminatee, value1) : "var is still there";
				final Term value2 = index2value.get(index2);
				assert !occursIn(eliminatee, value2) : "var is still there";
				final Term valueEqualityTerm = SmtUtils.binaryEquality(mgdScript.getScript(), value1, value2);
				final Term implication = SmtUtils.or(mgdScript.getScript(),
						SmtUtils.not(mgdScript.getScript(), indexEqualityTerm), valueEqualityTerm);
				resultConjuncts.add(implication);
			}
		}
		final Term resultConjunction = SmtUtils.and(mgdScript.getScript(), resultConjuncts);
		if (quantifier == QuantifiedFormula.EXISTS) {
			return resultConjunction;
		} else if (quantifier == QuantifiedFormula.FORALL) {
			return SmtUtils.not(mgdScript.getScript(), resultConjunction);
		} else {
			throw new AssertionError("unknown quantifier");
		}

	}

	public static boolean occursIn(final TermVariable tv, final Term term) {
		return Arrays.asList(term.getFreeVars()).contains(tv);
	}

	private class AuxVarConstructor {
		private final Set<TermVariable> mConstructedAuxVars = new HashSet<>();

		public TermVariable constructAuxVar(final String purpose, final Sort sort) {
			final TermVariable auxVar = mMgdScript.constructFreshTermVariable(purpose, sort);
			mConstructedAuxVars.add(auxVar);
			return auxVar;
		}

		public Set<TermVariable> getConstructedAuxVars() {
			return mConstructedAuxVars;
		}

	}

	private class EqProvider {
		private final Term[] mContext;
		private final TermVariable mEliminatee;
		private final int mQuantifier;

		public EqProvider(final Term inputTerm, final TermVariable eliminatee, final int quantifier) {
			mContext = PartialQuantifierElimination.getXjunctsInner(quantifier, inputTerm);
			mEliminatee = eliminatee;
			mQuantifier = quantifier;
		}

		public Term getEqTerm(final Term term) {
			final EqualityInformation eqInfo = EqualityInformation.getEqinfo(mScript, term, mContext, mEliminatee,
					mQuantifier);
			if (eqInfo == null) {
				return null;
			} else {
				return eqInfo.getTerm();
			}
		}
	}

	/**
	 * Let eliminatee be the array that is eliminated and (select eliminatee idx
	 * v) a select term. If idx contains eliminatee, we have to replace idx by
	 * an auxiliary variable. As an optimization, we only construct one
	 * auxiliary variable for each equivalence class of indices.
	 */
	private class IndexMappingProvider {

		private final Map<Term, Term> mIndexReplacementMapping = new HashMap<>();
		private final List<Term> mIndexMappingDefinitions = new ArrayList<>();

		public IndexMappingProvider(final List<Term> indices, final TermVariable eliminatee,
				final ThreeValuedEquivalenceRelation<Term> equalityInformation,
				final AuxVarConstructor auxVarConstructor, final int quantifier) {

			final IValueConstruction<Term, TermVariable> valueConstruction = new IValueConstruction<Term, TermVariable>() {

				@Override
				public TermVariable constructValue(final Term index) {
					final TermVariable indexReplacement = auxVarConstructor.constructAuxVar(s_AUX_VAR_INDEX,
							index.getSort());
					return indexReplacement;
				}

			};
			final ConstructionCache<Term, TermVariable> cc = new ConstructionCache<>(valueConstruction);
			for (final Term index : indices) {
				final Term eqTerm = findNiceReplacementForRepresentative(index, eliminatee, equalityInformation);
				if (eqTerm != null) {
					mIndexReplacementMapping.put(index, eqTerm);
				} else {
					// need to introduce auxiliary variable
					final Term indexRepresentative = equalityInformation.getRepresentative(index);
					final TermVariable indexReplacement = cc.getOrConstruct(indexRepresentative);
					mIndexReplacementMapping.put(index, indexReplacement);
					mIndexMappingDefinitions.add(PartialQuantifierElimination.equalityForExists(mScript, quantifier,
							indexReplacement, index));
				}
			}
		}



		public Map<Term, Term> getIndexReplacementMapping() {
			return mIndexReplacementMapping;
		}

		public List<Term> getIndexMappingDefinitions() {
			return mIndexMappingDefinitions;
		}

	}
	
	private static Term findNiceReplacementForRepresentative(final Term rep,
			final TermVariable eliminatee, final ThreeValuedEquivalenceRelation<Term> equalityInformation) {
		assert equalityInformation.isRepresentative(rep) : "Not representative " + rep;
		final Set<Term> eq = equalityInformation.getEquivalenceClass(rep);
		final List<Term> list = eq.stream().filter(x -> !occursIn(eliminatee, x)).collect(Collectors.toList());
		if (list.isEmpty()) {
			return null;
		} else {
			
		}
		Collections.sort(list, mFewerVariablesFirst);
		return list.get(0);
	}

}

// similar
// (i == storeIdx) ==> (a[i] == newValue && forall k. i == k ==> oldCell_i ==
// oldCell_k)
// (i != storeIdx) ==> (a[i] == oldCell_i
