/*
 * Copyright (C) 2016 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
 *
 * This file is part of the ULTIMATE HeapSeparator plug-in.
 *
 * The ULTIMATE HeapSeparator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE HeapSeparator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE HeapSeparator plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE HeapSeparator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE HeapSeparator plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieNonOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.LocalBoogieVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.DefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transformations.IntraproceduralReplacementVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.ProgramVarUtils;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityAnalysisResultProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.equalityanalysis.IEqualityProvidingState;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.vp.VPDomainSymmetricPair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedMap2;

/**
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class NewArrayIdProvider {
	
	private final Map<Set<Term>, PartitionInformation> mArrayToPartitionInformation = new HashMap<>();
	private final DefaultIcfgSymbolTable mNewSymbolTable;
	
	private final Map<Term, Set<Term>> mArrayIdToArrayGroup = new HashMap<>();

	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;
	private final HeapSeparatorBenchmark mStatistics;

	public NewArrayIdProvider(final CfgSmtToolkit csToolkit, 
			IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider, 
			HeapSepPreAnalysis hspav, HeapSeparatorBenchmark statistics) {
		mManagedScript = csToolkit.getManagedScript();
		mOldSymbolTable = csToolkit.getSymbolTable();
		mNewSymbolTable = new DefaultIcfgSymbolTable(csToolkit.getSymbolTable(), csToolkit.getProcedures());
		mStatistics = statistics;
		
		processAbstractInterpretationResult(equalityProvider, hspav);
	}
	
	/**
	 *
	 * @param equalityProvider
	 * @param hspav
	 * @return a map of the form (unseparated array --> index --> separated array)
	 */
	private void processAbstractInterpretationResult(
			final IEqualityAnalysisResultProvider<IcfgLocation, IIcfg<?>> equalityProvider,
			final HeapSepPreAnalysis hspav) {
		
		/*
		 * compute which arrays are equated somewhere in the program and thus need the same partitioning
		 */
		final UnionFind<Term> arrayGroupingUf = new UnionFind<>();
		for (final Term array : hspav.getArrayToAccessLocations().getDomain()) {
			arrayGroupingUf.findAndConstructEquivalenceClassIfNeeded(array);
		}
		for (final VPDomainSymmetricPair<Term> pair : hspav.getArrayEqualities()) {
			if (arrayGroupingUf.find(pair.getFirst()) == null) {
				continue;
			}
			if (arrayGroupingUf.find(pair.getSecond()) == null) {
				continue;
			}
			arrayGroupingUf.union(pair.getFirst(), pair.getSecond());
		}
		arrayGroupingUf.getAllEquivalenceClasses();

		mStatistics.setNoArrays(hspav.getArrayToAccessLocations().getDomain().size());
		mStatistics.setNoArrayGroups(arrayGroupingUf.getAllEquivalenceClasses().size());
		
		final HashRelation<Set<Term>, IcfgLocation> arrayGroupToAccessLocations = new HashRelation<>();
		
		for (final Set<Term> ec : arrayGroupingUf.getAllEquivalenceClasses()) {
			for (final Term array : ec) {
				for (final IcfgLocation loc : hspav.getArrayToAccessLocations().getImage(array)) {
					arrayGroupToAccessLocations.addPair(ec, loc);
				}
			}
		}
		
		final Map<Set<Term>, IEqualityProvidingState> arrayGroupToVPState = new HashMap<>();
		for (final Set<Term> arrayGroup : arrayGroupingUf.getAllEquivalenceClasses()) {
			final Set<IcfgLocation> arrayGroupAccessLocations = arrayGroupToAccessLocations.getImage(arrayGroup);
			arrayGroupToVPState.put(arrayGroup, 
					equalityProvider.getEqualityProvidingStateForLocationSet(arrayGroupAccessLocations));
		}
			
		
		/*
		 * Compute the actual partitioning for each array.
		 */
		for (final Entry<Set<Term>, IEqualityProvidingState> en : arrayGroupToVPState.entrySet()) {
			final Set<Term> arrayGroup = en.getKey();
			final IEqualityProvidingState state = en.getValue();
			
			final UnionFind<List<Term>> uf = new UnionFind<>();
			for (final List<Term> accessingTerm : hspav.getAccessingIndicesForArrays(arrayGroup)) {
				uf.findAndConstructEquivalenceClassIfNeeded(accessingTerm);
			}
			// TODO: optimization: compute partitioning on the equivalence class representatives instead
			// of all nodes
			for (final List<Term> accessingNode1 : hspav.getAccessingIndicesForArrays(arrayGroup)) {
				for (final List<Term> accessingNode2 : hspav.getAccessingIndicesForArrays(arrayGroup)) {
					assert accessingNode1.size() == accessingNode2.size();
					boolean anyUnequal = false;
					for (int i = 0; i < accessingNode1.size(); i++) {
						anyUnequal |= state.areUnequal(accessingNode1.get(i), accessingNode2.get(i));
					}
					
					if (!anyUnequal) {
						uf.union(accessingNode1, accessingNode2);
					}
				}
			}
			for (final Set<List<Term>> ec : uf.getAllEquivalenceClasses()) {
				registerEquivalenceClass(arrayGroup, ec);
				mStatistics.incrementEquivalenceClassCounter();
			}
		}
		
	}	
	

	

	/**
	 * Return the partition id of the partitioned array belonging to originalArrayId at position indexVector
	 * @param originalArrayId
	 * @param indexVector
	 * @return
	 */
	public Term getNewArrayId(final Term originalArrayId, final List<Term> indexVector) {
		return mArrayToPartitionInformation
				.get(mArrayIdToArrayGroup.get(originalArrayId))
				.getNewArray(originalArrayId, indexVector);
	}

	public void registerEquivalenceClass(
			final Set<Term> arrayIds, 
			final Set<List<Term>> ec) {
		final IndexPartition indexPartition = new IndexPartition(arrayIds, ec);

		PartitionInformation partitionInfo = mArrayToPartitionInformation.get(arrayIds);
		if (partitionInfo == null) {
			partitionInfo = new PartitionInformation(arrayIds, mManagedScript, mNewSymbolTable, mOldSymbolTable);
			mArrayToPartitionInformation.put(arrayIds, partitionInfo);
		}
		partitionInfo.addPartition(indexPartition);
		
		
		for (Term arrayId : arrayIds) {
			mArrayIdToArrayGroup.put(arrayId, arrayIds);
		}
	}

	public List<Term> getAllNewArrayIds(Term oldLhs) {
		return mArrayToPartitionInformation.get(mArrayIdToArrayGroup.get(oldLhs)).getNewArrayIds().get(oldLhs);
	}
	
	@Override
	public String toString() {
		return "NewArrayIdProvider: \n" + mArrayToPartitionInformation.toString();
	}

	public IIcfgSymbolTable getNewSymbolTable() {
		return mNewSymbolTable;
	}
}

/*
 * Represents a set of Array Indices which, with respect to a given array, may never alias with 
 * the indices in any other partition.
 */
class IndexPartition {
	final Set<Term> arrayIds;
	final Set<List<Term>> indices;

	public IndexPartition(final Set<Term> arrayIds, final Set<List<Term>> indices) {
		this.arrayIds = arrayIds;
		this.indices = Collections.unmodifiableSet(indices);
	}
	
	@Override
	public String toString() {
		return indices.toString();
	}
}

/**
 * Holds partition information for a given array group (as computed by the HeapSepPreAnalysis), i.e. which groups of 
 * indices (called IndexPartitions) may alias, and what new Term/IProgramVar is assigned to it. 
 * Also constructs these new identifiers and updates the new symbol table.
 * 
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
class PartitionInformation {
	/*
	 * an array group in the original program, an groups are formed as arrays that are equated anywhere in the program
	 */
	private final Set<Term> arrayIds;

	int versionCounter = 0;
	private final DefaultIcfgSymbolTable mNewSymbolTable;
	private final List<IndexPartition> indexPartitions;
	
	private final Map<Term, List<Term>> mOldArrayIdToNewArrayIds = new HashMap<>();
	
	final NestedMap2<IndexPartition, Term, Term> indexPartitionToArrayToNewArrayId = new NestedMap2<>();
	
	private final Map<List<Term>, IndexPartition> indexToIndexPartition = new HashMap<>();
	private final ManagedScript mManagedScript;
	private final IIcfgSymbolTable mOldSymbolTable;
	
	public PartitionInformation(final Set<Term> arrayIds, final ManagedScript mScript, 
			final DefaultIcfgSymbolTable newSymbolTable, IIcfgSymbolTable oldSymbolTable) {
		this.arrayIds = arrayIds;
		indexPartitions = new ArrayList<>();
		mManagedScript = mScript;
		mNewSymbolTable = newSymbolTable;
		mOldSymbolTable = oldSymbolTable;
	}
	
	Term getNewArray(final Term oldArrayId, final List<Term> indexVector) {
		assert arrayIds.contains(oldArrayId);
		final IndexPartition ip = indexToIndexPartition.get(indexVector);
		assert indexPartitionToArrayToNewArrayId.get(ip, oldArrayId) != null;
		return indexPartitionToArrayToNewArrayId.get(ip, oldArrayId);
	}

	void addPartition(final IndexPartition ip) {
		indexPartitions.add(ip);
		for (List<Term> index : ip.indices) {
			indexToIndexPartition.put(index, ip);
		}
		constructFreshProgramVarsForIndexPartition(ip);
	}

	private int getFreshVersionIndex() {
		//TODO: a method seems overkill right now -- remove if nothing changes..
		return versionCounter++;
	}

	/**
	 * Given an IndexPartition constructs fresh Terms and ProgramVars for all the arrays in this ParititionInformation's
	 * array group.
	 * Updates the mappings that holds these fresh Terms.
	 * 
	 * @param oldArrayId
	 * @param indexPartition
	 * @return
	 */
	private void constructFreshProgramVarsForIndexPartition(
			IndexPartition indexPartition) {
		mManagedScript.lock(this);
		
		for (Term arrayTv : arrayIds) {
			IProgramVarOrConst arrayPv = mOldSymbolTable.getProgramVar((TermVariable) arrayTv);

			IProgramVarOrConst freshVar = null;
			if (arrayPv instanceof LocalBoogieVar) {
				final LocalBoogieVar lbv = (LocalBoogieVar) arrayPv;
				final String newId = lbv.getIdentifier() + "_part_" + getFreshVersionIndex();
				final TermVariable newTv = mManagedScript.constructFreshCopy(lbv.getTermVariable());

				String constString = newId + "_const";
				mManagedScript.getScript().declareFun(constString, new Sort[0], newTv.getSort());
				final ApplicationTerm newConst = (ApplicationTerm) mManagedScript.term(this, constString);

				String constPrimedString = newId + "_const_primed";
				mManagedScript.getScript().declareFun(constPrimedString, new Sort[0], newTv.getSort());
				final ApplicationTerm newPrimedConst = (ApplicationTerm) mManagedScript.term(this, constPrimedString);

				freshVar = new LocalBoogieVar(
						newId, 
						lbv.getProcedure(), 
						null, 
						newTv, 
						newConst, 
						newPrimedConst);
				mNewSymbolTable.add(freshVar);

				indexPartitionToArrayToNewArrayId.put(indexPartition, arrayTv, newTv);
			} else if (arrayPv instanceof BoogieNonOldVar) {
				// the oldVar may have come up first..
				Term alreadyConstructed = indexPartitionToArrayToNewArrayId.get(indexPartition, arrayTv);
				if (alreadyConstructed == null) {
					BoogieNonOldVar bnovOld = (BoogieNonOldVar) arrayPv;

					final String newId = bnovOld.getIdentifier() + "_part_" + getFreshVersionIndex();

					final BoogieNonOldVar bnovNew = 
							ProgramVarUtils.constructGlobalProgramVarPair(newId, bnovOld.getSort(), mManagedScript, this);

					freshVar = bnovNew;
					mNewSymbolTable.add(freshVar);

					indexPartitionToArrayToNewArrayId.put(indexPartition, arrayTv, freshVar.getTerm());
					indexPartitionToArrayToNewArrayId.put(indexPartition, 
							((BoogieNonOldVar) arrayPv).getOldVar().getTerm(), 
							bnovNew.getOldVar().getTerm());
				} else {
					freshVar = mNewSymbolTable.getProgramVar((TermVariable) alreadyConstructed);
				}
				
			} else if (arrayPv instanceof BoogieOldVar) {
				// the nonOldVar may have come up first..
				Term alreadyConstructed = indexPartitionToArrayToNewArrayId.get(indexPartition, arrayTv);
				if (alreadyConstructed == null) {
					BoogieOldVar bovOld = (BoogieOldVar) arrayPv;

					final String newId = bovOld.getGloballyUniqueId() + "_part_" + getFreshVersionIndex();

					final BoogieNonOldVar bnovNew = 
							ProgramVarUtils.constructGlobalProgramVarPair(newId, bovOld.getSort(), mManagedScript, this);

					freshVar = bnovNew.getOldVar();
					mNewSymbolTable.add(freshVar);

					indexPartitionToArrayToNewArrayId.put(indexPartition, arrayTv, freshVar.getTerm());
					indexPartitionToArrayToNewArrayId.put(indexPartition, 
							((BoogieOldVar) arrayPv).getNonOldVar().getTerm(), 
							bnovNew.getTerm());
				} else {
					freshVar = mNewSymbolTable.getProgramVar((TermVariable) alreadyConstructed);
				}
				assert freshVar != null;
			} else if (arrayPv instanceof IntraproceduralReplacementVar) {
				assert false : "TODO: implement";
			} else if (arrayPv instanceof BoogieConst) {
				assert false : "TODO: implement";
			} else {
				assert false : "case missing --> add it?";
			}


			List<Term> newIdList = mOldArrayIdToNewArrayIds.get(arrayPv);
			if (newIdList == null) {
				newIdList = new ArrayList<>();
				mOldArrayIdToNewArrayIds.put(arrayTv, newIdList);
			}
			newIdList.add(freshVar.getTerm());
		}
		
		mManagedScript.unlock(this);
	}
	
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		
		sb.append(" --- PartitionInformation for array group: " + arrayIds + " --- \n");
		
		sb.append(" " + indexPartitions.size() + " partitions: " + indexPartitions);
		sb.append("\n");
		
		return sb.toString();
	}
	
	Map<Term, List<Term>> getNewArrayIds() {
		return mOldArrayIdToNewArrayIds;
	}
}
