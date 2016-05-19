/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.boogie.BoogieOldVar;
import de.uni_freiburg.informatik.ultimate.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.ModifiableGlobalVariableManager;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.TransFormula.Infeasibility;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.ICallAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IInternalAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.IReturnAction;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.HoareTripleCheckerStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hoaretriple.IHoareTripleChecker.Validity;

public class SdHoareTripleCheckerHelper {
	
	private final ModifiableGlobalVariableManager m_ModifiableGlobalVariableManager;
	
	private final HoareTripleCheckerStatisticsGenerator m_HoareTripleCheckerStatistics;
	private final IPredicateCoverageChecker m_PredicateCoverageChecker;
	
	
	public SdHoareTripleCheckerHelper(ModifiableGlobalVariableManager modGlobVarManager, 
			IPredicateCoverageChecker predicateCoverageChecker, 
			HoareTripleCheckerStatisticsGenerator edgeCheckerBenchmarkGenerator) {
		m_ModifiableGlobalVariableManager = modGlobVarManager;
		m_PredicateCoverageChecker = predicateCoverageChecker;
		if (edgeCheckerBenchmarkGenerator == null) {
			m_HoareTripleCheckerStatistics = new HoareTripleCheckerStatisticsGenerator();
		} else {
			m_HoareTripleCheckerStatistics = edgeCheckerBenchmarkGenerator;
		}
	}
	
	public SdHoareTripleCheckerHelper(ModifiableGlobalVariableManager modGlobVarManager, 
			HoareTripleCheckerStatisticsGenerator edgeCheckerBenchmarkGenerator) {
		this(modGlobVarManager, null, edgeCheckerBenchmarkGenerator);
	}
	
	
	public HoareTripleCheckerStatisticsGenerator getEdgeCheckerBenchmark() {
		return m_HoareTripleCheckerStatistics;
	}
	
	
	
	private static boolean varSetDisjoint(Set<BoogieVar> set1, Set<BoogieVar> set2) {
		if (set1.size() < set2.size()) {
			for (BoogieVar bv : set1) {
				if (set2.contains(bv)) {
					return false;
				}
			}
		} else {
			for (BoogieVar bv : set2) {
				if (set1.contains(bv)) {
					return false;
				}
			}
		}
		return true;
	}
	
	
	
	
	/**
	 * Idea: If the formula of the code block is satisfiable,
	 * the predecessor is satisfiable and the vars of predecessor are disjoint
	 * from the inVars of the code block, then a transition to false is not
	 * inductive.
	 * Idea with UNKNOWN: if the solver was unable to decide feasibility of cb, 
	 * the predecessor is satisfiable and the vars of predecessor are disjoint
	 * from the inVars of the code block, then the solver will be unable to
	 * show that a transition to false is inductive. 
	 *
	 * FIXME: Check for precondition false, not for precondition true.
	 */
	public Validity sdecInternalToFalse(IPredicate pre, IInternalAction act) {
		Infeasibility infeasiblity = act.getTransformula().isInfeasible();
		if (infeasiblity == Infeasibility.UNPROVEABLE) {
			if (varsDisjoinedFormInVars(pre, act.getTransformula())) {
				m_HoareTripleCheckerStatistics.getSDtfsCounter().incIn();
				return Validity.INVALID;
			} else  {
				return null;
			}
		} else if (infeasiblity == Infeasibility.INFEASIBLE) {
			return Validity.VALID;
		} else if (infeasiblity == Infeasibility.NOT_DETERMINED) {
			return null;
		} else {
			throw new IllegalArgumentException();
		}
	}
	
	
	
	
	/**
	 * Returns true iff the variables occurring in state are disjoint from the
	 * inVars of CodeBlock letter.
	 * @param state
	 * @param symbol
	 * @return
	 */
	private boolean varsDisjoinedFormInVars(IPredicate state, TransFormula tf) {
		for (BoogieVar bv : state.getVars()) {
			if (tf.getInVars().containsKey(bv)) {
				return false;
			}
		}
		return true;
	}
	
	
	/**
	 * FIXME: Mention assumptions.
	 * Idea: If 
	 * <ul>
	 * <li> the formula of the code block is satisfiable, 
	 * <li> the predecessor is satisfiable,
	 * <li> the successor is not unsatisfiable,
	 * <li> the variables of the predecessor are disjoint from the invars
	 * of the code block, and
	 * <li> the variables of the successor are disjoint from the outvars of the
	 * code block, from the invars of the code block and from the vars of the
	 * predecessor,
	 * </ul>
	 * then a transition (pre, act, post) is not inductive. 
	 *
	 * FIXME: Check for preconditions, postcondition? Check at least for
	 * infeasibility flag of TransFormula.
	 */
	public Validity sdecInteral(IPredicate pre, IInternalAction act, IPredicate post) {
		if (m_PredicateCoverageChecker != null) {
			Validity sat = m_PredicateCoverageChecker.isCovered(pre, post);
			if (sat == Validity.VALID) {
				if (Collections.disjoint(pre.getVars(), act.getTransformula().getAssignedVars())) {
					m_HoareTripleCheckerStatistics.getSDsluCounter().incIn();
					return Validity.VALID;
				}
			}
		}
		for (BoogieVar bv : pre.getVars()) {
			if (act.getTransformula().getInVars().containsKey(bv)) {
				return null;
			}
		}
		for (BoogieVar bv : post.getVars()) {
//			if (pre.getVars().contains(bv)) {
//				return null;
//			} else 
			if (act.getTransformula().getInVars().containsKey(bv)) {
				return null;
			} else if (act.getTransformula().getOutVars().containsKey(bv)) {
				return null;
			}
		}
		// now, we know that vars of pre and post are both disjoint from the
		/// vars of cb. Edge is inductive iff pre implies post
		if (m_PredicateCoverageChecker != null) {
			Validity sat = m_PredicateCoverageChecker.isCovered(pre, post);
			if (sat == Validity.VALID) {
				m_HoareTripleCheckerStatistics.getSDsluCounter().incIn();
				return Validity.VALID;
			} else if (sat == Validity.UNKNOWN) {
				return null;
			} else if (sat == Validity.NOT_CHECKED) {
				return null;
			} else if (sat == Validity.INVALID) {
				String proc = act.getPreceedingProcedure();
				assert proc.equals(act.getSucceedingProcedure()) : "internal statement must not change procedure";
				if (m_ModifiableGlobalVariableManager.containsNonModifiableOldVars(pre, proc) || 
						m_ModifiableGlobalVariableManager.containsNonModifiableOldVars(post, proc)) {
					return null;
				} else {
					//continue and return Validity.INVALID
				}
			}
		} else {
			if (!Collections.disjoint(pre.getVars(), post.getVars())) {
				return null;
			}
		}
		m_HoareTripleCheckerStatistics.getSDsCounter().incIn();
		return Validity.INVALID;
	}
	
	
//	public boolean sdecSatAssured(Predicate pre, CodeBlock cb) {
//		Set<BoogieVar> inVars = cb.getTransitionFormula().getInVars().keySet();
//		 if (varSetDisjoint(pre.getVars(), inVars)) {
//			 return true;
//		 }
//		 else return false;
//	}
	
	
	public Validity sdLazyEcInteral(IPredicate pre, IInternalAction act, IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecInteral(pre, act, post);
		}
		for (BoogieVar bv : post.getVars()) {
			if (pre.getVars().contains(bv)) {
				continue;
			} else if (act.getTransformula().getInVars().containsKey(bv)) {
				continue;
			} else if (act.getTransformula().getOutVars().containsKey(bv)) {
				continue;
			}
			// occurs neither in pre not in codeBlock, probably unsat
			m_HoareTripleCheckerStatistics.getSdLazyCounter().incIn();
			return Validity.INVALID;
		}
		return null;
	}
	
	public Validity sdecCallToFalse(IPredicate pre, ICallAction act) {
		// TODO:
		// there could be a contradiction if the Call is not a simple call
		// but interprocedural sequential composition 			
		if (act instanceof ICallAction) {
			m_HoareTripleCheckerStatistics.getSDtfsCounter().incCa();
			return Validity.INVALID;
		} else {
			return null;
		}
	}
	
	public Validity sdecCall(IPredicate pre, ICallAction act, IPredicate post) {
		for (BoogieVar bv : post.getVars()) {
			if (bv.isOldvar()) {
				//if oldVar occurs this edge might be inductive since 
				// old(g)=g is true
				return null;
			} else if (bv.isGlobal()) {
				assert !bv.isOldvar();
				if (pre.getVars().contains(bv)) {
					return null;
				}
			}
		}
		//workaround see preHierIndependent()
		TransFormula locVarAssignTf = act.getLocalVarsAssignment();
		if (!varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
			return null;
		}
		if (preHierIndependent(post, pre, act.getLocalVarsAssignment(), act.getSucceedingProcedure())) {
			m_HoareTripleCheckerStatistics.getSDsCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}
	
	public Validity sdLazyEcCall(IPredicate pre, ICallAction cb, IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecCall(pre, cb, post);
		}
		TransFormula locVarAssignTf = cb.getLocalVarsAssignment();
		boolean argumentsRestrictedByPre = 
				!varSetDisjoint(locVarAssignTf.getInVars().keySet(), pre.getVars());
		for (BoogieVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				continue;
			} else {
				if (locVarAssignTf.getAssignedVars().contains(bv)) {
					if (argumentsRestrictedByPre) {
						continue;
					}
				}
			}
			m_HoareTripleCheckerStatistics.getSdLazyCounter().incCa();
			return Validity.INVALID;
		}
		return null;
	}
	
	
	public Validity sdecReturn(IPredicate pre, IPredicate hier, IReturnAction ret, IPredicate post) {
		if (hierPostIndependent(hier, ret, post) 
				&& preHierIndependent(pre, hier, ret.getLocalVarsAssignmentOfCall(), ret.getPreceedingProcedure())
				&& prePostIndependent(pre, ret, post)) {
			m_HoareTripleCheckerStatistics.getSDsCounter().incRe();
			return Validity.INVALID;

		}
		return null;
	}
	
	
	public Validity sdLazyEcReturn(IPredicate pre, IPredicate hier, IReturnAction ret, IPredicate post) {
		if (isOrIteFormula(post)) {
			return sdecReturn(pre, hier, ret, post);
		}
		Set<BoogieVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		
		/*
		 * Old Version. Does not work if param set to constant.
		 * 
		// If there is an argument in post which is not assigned by return
		// and an parameter is in pre we have to return UNKNOWN
		Map<BoogieVar, TermVariable> arguments = call.getTransitionFormula().getInVars();
		Set<BoogieVar> parameters = call.getTransitionFormula().getAssignedVars();
		if (!varSetDisjoint(parameters, pre.getVars())) {
			for (BoogieVar bv : arguments.keySet()) {
				if (post.getVars().contains(bv) && !assignedVars.contains(bv)) {
					m_LazyEdgeCheckQueries++;
					return null;
				}
			}
		}
		 * 
		 */
		Set<BoogieVar> parameters = ret.getLocalVarsAssignmentOfCall().getAssignedVars();
		if (!varSetDisjoint(parameters, pre.getVars())) {
			return null;
		}

		String proc = ret.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);
		boolean assignedVarsRestrictedByPre = 
				!varSetDisjoint(ret.getAssignmentOfReturn().getInVars().keySet(), pre.getVars());
		for (BoogieVar bv : post.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (hier.getVars().contains(bv)) {
						continue;
					}
				} else {
					if (modifiableGlobals.contains(bv)) {
						if (pre.getVars().contains(bv)) {
							continue;
						}
					} else {
						if (hier.getVars().contains(bv)) {
							continue;
						}
						if (pre.getVars().contains(bv)) {
							continue;
						}

						
					}
					if (assignedVars.contains(bv)) {
						if (assignedVarsRestrictedByPre) {
							continue;
						}
					}
				}
				
			} else {
				if (assignedVars.contains(bv)) {
					if (assignedVarsRestrictedByPre) {
						continue;
					}
				} else {
					if (hier.getVars().contains(bv)) {
						continue;
					}
				}
			}
			m_HoareTripleCheckerStatistics.getSdLazyCounter().incRe();
			return Validity.INVALID;
		}
		return null;
	}
	

	private boolean preHierIndependent(IPredicate pre, IPredicate hier, 
			TransFormula localVarsAssignment, String calledProcedure) {
		//TODO: Matthias 7.10.2012 I hoped following would be sufficient.
		// But this is not sufficient when constant assigned to invar
		// e.g. pre is x!=0 and call is x_Out=1. Might be solved with
		// dataflow map.
		// 8.10.2012 consider also case where inVar is non-modifiable global
		// which does not occur in hier, but in pre
//		if (!varSetDisjoint(hier.getVars(), locVarAssignTf.getInVars().keySet())
//				&& !varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
//			return false;
//		}
		//workaround for preceding problem
		if (!varSetDisjoint(localVarsAssignment.getAssignedVars(), pre.getVars())) {
			return false;
		}
		
		// cases where pre and hier share non-modifiable var g, or
		// g occurs in hier, and old(g) occurs in pre.
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(calledProcedure);

		
		for (BoogieVar bv : pre.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					if (hier.getVars().contains(((BoogieOldVar) bv).getNonOldVar())) {
						return false;
					}
				} else {
					if (!modifiableGlobals.contains(bv) 
							&& hier.getVars().contains(bv)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	private boolean prePostIndependent(IPredicate pre, IReturnAction ret, IPredicate post) {
		TransFormula returnAssignTf = ret.getAssignmentOfReturn();
		if (!varSetDisjoint(pre.getVars(), returnAssignTf.getInVars().keySet())
				&& !varSetDisjoint(returnAssignTf.getAssignedVars(), post.getVars())) {
			return false;
		}
		TransFormula locVarAssignTf = ret.getLocalVarsAssignmentOfCall();
		if (!varSetDisjoint(post.getVars(), locVarAssignTf.getInVars().keySet())
				&& !varSetDisjoint(locVarAssignTf.getAssignedVars(), pre.getVars())) {
			return false;
		}
		for (BoogieVar bv : pre.getVars()) {
			if (bv.isGlobal() && !bv.isOldvar()) {
				if (pre.getVars().contains(bv)) {
					return false;
				}
			}
		}
		return true;
	}
	
	
	private boolean hierPostIndependent(IPredicate hier, IReturnAction ret, IPredicate post) {
		Set<BoogieVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		
		String proc = ret.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);
		
		for (BoogieVar bv : post.getVars()) {
			if (modifiableGlobals.contains(bv)) {
				//do nothing
				continue;
			}
			if (assignedVars.contains(bv)) {
				//do nothing
				continue;
			}
			if (hier.getVars().contains(bv)) {
				return false;
			}
		}
		return true;
	}
	
	
	
	
	/**
	 * If the assigned vars of cb are disjoint from the variables in p the
	 * selfloop (p,cb,p) is trivially inductive.
	 * Returns HTTV.VALID if selfloop is inductive. Returns null if we are
	 * not able to determinie inductivity selfloop. 
	 */
	public Validity sdecInternalSelfloop(IPredicate p, IInternalAction act) {
		Set<BoogieVar> assignedVars = act.getTransformula().getAssignedVars();
		Set<BoogieVar> occVars = p.getVars();
		for (BoogieVar occVar : occVars) {
			if (assignedVars.contains(occVar)) {
				return null;
			}
		}
		m_HoareTripleCheckerStatistics.getSDsluCounter().incIn();
		return Validity.VALID;
	}
	
	
	/**
	 * Returns UNSAT if p contains only non-old globals.
	 */
	public Validity sdecCallSelfloop(IPredicate p, ICallAction call) {
		for (BoogieVar bv : p.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return null;
				} 
			} else {
				return null;
			}
		}
		m_HoareTripleCheckerStatistics.getSDsluCounter().incCa();
		return Validity.VALID;
	}
	
	
	
	public Validity sdecReturnSelfloopPre(IPredicate p, IReturnAction ret) {
		Set<BoogieVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		for (BoogieVar bv : p.getVars()) {
			if (bv.isGlobal()) {
				if (bv.isOldvar()) {
					return null;
				} else {
					if (assignedVars.contains(bv)) {
						return null;
					}
				}
			} else {
				return null;
			}
		}
		m_HoareTripleCheckerStatistics.getSDsluCounter().incRe();
		return Validity.VALID;
	}
	
	
	public Validity sdecReturnSelfloopHier(IPredicate p, IReturnAction ret) {
		Set<BoogieVar> assignedVars = ret.getAssignmentOfReturn().getAssignedVars();
		String proc = ret.getPreceedingProcedure();
		Set<BoogieVar> modifiableGlobals = 
				m_ModifiableGlobalVariableManager.getModifiedBoogieVars(proc);

		for (BoogieVar bv : p.getVars()) {
			if (modifiableGlobals.contains(bv)) {
				return null;
			}
			if (assignedVars.contains(bv)) {
				return null;
			}
		}
		return Validity.VALID;
	}
	

	/**
	 * Returns true if the formula of this predicate is an or-term or an
	 * ite-term.
	 */
	private boolean isOrIteFormula(IPredicate p) {
		Term formula = p.getFormula();
		if (formula instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) formula;
			FunctionSymbol symbol = appTerm.getFunction();
			boolean result = symbol.getName().equals("or") || 
					symbol.getName().equals("ite"); 
			return result;
		} else {
			return false;
		}
	}}