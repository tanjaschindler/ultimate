package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class LassoExtractor<LETTER, STATE> implements IOperation<LETTER,STATE> {

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	private final INestedWordAutomatonSimple<LETTER, STATE> m_Operand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Reach;

	private List<NestedLassoRun<LETTER, STATE>> m_NestedLassoRuns;
	private List<NestedLassoWord<LETTER>> m_NestedLassoWords;

	public LassoExtractor(INestedWordAutomatonSimple<LETTER, STATE> operand) throws OperationCanceledException {
		m_Operand = operand;
		s_Logger.info(startMessage());
		if (m_Operand instanceof NestedWordAutomatonReachableStates) {
			m_Reach = (NestedWordAutomatonReachableStates<LETTER, STATE>) m_Operand;
		} else {
			m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Operand);
		}
		NestedWordAutomatonReachableStates<LETTER, STATE>.StronglyConnectedComponents sccs = 
				m_Reach.getOrComputeStronglyConnectedComponents();
		m_NestedLassoRuns = sccs.getAllNestedLassoRuns();
		m_NestedLassoWords = new ArrayList<NestedLassoWord<LETTER>>(m_NestedLassoRuns.size());
		if (m_NestedLassoRuns.isEmpty() && sccs.getNestedLassoRun() == null) {
			assert (new BuchiIsEmpty<LETTER, STATE>(m_Reach)).getResult();
		} else {
			for (NestedLassoRun<LETTER, STATE> nlr  : m_NestedLassoRuns) {
				m_NestedLassoWords.add(nlr.getNestedLassoWord());
			}
		}
		s_Logger.info(exitMessage());
	}

	@Override
	public List<NestedLassoWord<LETTER>> getResult() throws OperationCanceledException {
		return m_NestedLassoWords;
	}

	@Override
	public String operationName() {
		return "getSomeAcceptedLassoRuns";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand "
				+ m_Operand.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Found " + 
					m_NestedLassoRuns.size() + " examples of accepted words.";
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws OperationCanceledException {
		return true;
	}

}
