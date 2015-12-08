package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.direct;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.AGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.SpoilerVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.UnionFind;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public final class DirectGameGraph<LETTER, STATE> extends AGameGraph<LETTER, STATE> {
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Buechi;
	
	private final Logger m_Logger;
	
	private final StateFactory<STATE> m_StateFactory;
	
	public DirectGameGraph(final IUltimateServiceProvider services,
			final INestedWordAutomatonOldApi<LETTER, STATE> buechi,
			final StateFactory<STATE> stateFactory)
					throws OperationCanceledException {
		super(services);
		m_Buechi = buechi;
		m_Logger = getServiceProvider().getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_StateFactory = stateFactory;
		generateGameGraphFromBuechi();
	}

	@Override
	protected NestedWordAutomaton<LETTER, STATE> generateBuchiAutomatonFromGraph()
			throws OperationCanceledException {
		// determine which states to merge
    	UnionFind<STATE> uf = new UnionFind<>();
    	for (STATE state : m_Buechi.getStates()) {
    		uf.makeEquivalenceClass(state);
    	}
    	HashRelation<STATE, STATE> similarStates = new HashRelation<STATE, STATE>();
        for (SpoilerVertex<LETTER,STATE> v : getSpoilerVertices()) {
            // all the states we need are in V1...
            if (v.getPM(null, getGlobalInfinity()) < getGlobalInfinity()) {
            	STATE state1 = v.getQ0();
            	STATE state2 = v.getQ1();
            	similarStates.addPair(state1, state2);
            	
            }
        }
        // merge if bisimilar
        for (STATE state1 : similarStates.getDomain()) {
        	for (STATE state2 : similarStates.getImage(state1)) {
        		if (similarStates.containsPair(state2, state1)) {
        			uf.union(state1, state2);	
        		}
        	}
        }
        
        if (getServiceProvider().getProgressMonitorService() != null
        		&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
            m_Logger.debug("Stopped in generateBuchiAutomaton/table filled");
            throw new OperationCanceledException(this.getClass());
        }

        // merge states
        NestedWordAutomaton<LETTER, STATE> result = new NestedWordAutomaton<LETTER,STATE>(
        		getServiceProvider(), m_Buechi.getInternalAlphabet(), null, null, m_StateFactory);
        Set<STATE> representativesOfInitials = new HashSet<STATE>();
        for (STATE initial : m_Buechi.getInitialStates()) {
        	representativesOfInitials.add(uf.find(initial));
        }
        
        Map<STATE,STATE> input2result = new HashMap<STATE,STATE>(m_Buechi.size());
        for (STATE representative : uf.getAllRepresentatives()) {
        	boolean isInitial = representativesOfInitials.contains(representative);
        	boolean isFinal = m_Buechi.isFinal(representative);
        	Set<STATE> eqClass = uf.getEquivalenceClassMembers(representative);
        	STATE resultState = m_StateFactory.minimize(eqClass);
        	result.addState(isInitial, isFinal, resultState);
        	for (STATE eqClassMember : eqClass) {
        		input2result.put(eqClassMember, resultState);
        	}
        }
        
        for (STATE state : uf.getAllRepresentatives()) {
        	STATE pred = input2result.get(state);
        	for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Buechi.internalSuccessors(state)) {
        		STATE succ = input2result.get(outTrans.getSucc());
        		result.addInternalTransition(pred, outTrans.getLetter(), succ);
        	}
        }
        
        if (getServiceProvider().getProgressMonitorService() != null
        		&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
            m_Logger.debug("Stopped in generateBuchiAutomaton/states added to result BA");
            throw new OperationCanceledException(this.getClass());
        }
        return result;
	}

	@Override
	protected void generateGameGraphFromBuechi() throws OperationCanceledException {
        // Calculate v1 [paper ref 10]
        for (STATE q0 : m_Buechi.getStates()) {
            for (STATE q1 : m_Buechi.getStates()) {
                SpoilerVertex<LETTER,STATE> v1e = new SpoilerVertex<LETTER, STATE>(
                        0, false, q0, q1);
                addSpoilerVertex(v1e);
            }
            
            if (getServiceProvider().getProgressMonitorService() != null
            		&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
                m_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException(this.getClass());
            }
        }
        // Calculate v0 and edges [paper ref 10, 11, 12]
        for (STATE q0 : m_Buechi.getStates()) {
            for (STATE q1 : m_Buechi.getStates()) {
            	Set<LETTER> relevantLetters = new HashSet<LETTER>();
            	relevantLetters.addAll(m_Buechi.lettersInternalIncoming(q0));
            	relevantLetters.addAll(m_Buechi.lettersInternal(q1));
                for (LETTER s : relevantLetters) {
                    DuplicatorVertex<LETTER,STATE> v0e = new DuplicatorVertex<LETTER, STATE>(
                            0, false, q0, q1, s);
                    addDuplicatorVertex(v0e);
                    // V1 -> V0 edges [paper ref 11]
                    for (STATE pred0 : m_Buechi.predInternal(q0, s)) {
                    	//TODO: check conditions
                        if (!m_Buechi.isFinal(pred0) || m_Buechi.isFinal(q1)) {
                            addEdge(getSpoilerVertex(pred0, q1, false), v0e);
                        }
                    }
                    // V0 -> V1 edges [paper ref 11]
                    for (STATE succ1 : m_Buechi.succInternal(q1, s)) {
                    	//TODO: check conditions
                        if (!m_Buechi.isFinal(q0) || m_Buechi.isFinal(succ1)) {
                            addEdge(v0e, getSpoilerVertex(q0, succ1, false));
                        }
                    }
                }
            }
            
            if (getServiceProvider().getProgressMonitorService() != null
            		&& !getServiceProvider().getProgressMonitorService().continueProcessing()) {
                m_Logger.debug("Stopped in generateGameGraph/calculating v0 und v1");
                throw new OperationCanceledException(this.getClass());
            }
        }
        increaseGlobalInfinity();; // global infinity = (# of pr==1 nodes) + 1
        if (m_Logger.isDebugEnabled()) {
            m_Logger.debug("Infinity is " + getGlobalInfinity());
            m_Logger.debug("Number of vertices in game graph: "
                    + (getDuplicatorVertices().size() + getSpoilerVertices().size()));
            m_Logger.debug("Number of vertices in v0: " + getDuplicatorVertices().size());
            m_Logger.debug("Number of vertices in v1: " + getSpoilerVertices().size());
            int edges = 0;
            for (Set<Vertex<LETTER,STATE>> hs : getSuccessorGroups()) {
                edges += hs.size();
            }
            m_Logger.debug("Number of edges in game graph: " + edges);
        }
	}

}
