/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE BlockEncodingV2 plug-in.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE BlockEncodingV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BlockEncodingV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BlockEncodingV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE BlockEncodingV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.blockencoding.benchmark;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.BoogieIcfgContainer;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class SizeBenchmark implements ICsvProviderProvider<Integer> {
	
	private final int mEdges;
	private final int mLocations;
	private final String mLabel;
	
	public SizeBenchmark(final BoogieIcfgContainer root, final String label) {
		final Deque<IcfgEdge> edges = new ArrayDeque<>();
		final Set<IcfgEdge> closedE = new HashSet<>();
		final Set<IcfgLocation> closedV = new HashSet<>();
		
		edges.addAll(BoogieIcfgContainer.extractStartEdges(root));
		edges.stream().forEach(e -> closedV.add(e.getSource()));
		
		while (!edges.isEmpty()) {
			final IcfgEdge current = edges.removeFirst();
			if (closedE.contains(current)) {
				continue;
			}
			closedE.add(current);
			
			if (current.getTarget() == null) {
				throw new AssertionError("Target may not be null");
			}
			
			closedV.add(current.getTarget());
			for (final IcfgEdge next : current.getTarget().getOutgoingEdges()) {
				edges.add(next);
			}
		}
		
		mEdges = closedE.size();
		mLocations = closedV.size();
		mLabel = label;
	}
	
	@Override
	public ICsvProvider<Integer> createCvsProvider() {
		final List<String> columnTitles = new ArrayList<>();
		columnTitles.add(mLabel + " Locations");
		columnTitles.add(mLabel + " Edges");
		
		final List<Integer> row = new ArrayList<>();
		row.add(mLocations);
		row.add(mEdges);
		
		final SimpleCsvProvider<Integer> rtr = new SimpleCsvProvider<>(columnTitles);
		rtr.addRow(row);
		return rtr;
	}
	
	@Override
	public String toString() {
		return String.valueOf(mLocations) + " locations, " + String.valueOf(mEdges) + " edges";
	}
	
}