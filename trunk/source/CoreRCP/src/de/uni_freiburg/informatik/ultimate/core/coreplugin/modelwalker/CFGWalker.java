/*
 * Copyright (C) 2012-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2008-2015 Evren Ermis
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Core.
 * 
 * The ULTIMATE Core is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Core is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Core. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Core, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Core grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.core.coreplugin.modelwalker;

import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.lib.models.WrapperNode;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;
import de.uni_freiburg.informatik.ultimate.core.model.models.IWalkable;
import de.uni_freiburg.informatik.ultimate.core.model.observers.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class CFGWalker extends BaseWalker {

	private HashSet<IWalkable> mVisitedNodes = new HashSet<IWalkable>();

	public CFGWalker(ILogger logger) {
		super(logger);
	}

	@Override
	protected void runObserver(IElement element, IUnmanagedObserver observer) throws Throwable {
		IElement tobeproccessed = element;
		if (element instanceof WrapperNode) {
			WrapperNode wnode = (WrapperNode) element;
			if (wnode.getBacking() instanceof IElement) {
				tobeproccessed = (IElement) wnode.getBacking();
			}
		}

		if (observer.process(tobeproccessed)) {
			if (element instanceof IWalkable) {
				IWalkable node = (IWalkable) element;

				if (mVisitedNodes.contains(node)) {
					return;
				} else {
					mVisitedNodes.add(node);
					List<IWalkable> outgoings = node.getSuccessors();
					if (outgoings != null) {
						for (IWalkable i : outgoings) {
							runObserver(i, observer);
						}
					}
				}

			}
		}
	}

}