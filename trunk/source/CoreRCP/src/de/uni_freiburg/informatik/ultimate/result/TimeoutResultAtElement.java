/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 Evren Ermis
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.result;

import de.uni_freiburg.informatik.ultimate.core.services.model.IBacktranslationService;
import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * Use this to report that there was a timeout.
 * The ELEM of this object is a node in the Ultimate model that is related to
 * the problem that was analyzed when this timeout occurred.
 * @author Matthias Heizmann
 *
 * @param <ELEM>
 */
public class TimeoutResultAtElement<ELEM extends IElement> 
					extends AbstractResultAtElement<ELEM> implements IResult, ITimeoutResult {
	
	private final String m_longDescription;


	public TimeoutResultAtElement(ELEM element, String plugin, 
			IBacktranslationService translatorSequence, String longDescription) {
		super(element, plugin, translatorSequence);
		this.m_longDescription = longDescription;
	}
	
	@Override
	public String getShortDescription() {
		return "Timeout (" + mPlugin + ")";
	}

	@Override
	public String getLongDescription() {
		return m_longDescription;
	}

	
}
