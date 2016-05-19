/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.core.model.preferences;

/**
 * A {@link IPreferenceInitializer} contains all preferences (i.e., settings, options) that can be changed by a user to
 * customize a plugin.
 * 
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IPreferenceInitializer {

	/***
	 * This method is called by the preference initializer to initialize default preference values.
	 * 
	 * Note: Clients should not call this method. It will be called automatically by the preference initializer when the
	 * appropriate default preference node is accessed.
	 */
	void initializeDefaultPreferences();

	/**
	 * Reset all preferences of this preference initializer to their default values.
	 */
	void resetToDefaults();

	/**
	 * @return An array of {@link BaseUltimatePreferenceItem}s that define the preferences of this
	 *         {@link IPreferenceInitializer}.
	 */
	BaseUltimatePreferenceItem[] getDefaultPreferences();

	/**
	 * @return a human-readable string that is used as title for the group of preferences represented by this
	 *         initializer.
	 * 
	 */
	String getPreferenceTitle();

}