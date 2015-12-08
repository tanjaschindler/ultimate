/*
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * Copyright (C) 2013-2015 Vincent Langenfeld (langenfv@informatik.uni-freiburg.de)
 * 
 * This file is part of the ULTIMATE BuchiProgramProduct plug-in.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE BuchiProgramProduct plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE BuchiProgramProduct plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE BuchiProgramProduct plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE BuchiProgramProduct plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.buchiprogramproduct;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.optimizercfg.SmallBlockEncoder;
import de.uni_freiburg.informatik.ultimate.buchiprogramproduct.preferences.PreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceStore;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.util.CoreUtil;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IGenerator;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CodeBlock;
import de.uni_freiburg.informatik.ultimate.result.CounterExampleResult;

/**
 * This plugin implements the product algorithm described in the Masterthesis
 * "Automatische Generierungvon Buchi-Programmen".
 * 
 * 
 * @author Langenfeld
 * 
 * 
 */
public class BuchiProgramProduct implements IGenerator {

	private Logger mLogger;
	private BuchiProductObserver mBuchiProductObserver;
	private boolean mUseBuchiProductObserver;
	private boolean mPreviousToolFoundErrors;
	private IUltimateServiceProvider mServices;
	private int mUseful;
	private boolean mModelIsRCFG;

	private ProductBacktranslator mBacktranslator;
	private IToolchainStorage mStorage;

	@Override
	public GraphType getOutputDefinition() {
		if (mPreviousToolFoundErrors) {
			return null;
		}

		List<String> filenames = new ArrayList<String>();
		filenames.add("LTL+Program Product");
		return new GraphType(Activator.PLUGIN_ID, GraphType.Type.OTHER, filenames);
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		if (mPreviousToolFoundErrors) {
			return QueryKeyword.LAST;
		}
		return QueryKeyword.ALL;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {
		switch (graphType.getCreator()) {
		case "de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder":
			mModelIsRCFG = true;
		case "de.uni_freiburg.informatik.ultimate.ltl2aut":
			mUseBuchiProductObserver = true;
			mUseful++;
			break;
		default:
			mUseBuchiProductObserver = false;
			mModelIsRCFG = false;
			break;
		}
	}

	@Override
	public List<IObserver> getObservers() {
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		if (!mPreviousToolFoundErrors) {
			if (mModelIsRCFG
					&& new UltimatePreferenceStore(Activator.PLUGIN_ID).getBoolean(PreferenceInitializer.OPTIMIZE_SBE)) {
				observers.add(new SmallBlockEncoder(mLogger, mBacktranslator, mStorage));
			}

			if (mUseBuchiProductObserver) {
				if (mBuchiProductObserver == null) {
					mBuchiProductObserver = new BuchiProductObserver(mLogger, mServices, mBacktranslator, mStorage);
				}
				observers.add(mBuchiProductObserver);
			}
		}
		return observers;
	}

	@Override
	public void init() {
		mUseBuchiProductObserver = false;
		mModelIsRCFG = false;
		mUseful = 0;
	}

	@Override
	public String getPluginName() {
		return Activator.PLUGIN_NAME;
	}

	@Override
	public String getPluginID() {
		return Activator.PLUGIN_ID;
	}

	@Override
	public IElement getModel() {
		if (mBuchiProductObserver.getModel() != null) {
			return mBuchiProductObserver.getModel();
		} else {
			return null;
		}
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public UltimatePreferenceInitializer getPreferences() {
		return new PreferenceInitializer();
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		mStorage = storage;
	}

	@SuppressWarnings("rawtypes")
	@Override
	public void setServices(IUltimateServiceProvider services) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
		Collection<CounterExampleResult> cex = CoreUtil.filterResults(services.getResultService().getResults(),
				CounterExampleResult.class);
		mPreviousToolFoundErrors = !cex.isEmpty();
		mBacktranslator = new ProductBacktranslator(CodeBlock.class, Expression.class);
		if (!mPreviousToolFoundErrors) {
			mServices.getBacktranslationService().addTranslator(mBacktranslator);
		}
	}

	@Override
	public void finish() {
		if (!mPreviousToolFoundErrors && mUseful == 0) {
			throw new IllegalStateException("Was used in a toolchain were it did nothing");
		}
		if (mPreviousToolFoundErrors) {
			mLogger.info("Another plugin discovered errors, skipping...");
		}
	}

}
