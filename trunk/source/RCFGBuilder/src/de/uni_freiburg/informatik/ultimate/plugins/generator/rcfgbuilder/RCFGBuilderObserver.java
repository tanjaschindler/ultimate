/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2010-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 * 
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder;

import java.io.IOException;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IUnmanagedObserver;
import de.uni_freiburg.informatik.ultimate.access.WalkerOptions;
import de.uni_freiburg.informatik.ultimate.core.services.model.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.model.GraphType;
import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.model.ModelUtils;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Unit;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.CfgBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RootNode;

/**
 * Auto-Generated Stub for the plug-in's Observer
 */
public class RCFGBuilderObserver implements IUnmanagedObserver {

	/**
	 * Root Node of this Ultimate model. I use this to store information that
	 * should be passed to the next plugin. The Sucessors of this node exactly
	 * the initial nodes of procedures.
	 */
	private RootNode mGraphroot;

	/**
	 * Logger for this plugin.
	 */
	private final Logger mLogger;

	private final IUltimateServiceProvider mServices;

	private final IToolchainStorage mStorage;

	public RCFGBuilderObserver(IUltimateServiceProvider services, IToolchainStorage storage) {
		mServices = services;
		mStorage = storage;
		mLogger = mServices.getLoggingService().getLogger(Activator.PLUGIN_ID);
	}

	/**
	 * 
	 * @return the root of the CFG.
	 */
	public RootNode getRoot() {
		return mGraphroot;
	}

	/**
	 * Copied from CFG Builder
	 * 
	 * Called by the Ultimate Framework. Finds all procedure declarations and
	 * checks whether they're implementations or just declarations. If
	 * implementation is present calls makeProcedureCFG() and appends CFG as
	 * child of procedure node to CFG
	 * @throws IOException 
	 */
	public boolean process(IElement root) throws IOException {
		if (!(root instanceof Unit)) {
			// TODO
			mLogger.debug("No WrapperNode. Let Ultimate process with next node");
			return true;
		} else {
			Unit unit = (Unit) root;
			RCFGBacktranslator translator = new RCFGBacktranslator();
			CfgBuilder recCFGBuilder = new CfgBuilder(unit, translator, mServices, mStorage);
			try {
				mGraphroot = recCFGBuilder.getRootNode(unit);
				ModelUtils.mergeAnnotations(unit, mGraphroot);
				mServices.getBacktranslationService().addTranslator(translator);
			} catch (SMTLIBException e) {
				if (e.getMessage().equals("Cannot create quantifier in quantifier-free logic")) {
					mLogger.warn("Unsupported syntax: " + e.getMessage());
				} else if (e.getMessage().equals("Sort Array not declared")) {
					mLogger.warn("Unsupported syntax: " + e.getMessage());
				} else if (e.getMessage().equals("Unsupported non-linear arithmetic")) {
					mLogger.warn("Unsupported syntax: " + e.getMessage());
				} else {
					throw e;
				}
			}
		}
		return false;
	}

	@Override
	public void finish() {
		// TODO Auto-generated method stub

	}

	@Override
	public WalkerOptions getWalkerOptions() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void init(GraphType modelType, int currentModelIndex, int numberOfModels) {
		// TODO Auto-generated method stub

	}

	@Override
	public boolean performedChanges() {
		// TODO Auto-generated method stub
		return false;
	}

}
