package de.uni_freiburg.informatik.ultimate.boogie.procedureinliner;

import java.util.ArrayList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.access.IObserver;
import de.uni_freiburg.informatik.ultimate.core.preferences.UltimatePreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.core.services.IToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.ep.interfaces.IAnalysis;
import de.uni_freiburg.informatik.ultimate.model.GraphType;

/**
 * 
 * @author schaetzc@informatik.uni-freiburg.de
 * 
 */
public class BoogieProcedureInliner implements IAnalysis {

	private IUltimateServiceProvider mServices;
	private Logger mLogger;
	
	@Override
	public GraphType getOutputDefinition() {
		return null;
	}

	@Override
	public boolean isGuiRequired() {
		return false;
	}

	@Override
	public QueryKeyword getQueryKeyword() {
		return QueryKeyword.LAST;
	}

	@Override
	public List<String> getDesiredToolID() {
		return null;
	}

	@Override
	public void setInputDefinition(GraphType graphType) {

	}

	@Override
	public List<IObserver> getObservers() {
		// TODO generate Observers (which transform the AST)
		ArrayList<IObserver> observers = new ArrayList<IObserver>();
		observers.add(new ProcedureInliner(mServices));
		return observers;
	}

	@Override
	public void setToolchainStorage(IToolchainStorage storage) {
		// #2
	}

	@Override
	public void setServices(IUltimateServiceProvider services) {
		// #1
		mServices = services;
		mLogger = services.getLoggingService().getLogger(Activator.PLUGIN_ID);
		// exceptions: services.getResultService().reportResult(getPluginID(),
		//               new GenericResult(getPluginID(), "", longDescription, severity));
	}

	@Override
	public void init() {
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
	public UltimatePreferenceInitializer getPreferences() {
		return null;
	}

	@Override
	public void finish() {
	}

}
