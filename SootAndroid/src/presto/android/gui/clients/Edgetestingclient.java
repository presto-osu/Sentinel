package presto.android.gui.clients;

import presto.android.Configs;
import presto.android.Debug;
import presto.android.Logger;
import presto.android.gui.GUIAnalysisClient;
import presto.android.gui.GUIAnalysisOutput;
import presto.android.gui.clients.energy.StatUtil;
import presto.android.gui.clients.energy.VarUtil;
import presto.android.gui.wtg.EventHandler;
import presto.android.gui.wtg.WTGAnalysisOutput;
import presto.android.gui.wtg.WTGBuilder;
import presto.android.gui.wtg.ds.WTG;
import presto.android.gui.wtg.ds.WTGEdge;

/**
 * Created by zero on 4/11/17.
 */
public class Edgetestingclient implements GUIAnalysisClient {
  @Override
  public void run(GUIAnalysisOutput output) {
    VarUtil.v().guiOutput = output;
    if (!Configs.trackWholeExec) {
      Logger.verb(getClass().getSimpleName(), "Pre-running time " + Debug.v().getExecutionTime());
      Debug.v().setStartTime();
    }
    WTGBuilder wtgBuilder = new WTGBuilder();
    wtgBuilder.build(output);

    long execTime = Debug.v().getExecutionTime();
    WTGAnalysisOutput wtgAO = new WTGAnalysisOutput(output, wtgBuilder);

    WTG wtg = wtgAO.getWTG();

    Logger.verb(getClass().getSimpleName(), "Start Energy Analysis");

    //Log the start time for the energy analysis.
    long startime = System.currentTimeMillis();
    //Output current Mem info
    long curUsedMem = StatUtil.v().getUsedMem();

    for (WTGEdge e : wtg.getEdges()) {
      for (EventHandler evt : e.getCallbacks()) {
        if (evt.getWindow() == null && evt.getWidget() == null) {
          Logger.verb("EVENT", "Both window and widget is null in callback of edge " + e.toString());
          Logger.verb("EVENT", "\twindow null, widget null callback ");
        } else if (evt.getWindow() != null && evt.getWidget() != null) {
          Logger.verb("EVENT", "Both window and widget is NOT null in callback of edge " + e.toString());
          Logger.verb("EVENT", "\twindow " + evt.getWindow() + " widget " + evt.getWidget());

        }
      }

      for (EventHandler evt : e.getWTGHandlers()) {
        if (evt.getWindow() == null && evt.getWidget() == null) {
          Logger.verb("EVENT", "Both window and widget is null in handler of edge " + e.toString());
        } else if (evt.getWindow() != null && evt.getWidget() != null) {
          Logger.verb("EVENT", "Both window and widget is NOT null in handler of edge " + e.toString());
        }
      }
    }
  }
}
