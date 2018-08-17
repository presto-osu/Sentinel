package presto.android.gui.clients;

import presto.android.Configs;
import presto.android.Debug;
import presto.android.Logger;
import presto.android.gui.GUIAnalysisClient;
import presto.android.gui.GUIAnalysisOutput;
import presto.android.gui.clients.energy.StatUtil;
import presto.android.gui.clients.energy.VarUtil;
import presto.android.gui.clients.sensor.SensorRegistrationAnalyzer;
import presto.android.gui.clients.sensor.SensorVarUtil;
import presto.android.gui.wtg.WTGAnalysisOutput;
import presto.android.gui.wtg.WTGBuilder;
import presto.android.gui.wtg.ds.WTG;
import presto.android.xml.DefaultXMLParser;
import presto.android.xml.XMLParser;

import java.util.Iterator;

/**
 * Created by zero on 2/14/17.
 */
public class SensorRegistrationAnalysisClient implements GUIAnalysisClient{



  public SensorRegistrationAnalysisClient(){

  }

  @Override
  public void run(GUIAnalysisOutput output) {
    // Firstly do WTGAnalysis
    // set start time if only CCFG analysis is counted
    DefaultXMLParser xml = (DefaultXMLParser) XMLParser.Factory.getXMLParser();
    if (xml.getAppPackageName().equals("com.mobeezio.android.dogwhistler")) {
      //This app requires handling of other async ops defined in wtg.xml
      Configs.asyncStrategy = Configs.AsyncOpStrategy.All_EventHandler_Async;
    }

    VarUtil.v().guiOutput = output;
    if (!Configs.trackWholeExec) {
      Logger.verb(getClass().getSimpleName(), "Pre-running time " + Debug.v().getExecutionTime());
      Debug.v().setStartTime();
    }
    SensorVarUtil.flowgraph = output.getFlowgraph();
    WTGBuilder wtgBuilder = new WTGBuilder();
    wtgBuilder.build(output);

    long execTime = Debug.v().getExecutionTime();
    WTGAnalysisOutput wtgAO = new WTGAnalysisOutput(output, wtgBuilder);

    WTG wtg = wtgAO.getWTG();

    Logger.verb(getClass().getSimpleName(), "Start Energy Analysis");
    hashDeclaredActivities();

    //Log the start time for the energy analysis.
    long startime = System.currentTimeMillis();

    SensorRegistrationAnalyzer sAnalyzer = new SensorRegistrationAnalyzer(wtg, output, wtgAO);
    sAnalyzer.startTime = System.currentTimeMillis();
    sAnalyzer.analyze();
    long stopTime = System.currentTimeMillis();
    float runningSecond = ((float)(stopTime - startime))/1000;
    Logger.verb("TimeCost", "Client running time is " + runningSecond);
  }

  private void hashDeclaredActivities() {
    DefaultXMLParser xml = (DefaultXMLParser) XMLParser.Factory.getXMLParser();
    for (Iterator<String> iter = xml.getActivities(); iter.hasNext();) {
      String activity = iter.next();
      SensorVarUtil.declaredActivities.add(activity);
    }
    SensorVarUtil.declaredActivities.addAll(xml.aliasActivityToOriginMap.keySet());
  }
}
