package presto.android.gui.clients.sensor;

import com.google.common.base.Preconditions;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import presto.android.Configs;
import presto.android.Hierarchy;
import presto.android.Logger;
import presto.android.MethodNames;
import presto.android.gui.FixpointSolver;
import presto.android.gui.GUIAnalysisOutput;
import presto.android.gui.JimpleUtil;
import presto.android.gui.clients.energy.*;
import presto.android.gui.clients.testgen.uiautomator.TestGen;
import presto.android.gui.graph.*;
import presto.android.gui.listener.EventType;
import presto.android.gui.wtg.EventHandler;
import presto.android.gui.wtg.StackOperation;
import presto.android.gui.wtg.WTGAnalysisOutput;
import presto.android.gui.wtg.ds.WTG;
import presto.android.gui.wtg.ds.WTGEdge;
import presto.android.gui.wtg.ds.WTGNode;
import presto.android.gui.wtg.util.Filter;
import presto.android.gui.wtg.util.QueryHelper;
import presto.android.gui.wtg.util.WTGUtil;
import presto.android.xml.XMLParser;
import soot.*;
import soot.jimple.Stmt;
import soot.toolkits.graph.UnitGraph;

import java.io.File;
import java.util.*;

/**
 * Created by zero on 2/14/17.
 */
public class SensorRegistrationAnalyzer {

  private List<WTGEdge> allEdges;
  private List<WTGNode> allNodes;
  Set<Pair<NObjectNode, SootMethod>> allPairs = Sets.newHashSet();
  HashMultimap<Pair<NObjectNode, SootMethod>, SensorResNode> pairACQMap = HashMultimap.create();
  HashMultimap<Pair<NObjectNode, SootMethod>, SensorResNode> pairRELMap = HashMultimap.create();
  HashMultimap<Pair<NObjectNode, SootMethod>, SensorResNode> pairRemovedMap = HashMultimap.create();
  Set<SensorResNode> allAvailableResNode = Sets.newHashSet();
  HashMultimap<SootMethod, SensorResNode> callbackResMap = HashMultimap.create();
  HashMultimap<SensorResNode, SensorResNode> resResMap = HashMultimap.create();
  HashMultimap<NNode, SensorResNode> listenerResMap = HashMultimap.create();
  private WTG wtg;
  private JimpleUtil jimpleUtil;
  private WTGUtil wtgUtil;

  public long startTime = 0;

  public long endTime = 0;
  private XMLParser xmlParser;

  private Map<Pair<NObjectNode, SootMethod>, NObjectNode> widgetPairToWindowMap = Maps.newHashMap();

  public SensorRegistrationAnalyzer(WTG wtg, GUIAnalysisOutput guiOutput, WTGAnalysisOutput
          wtgOutput) {
    SensorVarUtil.wtg = wtg;
    SensorVarUtil.guiOutput = guiOutput;
    SensorVarUtil.wtgOutput = wtgOutput;
    SensorVarUtil.analyzer = this;
    this.wtg = wtg;
    this.jimpleUtil = JimpleUtil.v();
    this.wtgUtil = WTGUtil.v();
    this.xmlParser = XMLParser.Factory.getXMLParser();

  }

  public void analyze() {
    // Make a copy of all WTG nodes and edges
    this.allEdges = Lists.newArrayList(SensorVarUtil.wtg.getEdges());
    this.allNodes = Lists.newArrayList(SensorVarUtil.wtg.getNodes());
    Logger.trace("WTG", "Node count: " + this.allNodes.size());
    Logger.trace("WTG", "Edge count: " + this.allEdges.size());

    for (WTGEdge curEdge : this.allEdges) {
      NObjectNode guiWidget = curEdge.getGUIWidget();

      //Get life cycle callbacks (e.g. onPause()) from current WTGEdge and generate pair for it
      List<EventHandler> curCallBacks = curEdge.getCallbacks();
      for (EventHandler ev : curCallBacks) {
        this.allPairs.add(new Pair<>(ev.getWindow(), ev.getEventHandler()));
      }

      //Get event handler (e.g. onClick()) from current WTGEdge and generate pair for it.
      Set<SootMethod> curHandlerSet = curEdge.getEventHandlers();
      for (SootMethod curMethod : curHandlerSet){
        Pair<NObjectNode, SootMethod> tempPair = new Pair<>(guiWidget, curMethod);
        if (!(guiWidget instanceof NOptionsMenuNode))
          widgetPairToWindowMap.put(tempPair, curEdge.getSourceNode().getWindow());
        this.allPairs.add(new Pair<>(guiWidget, curMethod));
      }
    }
    doAllPairsTraverse();
    doAllSensorListenerTraverse();

    Set<SensorResSet> knownSelfEdges = new HashSet<>();
    Set<EdgeSet> knownEdges = new HashSet<>();
    Set<WTGNode> knownNodes = Sets.newHashSet();
    for (WTGEdge curEdge: this.allEdges) {
      if (curEdge.getSourceNode().getWindow() instanceof NActivityNode) {
        String className = curEdge.getSourceNode().getWindow().getClassType().getName();
        if (!SensorVarUtil.declaredActivities.contains(className)) {
          //Undeclared activity
          Logger.trace("DECLARE", className + " Not declared");
          SensorVarUtil.duplicatedAndInfeasibleEdge.add(curEdge);
          continue;
        }
      }

      if (curEdge.getTargetNode().getWindow() instanceof NActivityNode) {
        String className = curEdge.getTargetNode().getWindow().getClassType().getName();
        if (!SensorVarUtil.declaredActivities.contains(className)) {
          //Undeclared activity
          Logger.trace("DECLARE", className + " Not declared");
          SensorVarUtil.duplicatedAndInfeasibleEdge.add(curEdge);
          continue;
        }
      }

      if (curEdge.getEventType() == EventType.implicit_on_activity_result) {
        SensorVarUtil.duplicatedAndInfeasibleEdge.add(curEdge);
        continue;
      }
      EdgeSet es = new EdgeSet(curEdge);
      if (knownEdges.contains(es)) {
        SensorVarUtil.duplicatedAndInfeasibleEdge.add(curEdge);
        Logger.trace("Duplicated", "edge " + curEdge + " added");
        for (EdgeSet testes : knownEdges) {
          if (testes.equals(es)) {
            Logger.trace("Duplicated", "Same edge " + testes.edge);
          }
        }
        continue;
      } else {
        knownEdges.add(es);
      }
      if (curEdge.getStackOps().isEmpty() &&
              curEdge.getSourceNode() == curEdge.getTargetNode() &&
              curEdge.getEventType() != EventType.implicit_home_event &&
              curEdge.getEventType() != EventType.implicit_power_event) {
        //A self edge appears
        Set<SensorResNode> acquiredNodes = new HashSet<>();
        Set<SensorResNode> releasedNodes = new HashSet<>();
        NObjectNode guiWidget = curEdge.getGUIWidget();
        List<EventHandler> curCallBacks = curEdge.getCallbacks();
        for (EventHandler ev : curCallBacks) {
          Pair<NObjectNode, SootMethod> testPair = new Pair<>(ev.getWindow(), ev.getEventHandler());
          if (pairACQMap.containsKey(testPair))
            acquiredNodes.addAll(pairACQMap.get(testPair));
          if (pairRELMap.containsKey(testPair))
            releasedNodes.addAll(pairRELMap.get(testPair));
        }

        Set<SootMethod> curHandlerSet = curEdge.getEventHandlers();
        for (SootMethod curMethod : curHandlerSet){
          Pair<NObjectNode, SootMethod> testPair = new Pair<>(guiWidget, curMethod);
          if (pairACQMap.containsKey(testPair))
            acquiredNodes.addAll(pairACQMap.get(testPair));
          if (pairRELMap.containsKey(testPair))
            releasedNodes.addAll(pairRELMap.get(testPair));
        }
        SensorResSet entry = new SensorResSet();
        entry.acquireSet.addAll(acquiredNodes);
        entry.releaseSet.addAll(releasedNodes);
        entry.node = curEdge.getSourceNode();
        if (knownSelfEdges.contains(entry)) {
          SensorVarUtil.duplicatedAndInfeasibleEdge.add(curEdge);
            Logger.trace("Duplicated", "edge " + curEdge + " added");
          continue;
        } else {
          knownSelfEdges.add(entry);
        }
      }
      int stepLabelCount = 0;
      boolean labled = false;
      if (!curEdge.getStackOps().isEmpty()) {
        VarUtil.v().labeledEdge.add(curEdge);
        stepLabelCount += curEdge.getStackOps().size();
      }
      if (curEdge.getEventType() == EventType.implicit_home_event) {
        VarUtil.v().labeledEdge.add(curEdge);
        stepLabelCount += 1;
      }
      NObjectNode guiWidget = curEdge.getGUIWidget();
      List<EventHandler> curCallBacks = curEdge.getCallbacks();
      for (EventHandler ev : curCallBacks) {
        Pair<NObjectNode, SootMethod> testPair = new Pair<>(ev.getWindow(), ev.getEventHandler());
        if ((!pairACQMap.get(testPair).isEmpty()) || (!pairRELMap.get(testPair).isEmpty())) {
          labled = true;
          //VarUtil.v().totalSGEdgeCount += 1;
          stepLabelCount += pairACQMap.get(testPair).size();
          stepLabelCount += pairRELMap.get(testPair).size();
          //break;
        }
      }
      if (labled) {
        VarUtil.v().labeledEdge.add(curEdge);
      }
      //Get event handler (e.g. onClick()) from current WTGEdge and generate pair for it.
      Set<SootMethod> curHandlerSet = curEdge.getEventHandlers();
      for (SootMethod curMethod : curHandlerSet){
        Pair<NObjectNode, SootMethod> testPair = new Pair<>(guiWidget, curMethod);
        if ((!pairACQMap.get(testPair).isEmpty()) || (!pairRELMap.get(testPair).isEmpty())) {
          labled = true;
          stepLabelCount += pairACQMap.get(testPair).size();
          stepLabelCount += pairRELMap.get(testPair).size();
          //break;
        }
      }
      if (labled) {
        VarUtil.v().labeledEdge.add(curEdge);
      }
      VarUtil.v().totalSGEdgeCount += stepLabelCount;
      VarUtil.v().totalSGNodeCount += stepLabelCount - 1;
      if (VarUtil.v().labeledEdge.contains(curEdge)) {
        knownNodes.add(curEdge.getSourceNode());
        knownNodes.add(curEdge.getTargetNode());
      }
    }
    VarUtil.v().totalSGNodeCount += knownNodes.size();
    Logger.trace("DEBUG", "Forbidden Edges: "
            + SensorVarUtil.duplicatedAndInfeasibleEdge.size());
    if (SensorVarUtil.duplicatedAndInfeasibleEdge.size() > 0) {
      for (WTGEdge e : SensorVarUtil.duplicatedAndInfeasibleEdge) {
        Logger.trace("Forbidden", e.toString());
      }
    }
    Logger.trace("DEBUG", "Forbidden Sets: " + knownSelfEdges.size());
    String Kval = Configs.getClientParamCode("WTPK");

    //If the K value does not exists, use 5 as default
    if (Kval == null) {
      Logger.verb("EnergyAnalyzer.Analyze",
              "K value for WTG Path is not specified, use 5 as default");
      SensorVarUtil.K = 5;
    }else {
      try {
        String val = Kval.substring(4);
        SensorVarUtil.K = Integer.decode(val);
      }catch (IndexOutOfBoundsException e){
        Logger.verb("EnergyAnalyzer.Analyze",
                "K value for WTG Path is not specified, use 5 as default");
        SensorVarUtil.K = 5;
      }
      catch (NumberFormatException e){
        Logger.verb("EnergyAnalyzer.Analyze",
                "K value for WTG Path is not specified, use 5 as default");
        SensorVarUtil.K = 5;
      }
    }
    Pattern1_2AnalysisG();
    printStats2();
  }

  private void printStats2() {
    String infoLine = "AppName & Classes & Jimples & Node & Edge && LP1 & LP2 &&" +
            "LRP1 & LRP2 && TestsL1 & TestsL2 && Time";
    endTime = System.currentTimeMillis();
    long diff = this.endTime - this.startTime;
    float runningSec = (float)diff / 1000;
    int classCount = Configs.classCount;
    long jimpleCount = Configs.jimpleCount;
    int pathCount = SensorVarUtil.P1CandidateCount + SensorVarUtil.P2CandidateCount;
    String curLIne = String.format("%s & %d & %d & %d &%d && %d & %d && %d & %d && %d & %d &&" +
                    " %f ",
            Configs.benchmarkName,
            classCount,
            jimpleCount,
            VarUtil.v().totalSGNodeCount,
            VarUtil.v().totalSGEdgeCount,
            SensorVarUtil.P1Mark2Measurement,
            SensorVarUtil.P2Mark2Measurement,
            SensorVarUtil.P1Mark3Measurement,
            SensorVarUtil.P2Mark3Measurement,
            SensorVarUtil.P1UniqueCount,
            SensorVarUtil.P2UniqueCount,
            runningSec
            );
    Logger.verb("STAT", infoLine);
    Logger.verb("STAT", curLIne);
  }

  private void printStats() {
    String mtdTag = "STAT";
    int nodes = this.allNodes.size();
    int edges = this.allEdges.size();

    endTime = System.currentTimeMillis();
    long passedTime = this.endTime - this.startTime;
    float runningSec = (float)passedTime/1000;

    Logger.verb(mtdTag, "K = " + SensorVarUtil.K);

    String InfoLine = "App & Nodes & Edges & Path &&C1 Unique &C2 Unique && Time";
    String curLine =  String.format(
            "%s &%d &%d &%d &&%d &%d &&%f",
            Configs.benchmarkName,
            nodes,
            edges,
            SensorVarUtil.P1CandidateCount + SensorVarUtil.P2CandidateCount,
            SensorVarUtil.P1UniqueCount,
            SensorVarUtil.P2UniqueCount,
            runningSec);
    Logger.verb(mtdTag, InfoLine);
    Logger.verb(mtdTag, curLine);


  }

  private void doAllSensorListenerTraverse() {
    Set<SensorResNode> m_sessionACQ = Sets.newHashSet();
    Set<SensorResNode> m_sessionREL = Sets.newHashSet();
    for (SensorResNode curNode: Sets.newHashSet(this.allAvailableResNode)) {
      SootMethod callbk = extractListenerCallbackFromRes(curNode);
      if (callbk != null) {
        //Logger.verb("SensorResNode", "Callback mtd " + callbk.getSignature());
        m_sessionACQ.clear();
        m_sessionREL.clear();
        traverseMethodFull(callbk, m_sessionACQ, m_sessionREL, HashMultimap.<Stmt, Stmt>create(),
                HashMultimap.<Stmt, SootMethod>create());
        if (!m_sessionACQ.isEmpty()) {
          Logger.trace("SensorListener" , "Sensor Callback tried to acquire resource " + callbk
                  .getSignature());

        }
        for (SensorResNode relNode : m_sessionREL) {

          boolean reached = traverseMethod(callbk, relNode, HashMultimap.<Stmt, Stmt>create(),
                  HashMultimap.<Stmt, SootMethod>create());
          if (!reached) {
            resResMap.put(curNode, relNode);
            callbackResMap.put(callbk, relNode);
            listenerResMap.put(curNode.listenerNode, relNode);
          }
        }
      }
    }
  }

  private SootMethod extractListenerCallbackFromRes(SensorResNode node) {
    if (node.listenerNode instanceof NObjectNode) {
      NObjectNode listenerNode = (NObjectNode) node.listenerNode;
      SootClass listenerClass = listenerNode.getClassType();
      Logger.trace("ESensorResNode", "Class Name " + listenerClass.getName());
      if (listenerClass.declaresMethod("void onSensorChanged(android.hardware.SensorEvent)")) {
        return listenerClass.getMethod("void onSensorChanged(android.hardware.SensorEvent)");
      } else {
        for (SootMethod mtd : listenerClass.getMethods()) {
          if (mtd.getSignature().contains("onSensorChanged")) {
            Logger.trace("ESensorResNode", "MethodName " + mtd.getSubSignature());
          }
        }
      }
    }
    return null;
  }

  //Pattern 1 and 2 Analysis using generic DFS Path Generator
  private void Pattern1_2AnalysisG(){
    final String mtdTag = "SensorRegistrationAnalyzer.Pattern1_2AnalysisG";
    //Map used to save Pattern 1 Paths with energy defects.
    final Map<List<WTGEdge>, List<SensorResNode>> p1PathResMap = Maps.newHashMap();
    //Map used to save Pattern 2 Paths with energy defects.
    final Map<List<WTGEdge>, List<SensorResNode>> p2PathResMap = Maps.newHashMap();
    IPathFilter pattern1Filter = new IPathFilter() {
      @Override
      public boolean match(List<WTGEdge> P, Stack<NObjectNode> S) {

        if (P.size() < 2)
          return false;
        NObjectNode targetWindow = P.get(0).getTargetNode().getWindow();
        WTGEdge lastEdge = P.get(P.size() - 1);
        List<StackOperation> lastOpS = lastEdge.getStackOps();
        WTGNode sourceNode = P.get(0).getSourceNode();
        WTGNode finalTargetNode = P.get(P.size()-1).getTargetNode();
//        if (sourceNode != finalTargetNode)
//          return false;

        //Last edge should not be home/power/rotate
        EventType lastEvent = lastEdge.getEventType();
        if (lastEvent == EventType.implicit_rotate_event
                || lastEvent == EventType.implicit_home_event
                || lastEvent == EventType.implicit_power_event)
          return false;

        //Check if last edge have pop(w)
        boolean fPop = false;
        for (StackOperation curOp : lastOpS) {
          if (!curOp.isPushOp() && curOp.getWindow() == targetWindow)
            fPop = true;
        }
        if (!fPop)
          return false;

        //Make a copy of the stack
        Stack<NObjectNode> cpS = new Stack<NObjectNode>();
        cpS.addAll(S);
        //Undo last edges operation
        for (int i = lastOpS.size() - 1; i >= 0; i--) {
          StackOperation curOp = lastOpS.get(i);
          NObjectNode opWindow = curOp.getWindow();
          if (opWindow == targetWindow && (!curOp.isPushOp()) && cpS.isEmpty()) {
            //Stack is balanced(Empty). Currently it is a pop operation and op Window is the target Window
            if (sourceNode == finalTargetNode) {
              SensorVarUtil.P1CandidateCount++;
              List<SensorResNode> rmRes = SensorRegistrationAnalyzer.this.traverseCategory1Path(P);
              if (!rmRes.isEmpty()) {
                p1PathResMap.put(Lists.<WTGEdge>newArrayList(P), rmRes);
                SensorVarUtil.P1Mark3Measurement++;
              }
            }
            SensorVarUtil.P1Mark2Measurement++;
            return true;
          }
          //Undo the changes
          if (!curOp.isPushOp()) {
            //It is a pop
            cpS.push(opWindow);
          } else if (!cpS.isEmpty() && cpS.peek() == opWindow) {
            //It is a push and window match the top of the window stack
            cpS.pop();
          } else {
            Logger.err("DFSPATH", "ERROR: Stack is not balanced in isP1Candidate");
          }
        }
        return false;
      }
      @Override
      public String getFilterName() {
        return "Pattern1";
      }
    };

    IPathFilter pattern2Filter = new IPathFilter() {
      @Override
      public boolean match(List<WTGEdge> P, Stack<NObjectNode> S) {
        if (P.size() < 2) {
          return false;
        }
//        if (P.size() > 3) {
//          return false;
//        }
        NObjectNode targetWindow = P.get(0).getTargetNode().getWindow();
        NObjectNode topActivity = getTopActivity(S);
        if (topActivity == null)
          //If the stack is empty or no activity inside return false
          return false;
        WTGEdge lastEdge = P.get(P.size() - 1);
        EventType evt = lastEdge.getEventType();
        if (topActivity == targetWindow &&
           (evt == EventType.implicit_home_event)) {
          SensorVarUtil.P2CandidateCount++;
          SensorVarUtil.P2Mark2Measurement++;
          List<SensorResNode> rmRes = SensorRegistrationAnalyzer.this.traverseCategory2Path(P);
          if (!rmRes.isEmpty()) {
            p2PathResMap.put(Lists.<WTGEdge>newArrayList(P), rmRes);
            SensorVarUtil.P2Mark3Measurement++;
          }
          return true;
        }
        return false;
      }

      @Override
      public String getFilterName() {
        return "Patter2";
      }
    };

    //Gen Inital Edges
    List<WTGEdge> initEdges = Lists.newArrayList();
    for (WTGNode n : wtg.getNodes()){
      if(!(n.getWindow() instanceof NActivityNode)){
        //Ignore any window that is not Activity
        continue;
      }
      List<WTGEdge> validInboundEdges = Lists.newArrayList();
      for (WTGEdge curEdge : n.getInEdges()){
        switch (curEdge.getEventType()) {
          case implicit_back_event:
          case implicit_home_event:
          case implicit_rotate_event:
          case implicit_power_event:
//          case implicit_on_activity_result:
            continue;
        }
        List<StackOperation> curStack = curEdge.getStackOps();
        if (curStack != null && !curStack.isEmpty()) {
          StackOperation curOp = curStack.get(curStack.size() - 1);
          //If last op of this inbound edge is push
          if (curOp.isPushOp()) {
            NObjectNode pushedWindow = curOp.getWindow();
            WTGNode pushedNode = wtg.getNode(pushedWindow);
            if (pushedNode == n) {
              validInboundEdges.add(curEdge);
            }
          }
        }
      }
      if (validInboundEdges.isEmpty()){
        //No inBound edges. Fake them
        WTGEdge fakeInEdge = FakeNodeEdgeGenerator.v().genFakeType1Path(n);
        validInboundEdges.add(fakeInEdge);
      }

      for (WTGEdge e : validInboundEdges) {
        initEdges.add(e);
      }
    }

    IEdgeFilter edgeFilter = new IEdgeFilter() {
      @Override
      public boolean discard(WTGEdge e, List<WTGEdge> P, Stack<NObjectNode> S) {

        if (SensorVarUtil.duplicatedAndInfeasibleEdge.contains(e))
          return true;
        if (!VarUtil.v().labeledEdge.contains(e))
          return true;
        return false;
      }
    };


    List<IPathFilter> pathFilters = Lists.newArrayList();
    pathFilters.add(pattern1Filter);
    pathFilters.add(pattern2Filter);
    List<IEdgeFilter> edgeFilters = Lists.newArrayList();
    edgeFilters.add(edgeFilter);
    DFSGenericPathGenerator pathGen = DFSGenericPathGenerator.create(
            pathFilters, edgeFilters,initEdges,SensorVarUtil.K);
    pathGen.doPathGenerationWithTarget();

    Logger.trace("RES", "P1 RES Map size: " + p1PathResMap.size());
    Logger.trace("RES", "P2 RES Map size: " + p2PathResMap.size());
    if (p1PathResMap.size() != 0) {
      Logger.trace("SENSOR", "bazinga");
    }
    if (p2PathResMap.size() != 0) {
      Logger.trace("SENSOR", "bazinga2");
    }
    List<List<WTGEdge>> pathsForTestCases = Lists.newArrayList();
    if (!p1PathResMap.isEmpty()) {
      SensorOutputReducer reducerC1 = new SensorOutputReducer(SensorOutputReducer.PathType.C1);
      reducerC1.parseOutput(p1PathResMap);
      int uniqueIssues = reducerC1.getUniqueIssues();
      SensorVarUtil.P1UniqueCount = uniqueIssues;
      Logger.trace("SENSOR", "unique issues " + uniqueIssues);
      File newDir = new File("sensorEnergyOutput");
      if (!newDir.exists()) {
        newDir.mkdir();
      }
      reducerC1.outputToFileMerge(newDir.getAbsolutePath() + "/" + Configs.benchmarkName + "C1.log",
              SensorOutputReducer.OutputType.MINIMAL);
      if (Configs.clientParams.contains("testGen")) {
//        for (Set<NObjectNode> widgetNodeSet : reducerC1.mData.keySet()) {
//          for (SensorOutputReducer.Path path : reducerC1.mData.get(widgetNodeSet)) {
//            pathsForTestCases.add(path.minPath);
//          }
//        }
        for (Set<SensorOutputReducer.Tupple<NNode, NNode, SootMethod>> resSet :
                reducerC1.tupplesCollection.keySet()) {
          for (List<WTGEdge> path : reducerC1.tupplesCollection.get(resSet)) {
            pathsForTestCases.add(path);
          }
        }
      }
      Logger.verb("\033[1;31mDEBUG\033[0m", "Pattern 1 defects output to " + reducerC1.absPath);
    }

    if (!p2PathResMap.isEmpty()) {
      SensorOutputReducer reducerC2 = new SensorOutputReducer(SensorOutputReducer.PathType.C2);
      reducerC2.parseOutput(p2PathResMap);
      int uniqueIssues = reducerC2.getUniqueIssues();
      SensorVarUtil.P2UniqueCount = uniqueIssues;
      Logger.trace("SENSOR", "unique issues " + uniqueIssues);
      File newDir = new File("sensorEnergyOutput");
      if (!newDir.exists()) {
        newDir.mkdir();
      }
      reducerC2.outputToFileMerge(newDir.getAbsolutePath() + "/" + Configs.benchmarkName + "C2.log",
              SensorOutputReducer.OutputType.MINIMAL);
      if (Configs.clientParams.contains("testGen")) {
//        for (Set<NObjectNode> widgetNodeSet : reducerC2.mData.keySet()) {
//          for (SensorOutputReducer.Path path : reducerC2.mData.get(widgetNodeSet)) {
//            pathsForTestCases.add(path.minPath);
//          }
//        }
        for (Set<SensorOutputReducer.Tupple<NNode, NNode, SootMethod>> resSet :
                reducerC2.tupplesCollection.keySet()) {
          for (List<WTGEdge> path : reducerC2.tupplesCollection.get(resSet)) {
            pathsForTestCases.add(path);
          }
        }
      }

      Logger.verb("\033[1;31mDEBUG\033[0m",
              "Pattern 2 defects output to " + reducerC2.absPath);
    }
    if (!pathsForTestCases.isEmpty()) {
      File newDir = new File("sensorEnergyOutput");
      if (!newDir.exists()) {
        newDir.mkdir();
      }

      TestGen tg = new TestGen(newDir.getAbsolutePath() +
              "/" + Configs.benchmarkName  + "Tests.py",
              Configs.sootAndroidRoot + "/testcases/gatorTestGenBase.py",
              xmlParser);
      for (List<WTGEdge> path : pathsForTestCases) {
        tg.feedPath(path);
      }
      tg.outputToFile();
    } else {
      Logger.verb("TESTCASE", "pathsForTestCases is empty");
    }
  }

  /**
   * Find if the method is relevant with the given node.
   * e.g. a WTGEdge may contains an onPause() callback from another method
   * @param mtd input method
   * @param node input WTGNode
   * @return  return true if these two input within same window. otherwise return false
   */
  private boolean isMethodRelevant(SootMethod mtd, WTGNode node){
    NObjectNode window = node.getWindow();
    SootClass tcls = window.getClassType();
    SootClass mcls = mtd.getDeclaringClass();
    if (mcls == tcls){
      return true;
    }else {
      while (tcls.hasSuperclass()){
        tcls = tcls.getSuperclass();
        if (tcls == mcls){
          return true;
        }
      }
    }
    return false;
  }

  private NObjectNode getTopActivity(Stack<NObjectNode> windowStack){
    if (windowStack.isEmpty())
      return null;
    if (!(windowStack.peek() instanceof NActivityNode)) {
      return null;
    }
    for (int i = windowStack.size() - 1; i >= 0; i--){
      NObjectNode curObj = windowStack.get(i);
      if (curObj instanceof NActivityNode)
        return curObj;
    }

    return null;
  }

  /**
   * Remove a resource from resource map if REL match an entry in ACQ
   * @param rmACQ remained aquired resource map.
   * @param curNode resource which is REL
   * @return  return true if it matches, otherwise return false.
   */
  private boolean matchAndRemoveRes(HashMultimap<NNode, SensorResNode> rmACQ, SensorResNode
          curNode){

    Preconditions.checkNotNull(rmACQ);
    boolean bWarning = false;
    if (rmACQ.containsKey(curNode.listenerNode)){
      Set<SensorResNode> resNodeSet = Sets.newHashSet(rmACQ.get(curNode.listenerNode));
      for (SensorResNode curResNode : resNodeSet){
        if (curNode.sensorNode == null) {
          //Remove all sensor under a listener
          if (curNode.listenerNode.equals(curResNode.listenerNode)) {
            rmACQ.remove(curResNode.listenerNode, curResNode);
          } else {
            Logger.trace("matchAndRemoval", "Listener node not equal");
          }
        } else {
          //Match 2
          if (curNode.listenerNode.equals(curResNode.listenerNode) && curNode.sensorNode.equals
                  (curResNode.sensorNode)) {
            rmACQ.remove(curResNode.listenerNode, curResNode);
          } else {
            Logger.trace("matchAndRemoval", "Listener and sensor node not equal");
          }
        }
      }

      return true;
    } else if (bWarning){
      Logger.verb("MATCH", "Target: " + curNode.listenerNode + " not matched");
    }

    return false;
  }

  private void addResNodeToMap(HashMultimap<NNode, SensorResNode> m_ACQMAP, Set<SensorResNode>
          m_sessionACQL){
    if (!m_sessionACQL.isEmpty()){
      //Logger.verb("ADDRES", "m_sessionACQL not empty");
      for (SensorResNode curACQ : m_sessionACQL){
        //Add this ACQ into m_ACQMAP if no duplicate exist
        //Different callbacks/handlers may call the same method which contains ACQ or REL. Therefore, duplicated
        //ResNode will be created in for these callbacks/handlers even though they are same resource
        //This is a workaround to prevent adding these duplicated ResNode to the Map.
        if (!m_ACQMAP.containsKey(curACQ.listenerNode)) {
          //No entry. Absolutely no duplication. Add this ResNode to Map.
          m_ACQMAP.put(curACQ.listenerNode, curACQ);
        } else{
          Set<SensorResNode> curResSet = m_ACQMAP.get(curACQ.listenerNode);
          boolean bSame = false;
          for (SensorResNode curRes : curResSet) {
            if (curRes.sensorNode.equals(curACQ.sensorNode) &&
                curRes.stmt.equals(curACQ.stmt) &&
                curRes.context.equals(curACQ.context)){
              //objectNode and Stmt and the method contains this Stmt is the same. Duplication detected
              bSame = true;
              break;
            }
          }
          if (!bSame) {
            //Add this ACQ into m_ACQMAP if no duplicate exist
            m_ACQMAP.put(curACQ.listenerNode, curACQ);
          }
        }
      }
    }
  }

  /**
   * Traverse on Category 1 Path using the description in the Paper Section 2.3
   * @param curPath The Category 1 path needs to be traversed
   * @return If this path contains a leak. return leaking resources. Otherwise return an empty list
   */
  public List<SensorResNode> traverseCategory1Path(List<WTGEdge> curPath){
    Stack<NObjectNode> windowStack = new Stack<NObjectNode>();
    NObjectNode targetNode = curPath.get(0).getTargetNode().getWindow();
    WTGNode targetWTGNode = curPath.get(0).getTargetNode();
    List<SensorResNode> retList = Lists.newArrayList();

    //Map<ListenerNode, SensorResNode>
    HashMultimap<NNode, SensorResNode> rmACQMap = HashMultimap.create();

    Set<SensorResNode> m_sessionACQ;
    Set<SensorResNode> m_sessionREL;
    if (!(targetNode instanceof NActivityNode)){
      //If target Window is not an activity
      //Do noting on it
      return retList;
    }


    //Assume the src node is already in the stack
    windowStack.push(curPath.get(0).getSourceNode().getWindow());
    for (int i = 0; i < curPath.size(); i++){
      WTGEdge curEdge = curPath.get(i);
      List<StackOperation> ops = curEdge.getStackOps();
      for (StackOperation op :ops){
        NObjectNode opWindow = op.getWindow();
        if (op.isPushOp()){
          windowStack.push(opWindow);
        }else if (!windowStack.isEmpty()){
          windowStack.pop();
        }else{
          return retList;
        }
      }

      NObjectNode widget = curEdge.getGUIWidget();
      for (SootMethod curHandler : curEdge.getEventHandlers()){
        if (i == 0 || i == curPath.size() - 1){
          if (!isMethodRelevant(curHandler, targetWTGNode))
            continue;
        }

        Pair<NObjectNode, SootMethod> curPair = new Pair<NObjectNode, SootMethod>(widget, curHandler);
        m_sessionACQ = pairACQMap.get(curPair);
        m_sessionREL = pairRELMap.get(curPair);
        NObjectNode curTopWindow = getTopActivity(windowStack);

        if (!m_sessionREL.isEmpty()){
          for (SensorResNode curREL :m_sessionREL){
            matchAndRemoveRes(rmACQMap, curREL);
          }
        }

        if (curTopWindow == targetNode){
          addResNodeToMap(rmACQMap, m_sessionACQ);
        }

      }

      //Then do on Callbacks
      if (i == curPath.size() - 1){
        //Last edge
        //Check in onPause/onStop/onDestroy
        for (EventHandler evt : curEdge.getCallbacks()){
          SootMethod curMethod = evt.getEventHandler();
          String curSub = curMethod.getSubSignature();
          if (!(curSub.contains("onPause") ||
                curSub.contains("onStop") ||
                curSub.contains("onDestroy")))
            continue;
          Pair<NObjectNode, SootMethod> curPair = new Pair<NObjectNode, SootMethod>(evt.getWindow(), evt
                  .getEventHandler());
          m_sessionACQ = pairACQMap.get(curPair);
          m_sessionREL = pairRELMap.get(curPair);
          NObjectNode curTopWindow = getTopActivity(windowStack);
          if (!m_sessionREL.isEmpty()){
            for (SensorResNode curREL : m_sessionREL){
              matchAndRemoveRes(rmACQMap, curREL);
            }
          }
          if (curTopWindow == targetNode){
            addResNodeToMap(rmACQMap, m_sessionACQ);
          }
        }
        continue;
      }

      for (EventHandler evt : curEdge.getCallbacks()){
        if (i == 0 || i == curPath.size() - 1){
          if (!isMethodRelevant(evt.getEventHandler(), targetWTGNode))
            continue;
        }
        Pair<NObjectNode, SootMethod> curPair = new Pair<NObjectNode, SootMethod>(evt.getWindow(), evt
                .getEventHandler());
        m_sessionACQ = pairACQMap.get(curPair);
        m_sessionREL = pairRELMap.get(curPair);
        NObjectNode curTopWindow = getTopActivity(windowStack);
        if (!m_sessionREL.isEmpty()){
          for (SensorResNode curREL : m_sessionREL){
            matchAndRemoveRes(rmACQMap, curREL);
          }
        }
        if (curTopWindow == targetNode){
          addResNodeToMap(rmACQMap, m_sessionACQ);
        }
      }
    }
    if (!rmACQMap.isEmpty()){
      //Set<SensorResNode> rm_RESSet = rmACQMap
      for (NNode curObj : Sets.newHashSet(rmACQMap.keySet())){
        if (listenerResMap.containsKey(curObj)) {
          Set<SensorResNode> removalNodes = listenerResMap.get(curObj);
          for (SensorResNode curREL : removalNodes) {
            matchAndRemoveRes(rmACQMap, curREL);
          }
        }
        Set<SensorResNode> curRESSet = rmACQMap.get(curObj);
        retList.addAll(curRESSet);
      }
    }
    return retList;
  }

  public List<SensorResNode> traverseCategory2Path(List<WTGEdge> curPath){
    Stack<NObjectNode> windowStack = new Stack<NObjectNode>();
    NObjectNode targetNode = curPath.get(0).getTargetNode().getWindow();
    WTGNode targetWTGNode = curPath.get(0).getTargetNode();
    List<SensorResNode> retList = Lists.newArrayList();
    //listenerNode -> SensorResNode
    HashMultimap<NNode, SensorResNode> rmACQMap = HashMultimap.create();
    Set<SensorResNode> m_sessionACQ;
    Set<SensorResNode> m_sessionREL;
    if (!(targetNode instanceof NActivityNode)){
      //If target Window is not an activity
      //Do noting on it
      return retList;
    }

    //Assume the src node is already in the stack
    windowStack.push(curPath.get(0).getSourceNode().getWindow());
    for (int i = 0; i < curPath.size(); i++){
      WTGEdge curEdge = curPath.get(i);
      List<StackOperation> ops = curEdge.getStackOps();
      for (StackOperation op :ops){
        NObjectNode opWindow = op.getWindow();
        if (op.isPushOp()){
          windowStack.push(opWindow);
        }else if (!windowStack.isEmpty()){
          windowStack.pop();
        }else{
          return retList;
        }
      }

      NObjectNode widget = curEdge.getGUIWidget();
      for (SootMethod curHandler : curEdge.getEventHandlers()){
        if (i == 0 || i == curPath.size() - 1){
          if (!isMethodRelevant(curHandler, targetWTGNode))
            continue;
        }

        Pair<NObjectNode, SootMethod> curPair = new Pair<NObjectNode, SootMethod>(widget, curHandler);
        m_sessionACQ = pairACQMap.get(curPair);
        m_sessionREL = pairRELMap.get(curPair);
        NObjectNode curTopWindow = getTopActivity(windowStack);
        if (!m_sessionREL.isEmpty()){
          for (SensorResNode curREL :m_sessionREL){
            matchAndRemoveRes(rmACQMap, curREL);
          }
        }
        if (curTopWindow == targetNode){
          addResNodeToMap(rmACQMap, m_sessionACQ);
        }
      }

      //Then do on Callbacks
      for (EventHandler evt : curEdge.getCallbacks()){
        if (i == 0 ){
          if (!isMethodRelevant(evt.getEventHandler(), targetWTGNode))
            continue;
        }

        if (i == curPath.size() - 1){
          SootMethod curMethod = evt.getEventHandler();
          if (!isMethodRelevant(evt.getEventHandler(), targetWTGNode))
            continue;
          String curSub = curMethod.getSubSignature();
          if (curSub.contains("onResume") ||
              curSub.contains("onStart") ||
              curSub.contains("onRestart"))
            continue;
        }

        Pair<NObjectNode, SootMethod> curPair = new Pair<NObjectNode, SootMethod>(evt.getWindow(), evt
                .getEventHandler());
        m_sessionACQ = pairACQMap.get(curPair);
        m_sessionREL = pairRELMap.get(curPair);
        NObjectNode curTopWindow = getTopActivity(windowStack);
        if (!m_sessionREL.isEmpty()){
          for (SensorResNode curREL : m_sessionREL){
            matchAndRemoveRes(rmACQMap, curREL);
          }
        }
        if (curTopWindow == targetNode){
          addResNodeToMap(rmACQMap, m_sessionACQ);
        }
      }
    }
//    if (!rmACQMap.isEmpty()){
//      for (NNode curObj : rmACQMap.keySet()){
//        Set<SensorResNode> curRESSet = rmACQMap.get(curObj);
//        retList.addAll(curRESSet);
//      }
//    }
    if (!rmACQMap.isEmpty()){
      //Set<SensorResNode> rm_RESSet = rmACQMap
      for (NNode curObj : Sets.newHashSet(rmACQMap.keySet())){
        if (listenerResMap.containsKey(curObj)) {
          Set<SensorResNode> removalNodes = listenerResMap.get(curObj);
          for (SensorResNode curREL : removalNodes) {
            matchAndRemoveRes(rmACQMap, curREL);
            Logger.trace("ListenerRemoval" , curREL.toString());
          }
        }
        Set<SensorResNode> curRESSet = rmACQMap.get(curObj);
        retList.addAll(curRESSet);
      }
    }

    return retList;
  }

  /**
   * Get infeasible Edges for the target pair. If not exists, do the anaysis and generate it
   * @param curPair Target pair
   * @return  infeasible edges
   */
  private HashMultimap<Stmt, Stmt> getInfeasibleEdges(Pair<NObjectNode, SootMethod> curPair){
    HashMultimap<Stmt, Stmt> ret;
    boolean bRecreate = false;
    if (VarUtil.v().infeasibleEdgesMap.containsKey(curPair)){
      ret = VarUtil.v().infeasibleEdgesMap.get(curPair);
    }else{
      bRecreate = true;
      ret = HashMultimap.create();
      HashMultimap<Stmt, SootMethod> infeasibleCalls = HashMultimap.create();
      SensorVarUtil.constantAnalysis.doAnalysis(curPair.getL(), curPair.getR(), ret, infeasibleCalls);
    }
    return ret;
  }

  public HashMultimap<Stmt, Stmt> reverseInfeasibleEdges(HashMultimap<Stmt, Stmt> infeasibleEdges){
    HashMultimap<Stmt, Stmt> retMap = HashMultimap.create();
    for (Stmt pred: infeasibleEdges.keySet()){
      Set<Stmt> tarSet = infeasibleEdges.get(pred);
      for (Stmt target : tarSet){
        retMap.put(target, pred);
      }
    }
    return retMap;
  }

  /**
   * Get infeasible Calls for the target pair. If not exists, do the anaysis and generate it
   * @param curPair Target pair
   * @return  infeasible calls
   */
  private HashMultimap<Stmt, SootMethod> getInfeasibleCalls(Pair<NObjectNode, SootMethod> curPair){
    HashMultimap<Stmt, SootMethod> ret;
    boolean bRecreate = false;
    if (VarUtil.v().infeasibleCallsMap.containsKey(curPair)){
      ret = VarUtil.v().infeasibleCallsMap.get(curPair);
    }else{
      bRecreate = true;
      ret = HashMultimap.create();
      HashMultimap<Stmt, Stmt> infeasibleEdges = HashMultimap.create();
      SensorVarUtil.constantAnalysis.doAnalysis(curPair.getL(), curPair.getR(), infeasibleEdges, ret);
    }
    return ret;
  }

  public boolean reverseICFGTraversal(
          SensorResNode curACQ,
          SensorResNode curREL,
          Pair<NObjectNode, SootMethod> curPair,
          HashMultimap<Stmt, Stmt> curInfeasibleEdges,
          HashMultimap<Stmt, SootMethod> curInfeasibleCalls) {

    Map<Stmt, SootMethod> visitedStmts = Maps.newHashMap();
    List<Stmt> visitedSeq = Lists.newArrayList();
    Set<Stmt> escapedStmts = Sets.newHashSet();
    Map<SootMethod, UnitGraph> methodToCFG = Maps.newHashMap();

    if (curInfeasibleEdges == null) {
      curInfeasibleEdges = HashMultimap.create();
    }
    reverseInfeasibleEdges(curInfeasibleEdges);
    if (curInfeasibleCalls == null) {
      curInfeasibleCalls = HashMultimap.create();
    }

    Filter<Stmt, SootMethod> F = new Filter<Stmt, SootMethod>() {
      public boolean match(Stmt unit, SootMethod sm) {
      if (wtgUtil.isReleaseResourceCall(unit)) {
        //REL encountered
        if (SensorVarUtil.stmtResNodeMap.containsKey(unit)) {
          Set<SensorResNode> curRelSet = SensorVarUtil.stmtResNodeMap.get(unit);
          for (SensorResNode curRelSetItem : curRelSet){
            if (curRelSetItem.listenerNode == curREL.listenerNode
                    && curRelSetItem.sensorNode == curREL.sensorNode) {
              return true;
            }
          }
        }
      }
      return false;
      }
    };

    ExperimentalContextSensitiveTraversal.getInstance().reverseTraversal(
            curPair.getR(),
            visitedStmts,
            visitedSeq,
            escapedStmts,
            methodToCFG,
            F,
            curInfeasibleEdges,
            curInfeasibleCalls
    );

    if (visitedStmts.containsKey(curACQ.stmt)) {
      return true;
    } else {
      return false;
    }

  }

  private NObjectNode retrieveParentActivity(NObjectNode node) {
    if (node instanceof NActivityNode || node instanceof NDialogNode) {
      return node;
    }
    if (node instanceof NOptionsMenuNode) {
      SootClass parentActivity = ((NOptionsMenuNode)node).ownerActivity;
      return SensorVarUtil.flowgraph.allNActivityNodes.get(parentActivity);
    }
    return node;
  }

  private void doAllPairsTraverse(){


    final String mtdTag = "ALLMTDTR";   //Log tag

    //All method get, Do phase 1. Get All ACQ and REL
    //Following Sets use to save found ACQ and RELs from a single Pair.
    Set<SensorResNode> p_SessionACQ = Sets.newHashSet();
    Set<SensorResNode> p_SessionREL = Sets.newHashSet();
    List<SensorResNode> resNodeList = Lists.newArrayList();
    SensorVarUtil.stmtResNodeMap = HashMultimap.create();

    for (Pair<NObjectNode, SootMethod> curPair: allPairs) {
      //For each pair of GUIWidget, handler/ lifecycle callback pair. Find ACQ and REL.
      p_SessionACQ.clear();
      p_SessionREL.clear();
      SootMethod curMethod = curPair.getR();
      //Get infeasibleEdges and infeasibleCalls of target method
      HashMultimap<Stmt, Stmt> curInfeasibleEdges = getInfeasibleEdges(curPair);
      HashMultimap<Stmt, SootMethod> curInfeasibleCalls = getInfeasibleCalls(curPair);

      //Traverse on method. Return True if any ACQ or REL is found.
      boolean bRes = traverseMethodFull(
              curMethod,
              p_SessionACQ,
              p_SessionREL,
              curInfeasibleEdges,
              curInfeasibleCalls);

      if (bRes) {
        for (SensorResNode curRes : p_SessionACQ) {
          curRes.guiWidget = curPair.getL();
          if (!(curRes.guiWidget instanceof NWindowNode)) {
            curRes.guiWidget = widgetPairToWindowMap.get(curPair);
          }
          curRes.guiWidget = retrieveParentActivity(curRes.guiWidget);
          pairACQMap.put(curPair, curRes);
          Logger.trace("PAIRACQ", "Pair: " + curPair + " ACQ " + curRes.toString());
          SensorVarUtil.stmtResNodeMap.put(curRes.stmt, curRes);
          resNodeList.add(curRes);
        }

        for (SensorResNode curRes : p_SessionREL) {
          curRes.guiWidget = curPair.getL();
          if (!(curRes.guiWidget instanceof NWindowNode)) {
            curRes.guiWidget = widgetPairToWindowMap.get(curPair);
          }
          curRes.guiWidget = retrieveParentActivity(curRes.guiWidget);
          pairRELMap.put(curPair, curRes);
          SensorVarUtil.stmtResNodeMap.put(curRes.stmt, curRes);
        }
      }
    }// End of for.

    //It might be unnecessary. So comment it out for now.
    //Phase 1 ended. Do Phase 2 part 1. traverse reversed ICFG of each ACQ that have the same REL
    for (Pair<NObjectNode, SootMethod> curPair: Sets.newHashSet(pairACQMap.keySet())){
      if (!pairRELMap.containsKey(curPair))
        continue;
      HashMultimap<Stmt, Stmt> curInfeasibleEdges = getInfeasibleEdges(curPair);
      HashMultimap<Stmt, SootMethod> curInfeasibleCalls = getInfeasibleCalls(curPair);
      //curPair contians both ACQ and REL
      Set<SensorResNode> acqResSet = Sets.newHashSet(pairACQMap.get(curPair));
      Set<SensorResNode> relResSet = Sets.newHashSet(pairRELMap.get(curPair));

      boolean containBothACQREL = false;
      for (SensorResNode curRel : relResSet) {
        Set<SensorResNode> matchedAcqResSet = findMatchFromACQSet(acqResSet, curRel);
        if (matchedAcqResSet.isEmpty())
          //No matches
          continue;
        else {
          containBothACQREL = true;
          break;
        }
      }
      if (containBothACQREL) {
        Set<SensorResNode> p_SensorACQRemoval = Sets.newHashSet();
        Set<SensorResNode> p_SensorRELRemoval = Sets.newHashSet();

        SootMethod curMethod = curPair.getR();
        Logger.trace("FULLTRAV", "Method: " +
                curMethod.getSignature() +
                " Contains both ACQ and REL");

        boolean bChanged = traverseMethodWithIfContext(
                curMethod,
                p_SensorACQRemoval,
                p_SensorRELRemoval,
                acqResSet,
                relResSet,
                curInfeasibleEdges,
                curInfeasibleCalls);
        if (bChanged) {
          Logger.trace("FULLTRAV", "Res Changed");
          for (SensorResNode curNode : p_SensorACQRemoval) {
            // There is an issue in callgraph construction of geopaparazzi.
            // Ingore the result here
            if (xmlParser.getAppPackageName().equals("eu.hydrologis.geopaparazzi"))
              continue;
            pairACQMap.remove(curPair, curNode);
            Logger.trace("FULLTRAV", "ACQResNode: " + curNode + " Removed From ACQ");

          }
          for (SensorResNode curNode : p_SensorRELRemoval) {
            //relResSet.remove(curNode);
            pairRELMap.remove(curPair, curNode);
            Logger.trace("FULLTRAV", "RELResNode: " + curNode + " Removed From REL");
            SensorVarUtil.stmtResNodeMap.remove(curNode.stmt, curNode);
          }
          acqResSet = pairACQMap.get(curPair);
          relResSet = pairRELMap.get(curPair);
        }

      }

      //For each REL in relSet
      for (SensorResNode curRel :relResSet){
        Set<SensorResNode> matchedAcqResSet = findMatchFromACQSet(acqResSet, curRel);
        if (matchedAcqResSet.isEmpty())
          //No matches
          continue;
        for (SensorResNode curAcq: matchedAcqResSet){
          boolean bDownwardExposed = reverseICFGTraversal(
                  curAcq,
                  curRel,
                  curPair,
                  curInfeasibleEdges,
                  curInfeasibleCalls);

          if (!bDownwardExposed){
            //pairACQMap.get(curPair).remove(curAcq);
            Logger.trace("FULLTRV", "Downward exposure, remove ACQ" + curAcq);
            pairACQMap.remove(curPair,curAcq);
          }
        }
      }
    }


    Logger.trace("Dev", "ACQ PairInfo:");
    for (Pair<NObjectNode, SootMethod> curPair : pairACQMap.keySet()) {
      Set<SensorResNode> resNodes = pairACQMap.get(curPair);
      if (resNodes.isEmpty())
        Logger.trace("Dev", curPair.toString() + " ACQ: " + " Empty Set");
      else {
        Logger.trace("Dev", curPair.toString() + " ACQ: " + resNodes.toString());
        for (SensorResNode node :resNodes) {
          Logger.trace("Dev", "Hashcode: " + node.hashCode());
        }
      }
    }

    Logger.trace("Dev", "REL PairInfo:");
    for (Pair<NObjectNode, SootMethod> curPair : pairRELMap.keySet()) {
      Set<SensorResNode> resNodes = pairRELMap.get(curPair);
      if (resNodes.isEmpty())
        Logger.verb("Dev", curPair.toString() + " REL: " + " Empty Set");
      else
        Logger.verb("Dev", curPair.toString() + " REL: " + resNodes.toString());
    }


//     It might be unnecessary as well. So comment it out for now
//    //Phase 1 ended. Do Phase 2 part 2. Calculate the reachability of each REL
//    for (Pair<NObjectNode, SootMethod> curPair : Sets.newHashSet(pairRELMap.keySet())) {
//      Set<SensorResNode> resSet = Sets.newHashSet(pairRELMap.get(curPair));
//      SootMethod curMethod = curPair.getR();
//      //Get infeasibleEdges and infeasibleCalls of target method
//      HashMultimap<Stmt, Stmt> curInfeasibleEdges = getInfeasibleEdges(curPair);
//      HashMultimap<Stmt, SootMethod> curInfeasibleCalls = getInfeasibleCalls(curPair);
//
//      for (SensorResNode curRes : resSet){
//        boolean reached = traverseMethod(curMethod, curRes, curInfeasibleEdges, curInfeasibleCalls);
//        if (reached) {
//          //Remove the REL if there exists a path to exit without go through REL.
//          pairRELMap.remove(curPair, curRes);
//          //Add removed REL into a new Map, just in case it needs further analysis.
//          pairRemovedMap.put(curPair, curRes);
//        }
//      }
//    }
    //Phase 2 ended
//
//    Serve Rate not necessary, comment out
//    //Phase 3 Evaluate Serve Rate
//    VarUtil.v().severeRateMap = Maps.newHashMap();
//    for (ResNode curResNode : resNodeList){
//      List<SootMethod> callBackList = EnergyUtils.v().extractListenerCallback(curResNode);
//      boolean rel = false;
//      for (SootMethod curCallback : callBackList){
//        p_SessionACQ.clear();
//        p_SessionREL.clear();
//        traverseLocationChanged(curCallback, p_SessionREL, null, null);
//        if (p_SessionREL.isEmpty())
//          continue;
//        boolean hasConcreteREL = false;
//        for (ResNode curInsideRes : p_SessionREL){
//          boolean reached = traverseMethod(curCallback, curInsideRes, null, null);
//          if (!reached){
//            hasConcreteREL = true;
//          }
//        }
//        if (hasConcreteREL)
//          rel = true;
//      }
//      if (rel){
//        VarUtil.v().severeRateMap.put(curResNode, 1);
//      }else{
//        VarUtil.v().severeRateMap.put(curResNode, 0);
//      }
//    }
  }

  /**
   * Traverse the target method and calculate the reachabilty of target Resource
   * @param handler target method needs to be traversed
   * @param tgtRes  target resource
   * @param infeasibleEdges infeasibleEdges from constant propagation
   * @param infeasibleCalls infeasibleCalls from constant propagation
   * @return If the EXIT is reached while traverse stopped
   * at the target Resource. return true otherwise return false
   */
  private boolean traverseMethod(
          SootMethod handler,
          final SensorResNode tgtRes,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls){

    final SensorResNode target = tgtRes;

    final SootMethod inHander = handler;
    final Set<Stmt> escapedStmts = Sets.newHashSet();
    final Map<Stmt, SootMethod> visitedStmts = Maps.newHashMap();
    final Map<SootMethod, UnitGraph> methodToCFG = Maps.newHashMap();

    if (infeasibleEdges == null)
      infeasibleEdges = HashMultimap.create();
    if (infeasibleCalls == null)
      infeasibleCalls = HashMultimap.create();
    final String mtdTag = "TraverseMethod";

    Filter<Stmt, SootMethod> fF = new Filter<Stmt, SootMethod>() {
      public boolean match(Stmt unit, SootMethod sm) {

        if (unit.equals(tgtRes.stmt) && sm.equals(tgtRes.context)){
          return true;
        }else
          return false;
      }
    };

    List<Stmt> visitedSeq = Lists.newArrayList();

    IfNullUtil.v().forwardTraversalIfIgnore(
            handler,
            visitedStmts,
            visitedSeq,
            escapedStmts,
            methodToCFG,
            fF,
            infeasibleEdges,
            infeasibleCalls
    );

    UnitGraph handlerCFG = methodToCFG.get(handler);
    boolean reachToExit = false;
    for (Unit exitNode : handlerCFG.getTails()) {
      if (visitedStmts.containsKey(exitNode)) {
        reachToExit = true;
        break;
      }
    }

    return reachToExit;
  }



  public Set<SensorResNode> findMatchFromACQSet(Set<SensorResNode> acqSet, SensorResNode relSet) {
    Set<SensorResNode> retSet = Sets.newHashSet();
    for (SensorResNode curACQNode : acqSet) {
      if (curACQNode.listenerNode.equals(relSet.listenerNode)) {
        if (relSet.sensorNode == null) {
          Logger.trace("MATCH", "Found match " + curACQNode.toString());
          retSet.add(curACQNode);
        } else if (curACQNode.sensorNode.equals(relSet.sensorNode)) {
          Logger.trace("MATCH", "Found match " + curACQNode.toString());
          retSet.add(curACQNode);
        }
      }
    }
    return retSet;
  }

  public void debugOutputNodeSet(Set<NNode> nodeSet) {
    for (NNode node : nodeSet) {
      Logger.trace("DEBUG", "Node item " + node.toString());
    }
  }

  private Set<NSensorIdNode> retrieveNGetSensorOpNode(NGetSensorOpNode sensorOpNode) {
    FixpointSolver solver = SensorVarUtil.guiOutput.getSolver();
    Set<NSensorIdNode> retSet = Sets.newHashSet();
    if (solver.reachingSensorIds.containsKey(sensorOpNode)) {
      Set<NSensorIdNode> reachedSensorIdNode = solver.reachingSensorIds.get(sensorOpNode);
      for (NSensorIdNode sensorIdNode : reachedSensorIdNode) {
//        Logger.verb("SENSORID", String.format("SensorOP: %s reached %s", sensorOpNode.toString()
//                , sensorIdNode.toString()));
        retSet.add(sensorIdNode);

      }
    } else {
      Logger.verb("SENSORID", String.format("SensorOP: %s does not reach any sensorIDnode",
              sensorOpNode.toString()));
    }
    return retSet;
  }

  private boolean traverseMethodWithIfContext(
          SootMethod handler,
          Set<SensorResNode> p_sessionACQRemoval,
          Set<SensorResNode> p_sessionRELRemoval,
          Set<SensorResNode> p_originalACQ,
          Set<SensorResNode> p_originalREL,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {

    final SootMethod inHandler = handler;
    final Set<SensorResNode> in_sessionACQRemoval = p_sessionACQRemoval;
    in_sessionACQRemoval.addAll(p_originalACQ);
    final Set<SensorResNode> in_sessionRELRemoval = p_sessionRELRemoval;
    in_sessionRELRemoval.addAll(p_sessionRELRemoval);
    final Set<SensorResNode> in_originalACQ = p_originalACQ;
    final Set<SensorResNode> in_originalREL = p_originalREL;
    final Set<Stmt> escapedStmts = Sets.newHashSet();
    final Map<Stmt, SootMethod> visitedStmts = Maps.newHashMap();
    final Map<SootMethod, UnitGraph> methodToCFG = Maps.newHashMap();
    if (infeasibleEdges == null)
      infeasibleEdges = HashMultimap.create();
    if (infeasibleCalls == null)
      infeasibleCalls = HashMultimap.create();

    final QueryHelper queryHelper = QueryHelper.v();
    Filter<Stmt, SootMethod> fF = new Filter<Stmt, SootMethod>() {
      public boolean match(Stmt unit, SootMethod sm) {
        if (unit.containsInvokeExpr()) {
          //Logger.verb("DEBUGSTMT", "on Stmt " + unit.toString());
        }
        if (wtgUtil.isSensorAcquireCall(unit)) {
          // The first param is Listener
          // The second param is Sensor object
          Value listenerValue = unit.getInvokeExpr().getArg(0);
          Value sensorValue = unit.getInvokeExpr().getArg(1);
          Logger.trace("ACQUIRE", String.format("encountered at %s, context %s, handler %s",
                  unit, sm, handler));
          if (!(listenerValue instanceof Value)) {
            throw new RuntimeException("[ERROR]: the sensorListener is not type of local for stmt" +
                    " " + unit);
          }
          if (!(sensorValue instanceof Value)) {
            throw new RuntimeException("[ERROR]: the sensor is not type of local in unit: " + unit);
          }
          Set<NNode> listenerBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                  .guiOutput.getFlowgraph().simpleNode(listenerValue));
          Set<NNode> sensorBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                  .guiOutput.getFlowgraph().simpleNode(sensorValue));

          //Look for NListenerAllocNode in the backReachedNodes
          Set<NNode> listenerAllocNode = Sets.newHashSet();
          for (NNode curNode : listenerBackReachedNodes) {
//            if (curNode instanceof NListenerAllocNode) {
//              listenerAllocNode.add((NListenerAllocNode) curNode);
//            }
            if (isLegitSensorListenerNode(curNode)) {
              listenerAllocNode.add(curNode);
            }
          }

          Logger.trace("ACQUIRE", "Output Listener Nodes");
          debugOutputNodeSet(listenerAllocNode);

          Set<NNode> sensorIdNodeSet = Sets.newHashSet();
          for (NNode curNode : sensorBackReachedNodes) {
            if (curNode instanceof NGetSensorOpNode) {
              sensorIdNodeSet.addAll(retrieveNGetSensorOpNode((NGetSensorOpNode) curNode));
            }
          }

          Logger.trace("ACQUIRE", "Output Sensor Nodes");
          debugOutputNodeSet(sensorIdNodeSet);

          if (!listenerAllocNode.isEmpty()) {
            for (NNode listenerNode : listenerAllocNode) {
              for (NNode sensorNode : sensorIdNodeSet) {
//                SensorResNode resNode = new SensorResNode(sensorNode, listenerNode, unit,
//                        handler, sm);
//                m_sessionACQL.add(resNode);
                for (Iterator<SensorResNode> iterator = in_sessionACQRemoval.iterator(); iterator.hasNext();) {
                  SensorResNode curResNode = iterator.next();
                  if (curResNode.sensorNode.equals(sensorNode) && curResNode.listenerNode == listenerNode && unit == curResNode.stmt && curResNode.context == sm) {
                    Logger.trace("IFCONTEXT", "ACQResNode: " + curResNode.toString() + " Removed");
                    iterator.remove();
                  }
                }
              }
            }
          }
        }

        if (wtgUtil.isSensorReleaseCall(unit)) {

          SootMethod mtd = unit.getInvokeExpr().getMethod();
          Logger.trace("RELEASE", String.format("encountered at %s, context %s, handler %s",
                  unit, sm, handler));
          Value listenerValue = null;
          Value sensorValue = null;
          if (mtd.getSignature().equals(MethodNames.unregisterSensorListener0Sig)) {
            listenerValue = unit.getInvokeExpr().getArg(0);
          } else {
            listenerValue = unit.getInvokeExpr().getArg(0);
            sensorValue = unit.getInvokeExpr().getArg(1);
          }
          Set<NNode> listenerBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                  .guiOutput.getFlowgraph().simpleNode(listenerValue));
          Set<NNode> sensorBackReachedNodes = null;
          if (sensorValue != null) {
            sensorBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                    .guiOutput.getFlowgraph().simpleNode(sensorValue));
          } else {
            sensorBackReachedNodes = Sets.newHashSet();
          }

          //Look for NListenerAllocNode in the backReachedNodes
          Set<NNode> listenerAllocNode = Sets.newHashSet();
          for (NNode curNode : listenerBackReachedNodes) {
//            if (curNode instanceof NListenerAllocNode) {
//              listenerAllocNode.add((NListenerAllocNode) curNode);
//            }
            if (isLegitSensorListenerNode(curNode)) {
              listenerAllocNode.add(curNode);
            }
          }
          Logger.trace("RELEASE", "Output Listener Nodes");
          debugOutputNodeSet(listenerBackReachedNodes);

          Set<NNode> sensorIdNodeSet = Sets.newHashSet();
          for (NNode curNode : sensorBackReachedNodes) {
            if (curNode instanceof NGetSensorOpNode) {
              //sensorAllocNode.add((NGetSensorOpNode) curNode);
              sensorIdNodeSet.addAll(retrieveNGetSensorOpNode((NGetSensorOpNode) curNode));
            }
          }
          Logger.trace("RELEASE", "Output Sensor Nodes");
          debugOutputNodeSet(sensorIdNodeSet);
          debugOutputNodeSet(sensorBackReachedNodes);

          for (NNode listenerNode : listenerAllocNode) {
            if (sensorIdNodeSet.isEmpty()) {
              //It is possible that developer use unregisterListener directly on a listener
              // instead of a sensor and listener
//              SensorResNode resNode = new SensorResNode(null, listenerNode, unit,
//                      handler, sm);
//              m_sessionRELL.add(resNode);
              for (Iterator<SensorResNode> iterator = in_sessionRELRemoval.iterator(); iterator.hasNext();) {
                SensorResNode curResNode = iterator.next();
                Logger.trace("IFCONTEXT", "REL CurRes: " + curResNode.toString() + " listenerNode " + listenerNode );
                if (curResNode.listenerNode == listenerNode && curResNode.stmt == unit && curResNode.context == sm) {
                  Logger.trace("IFCONTEXT", "RELResNode " + curResNode + " Removed");
                  iterator.remove();

                }
              }
            } else {
              for (NNode sensorNode : sensorIdNodeSet) {
//                SensorResNode resNode = new SensorResNode(sensorNode, listenerNode, unit,
//                        handler, sm);
//                SensorVarUtil.stmtResNodeMap.put(unit, resNode);
//                m_sessionRELL.add(resNode);
                for (Iterator<SensorResNode> iterator = in_sessionRELRemoval.iterator(); iterator.hasNext();) {
                  SensorResNode curResNode = iterator.next();
                  if (curResNode.sensorNode.equals(sensorNode) && curResNode.listenerNode == listenerNode && unit == curResNode.stmt && curResNode.context == sm) {
                    Logger.trace("IFCONTEXT", "RELResNode: " + curResNode.toString() + " Removed");
                    iterator.remove();
                  }
                }
              }
            }
          }
        }
        return false;
      }
    };

    List<Stmt> visitedSeq = Lists.newArrayList();
    ExperimentalContextSensitiveTraversal.getInstance().forwardTraversalIfContext(
            inHandler,
            visitedStmts,
            visitedSeq,
            escapedStmts,
            methodToCFG,
            fF,
            infeasibleEdges,
            infeasibleCalls);

    if (in_sessionACQRemoval.isEmpty() && in_sessionRELRemoval.isEmpty()) {
      return false;
    } else {
      return true;
    }
  }

  private boolean isLegitSensorListenerNode(NNode node) {
    if (node instanceof NListenerAllocNode || node instanceof NWindowNode) {
      SootClass c = ((NObjectNode) node).getClassType();
      Hierarchy hier = Hierarchy.v();
      SootClass sensorEventListener = Scene.v().getSootClass("android.hardware" +
              ".SensorEventListener");
      if (sensorEventListener == null) {
        Logger.err("WARNING", "SENSOREventListener type is null");
      }
      Logger.trace("LEGIT", "Compare " + c.getName() + " to " + sensorEventListener.getName());
      boolean ret = c.getInterfaces().contains(sensorEventListener);
       //= hier.isSubclassOf(c, sensorEventListener);
      Logger.trace("LEGIT", "ret: " + ret);
      if (!ret) {
        for (SootClass curInt: c.getInterfaces()) {
          Logger.trace("LEGIT", "INTERFACE " + curInt.getName());
        }
      }
      return ret;
    }
    return false;
  }

  /**
   * Traverse the target method without computing reachability. return true
   * @param handler method needs to be traversed
   * @param p_sessionACQ map used to save any ACQ resources found in this method
   * @param p_sessionREL map used to save any REL resources found in this method
   * @param infeasibleEdges infeasibleEdges from the constant propagation. Could be null
   * @param infeasibleCalls infeasibleCalls from the constant propagation. Could be null
   * @return  If any ACQ or REL is found, return true otherwise return false.
   */
  private boolean traverseMethodFull(
          SootMethod handler,
          Set<SensorResNode> p_sessionACQ,
          Set<SensorResNode> p_sessionREL,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls

  ) {

    //Logger.verb("DEBUG", "Traverse on method" + handler.toString());

    final SootMethod inHandler = handler;

    final List<SensorResNode> m_sessionACQL = Lists.newArrayList();
    final List<SensorResNode> m_sessionRELL = Lists.newArrayList();
    final Set<Stmt> escapedStmts = Sets.newHashSet();
    final Map<Stmt, SootMethod> visitedStmts = Maps.newHashMap();
    final Map<SootMethod, UnitGraph> methodToCFG = Maps.newHashMap();
    if (infeasibleEdges == null)
      infeasibleEdges = HashMultimap.create();
    if (infeasibleCalls == null)
      infeasibleCalls = HashMultimap.create();
    final QueryHelper queryHelper = QueryHelper.v();

    final String mtdTag = "TRAVSEMTDFF";
    final String fltTag = "TRAVEMTDFF_FT";

    Filter<Stmt, SootMethod> fF = new Filter<Stmt, SootMethod>() {
      public boolean match(Stmt unit, SootMethod sm) {
        if (unit.containsInvokeExpr()) {
          //Logger.verb("DEBUGSTMT", "on Stmt " + unit.toString());
//          SootMethod target = unit.getInvokeExpr().getMethod();
//          if (target.getName().contains("handleWhistleTouch")) {
//            Logger.verb("Dev", unit.toString());
//          } else if (target.getName().contains("handleTimerActivation")) {
//            Logger.verb("Dev", unit.toString());
//            Logger.verb("Dev", target.retrieveActiveBody().toString());
//          } else if (target.getName().contains("registerListener")) {
//            Logger.verb("Dev", unit.toString());
//          }
        }
        if (wtgUtil.isSensorAcquireCall(unit)) {
          // The first param is Listener
          // The second param is Sensor object
          Value listenerValue = unit.getInvokeExpr().getArg(0);
          Value sensorValue = unit.getInvokeExpr().getArg(1);
          Logger.trace("ACQUIRE", String.format("encountered at %s, context %s, handler %s",
                  unit, sm, handler));
          if (!(listenerValue instanceof Value)) {
            throw new RuntimeException("[ERROR]: the sensorListener is not type of local for stmt" +
                    " " + unit);
          }
          if (!(sensorValue instanceof Value)) {
            throw new RuntimeException("[ERROR]: the sensor is not type of local in unit: " + unit);
          }
          Set<NNode> listenerBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                  .guiOutput.getFlowgraph().simpleNode(listenerValue));
          Set<NNode> sensorBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                  .guiOutput.getFlowgraph().simpleNode(sensorValue));

          //Look for NListenerAllocNode in the backReachedNodes
          Set<NNode> listenerAllocNode = Sets.newHashSet();
          for (NNode curNode : listenerBackReachedNodes) {
//            if (curNode instanceof NListenerAllocNode) {
//              listenerAllocNode.add((NListenerAllocNode) curNode);
//            }
            if (isLegitSensorListenerNode(curNode)) {
              listenerAllocNode.add(curNode);
            }
          }

          Logger.trace("ACQUIRE", "Output Listener Nodes");
          debugOutputNodeSet(listenerAllocNode);

          Set<NNode> sensorIdNodeSet = Sets.newHashSet();
          for (NNode curNode : sensorBackReachedNodes) {
            if (curNode instanceof NGetSensorOpNode) {
              sensorIdNodeSet.addAll(retrieveNGetSensorOpNode((NGetSensorOpNode) curNode));
            }
          }

          Logger.trace("ACQUIRE", "Output Sensor Nodes");
          debugOutputNodeSet(sensorIdNodeSet);

          if (!listenerAllocNode.isEmpty()) {
            for (NNode listenerNode : listenerAllocNode) {
              for (NNode sensorNode : sensorIdNodeSet) {
                SensorResNode resNode = new SensorResNode(sensorNode, listenerNode, unit,
                        handler, sm);
                m_sessionACQL.add(resNode);
              }
            }
          }
        }

        if (wtgUtil.isSensorReleaseCall(unit)) {

          SootMethod mtd = unit.getInvokeExpr().getMethod();
          Logger.trace("RELEASE", String.format("encountered at %s, context %s, handler %s",
                  unit, sm, handler));
          Value listenerValue = null;
          Value sensorValue = null;
          if (mtd.getSignature().equals(MethodNames.unregisterSensorListener0Sig)) {
            listenerValue = unit.getInvokeExpr().getArg(0);
          } else {
            listenerValue = unit.getInvokeExpr().getArg(0);
            sensorValue = unit.getInvokeExpr().getArg(1);
          }
          Set<NNode> listenerBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                  .guiOutput.getFlowgraph().simpleNode(listenerValue));
          Set<NNode> sensorBackReachedNodes = null;
          if (sensorValue != null) {
            sensorBackReachedNodes = queryHelper.allVariableValues(SensorVarUtil
                    .guiOutput.getFlowgraph().simpleNode(sensorValue));
          } else {
            sensorBackReachedNodes = Sets.newHashSet();
          }

          //Look for NListenerAllocNode in the backReachedNodes
          Set<NNode> listenerAllocNode = Sets.newHashSet();
          for (NNode curNode : listenerBackReachedNodes) {
//            if (curNode instanceof NListenerAllocNode) {
//              listenerAllocNode.add((NListenerAllocNode) curNode);
//            }
            if (isLegitSensorListenerNode(curNode)) {
              listenerAllocNode.add(curNode);
            }
          }
          Logger.trace("RELEASE", "Output Listener Nodes");
          debugOutputNodeSet(listenerAllocNode);

          Set<NNode> sensorIdNodeSet = Sets.newHashSet();
          for (NNode curNode : sensorBackReachedNodes) {
            if (curNode instanceof NGetSensorOpNode) {
              //sensorAllocNode.add((NGetSensorOpNode) curNode);
              sensorIdNodeSet.addAll(retrieveNGetSensorOpNode((NGetSensorOpNode) curNode));
            }
          }
          Logger.trace("RELEASE", "Output Sensor Nodes");
          debugOutputNodeSet(sensorIdNodeSet);
          debugOutputNodeSet(sensorBackReachedNodes);

          for (NNode listenerNode : listenerAllocNode) {
            if (sensorIdNodeSet.isEmpty()) {
              //It is possible that developer use unregisterListener directly on a listener
              // instead of a sensor and listener
              SensorResNode resNode = new SensorResNode(null, listenerNode, unit,
                      handler, sm);
              m_sessionRELL.add(resNode);
              SensorVarUtil.stmtResNodeMap.put(unit, resNode);
            } else {
              for (NNode sensorNode : sensorIdNodeSet) {
                SensorResNode resNode = new SensorResNode(sensorNode, listenerNode, unit,
                        handler, sm);
                SensorVarUtil.stmtResNodeMap.put(unit, resNode);
                m_sessionRELL.add(resNode);
              }
            }
          }
        }
        return false;
      }
    };
    List<Stmt> visitedSeq = Lists.newArrayList();
    ExperimentalContextSensitiveTraversal.getInstance().forwardTraversalMod(
            handler,
            visitedStmts,
            visitedSeq,
            escapedStmts,
            methodToCFG,
            fF,
            infeasibleEdges,
            infeasibleCalls
    );

    if (m_sessionACQL.isEmpty() && m_sessionRELL.isEmpty()) {
      //No energy related operations
      return false;
    }
    //Dump visited Seq

    if (!m_sessionACQL.isEmpty()) {
      p_sessionACQ.clear();
      for (SensorResNode curNode : m_sessionACQL) {
        p_sessionACQ.add(curNode);
        allAvailableResNode.add(curNode);
      }
    }

    if (!m_sessionRELL.isEmpty()) {
      p_sessionREL.clear();
      for (SensorResNode curNode : m_sessionRELL) {
        p_sessionREL.add(curNode);
        allAvailableResNode.add(curNode);
      }
    }
    return true;
  }

}
