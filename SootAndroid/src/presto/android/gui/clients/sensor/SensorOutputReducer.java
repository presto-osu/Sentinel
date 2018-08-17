package presto.android.gui.clients.sensor;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import com.google.common.collect.Sets;
import presto.android.Logger;
import presto.android.gui.clients.energy.Pair;
import presto.android.gui.graph.NNode;
import presto.android.gui.graph.NObjectNode;
import presto.android.gui.listener.EventType;
import presto.android.gui.wtg.EventHandler;
import presto.android.gui.wtg.ds.WTGEdge;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by zero on 2/21/17.
 */
public class SensorOutputReducer {
  public enum PathType{
    C1, C2
  }

  public enum OutputType{
    COMPLETE, MINIMAL
  }

  class Path {
    Set<NObjectNode> widgetSet;
    List<List<WTGEdge>> pathList;
    Set<SensorResNode> resourceSet;
    List<WTGEdge> minPath;
    Integer severeLevel;

    public boolean compareSet(Set<SensorResNode> another){
      if (another.size() == resourceSet.size()){
        for (SensorResNode iNode : another){
          if (!this.resourceSet.contains(iNode))
            return false;
        }
        return true;
      }
      return false;
    }

    public Path(Set<NObjectNode> widgetSet, Set<SensorResNode> resourceSet){
      this.widgetSet = widgetSet;
      this.resourceSet = resourceSet;
      this.pathList = Lists.newArrayList();
      this.severeLevel = 0;
    }

    public void addPath(List<WTGEdge> l){
      if (minPath == null){
        minPath = l;
      } else if (minPath.size() == l.size() &&
              l.get(l.size()-1).getEventType() == EventType.implicit_back_event) {
        minPath = l;
      } else if (minPath.size() > l.size()){
        minPath = l;
      }
      pathList.add(l);
    }

//    public void calculateSevereLevel(){
//      severeLevel = 0;
//      if (!resourceSet.isEmpty()){
//        Map<SensorResNode, Integer> sMap = VarUtil.v().severeRateMap;
//        for (SensorResNode curRes : resourceSet){
//          if (sMap.containsKey(curRes)){
//            Integer i = sMap.get(curRes);
//            if (i != null && i == 1)
//              severeLevel = 1;
//          }
//        }
//      }
//    }
  }

  class Tupple <K, E, V> {
    public K item1;
    public E item2;
    public V item3;

    public Tupple(K k, E e, V v) {
      item1 = k;
      item2 = e;
      item3 = v;
    }
    @Override
    public int hashCode() {
      return item1.hashCode() + item2.hashCode() + item3.hashCode();
    }

    @Override
    public boolean equals(Object b) {
      if (b instanceof Tupple) {
        Tupple t = (Tupple) b;
        return item1.equals(t.item1) && item2.equals(t.item2) && item3.equals(t.item3);
      }
      return false;
    }

    @Override
    public String toString() {
      return item1.toString() + " " + item2.toString() + " " + item3;
    }
  }

  //HashMultimap<NObjectNode, SensorOutputReducer.Path> mData;
  HashMultimap<Set<NObjectNode>, SensorOutputReducer.Path> mData;
  SensorOutputReducer.PathType mCategoryType;
  Map<List<WTGEdge>, List<SensorResNode>> mPathResMap;
  public String absPath = "";

  public SensorOutputReducer(SensorOutputReducer.PathType c){
    this.mData = HashMultimap.create();
    this.mCategoryType = c;
  }

  public int getUniqueIssues(){
    int sum = 0;
//    for (Set<NObjectNode> curObjNodeSet : this.mData.keySet()){
//      sum += this.mData.get(curObjNodeSet).size();
//    }
    for (Set<Tupple<NNode, NNode, SootMethod>> tuppleSet : this.tupplesCollection.keySet()) {
      sum += this.tupplesCollection.get(tuppleSet).size();
    }
    return sum;
  }

  public void parseOutput(Map<List<WTGEdge>, List<SensorResNode>> pathResMap){
    this.mPathResMap = pathResMap;
    for (List<WTGEdge> curPath : pathResMap.keySet()){
      //While very unlikely. Test if the path is empty
      if (curPath.isEmpty())
        continue;

      //NObjectNode curObjectNode = curPath.get(0).getTargetNode().getWindow();
      Set<NObjectNode> curObjectNodeSet = Sets.newHashSet();
      Set<SensorResNode> curResSet = Sets.newHashSet(pathResMap.get(curPath));
      for (SensorResNode resNode : curResSet) {
        if (resNode.guiWidget != null)
          curObjectNodeSet.add(resNode.guiWidget);
      }
      if (curObjectNodeSet.isEmpty())
        curObjectNodeSet.add(curPath.get(0).getTargetNode().getWindow());
      if (!mData.containsKey(curObjectNodeSet)){
        SensorOutputReducer.Path curPathNode = new SensorOutputReducer.Path(curObjectNodeSet, curResSet);
        curPathNode.addPath(curPath);
        mData.put(curObjectNodeSet, curPathNode);
      }else{
        //It does have an entry for this Node
        Set<SensorOutputReducer.Path> curPathSet = mData.get(curObjectNodeSet);
        SensorOutputReducer.Path targetPathNode = null;
        for (SensorOutputReducer.Path curPathNode : curPathSet){
          if (curPathNode.compareSet(curResSet)){
            targetPathNode = curPathNode;
            break;
          }
        }
        if (targetPathNode == null){
          targetPathNode = new SensorOutputReducer.Path(curObjectNodeSet, curResSet);
          targetPathNode.addPath(curPath);
          mData.put(curObjectNodeSet, targetPathNode);
        }else{
          targetPathNode.addPath(curPath);
        }
      }
    }
    sameParentMerger();
    int countMerged = 0;
    Logger.trace("MERGER", "Tupples count " + tupplesCollection.keySet().size());
    for (Set<Tupple<NNode, NNode, SootMethod>> tupple : tupplesCollection.keySet()) {
      Logger.trace("MERGE", "Tupple " + tupple.toString());
      countMerged += tupplesCollection.get(tupple).size();
    }
    Logger.trace("MERGER", "Count: " + countMerged);
  }

  Map<Set<Tupple<NNode, NNode, SootMethod>>, List<List<WTGEdge>>> tupplesCollection;
  public void sameParentMerger() {
    int totalMinCount = 0;
    tupplesCollection = Maps.newHashMap();
    for (Set<NObjectNode> widgetNodeSet : this.mData.keySet()) {
      for (SensorOutputReducer.Path path : this.mData.get(widgetNodeSet)) {
        Set<Tupple<NNode, NNode, SootMethod>> curTuppleSet =
                Sets.newHashSet();
        for (SensorResNode res : path.resourceSet) {
          Tupple<NNode, NNode, SootMethod> curTupple = new
                  Tupple<>(res.sensorNode, res.listenerNode, res.context);
          curTuppleSet.add(curTupple);
        }
        if (!tupplesCollection.containsKey(curTuppleSet)) {
          tupplesCollection.put(curTuppleSet, Lists.newArrayList());
        }
        //tupplesCollection.get(curTuppleSet).add(path.minPath);
        totalMinCount++;
        addPathToCollection(curTuppleSet, path.minPath);
      }
    }
    Logger.trace("MERGE", "Candidate Path count: " + totalMinCount);
  }

  public void addPathToCollection(
          Set<Tupple<NNode, NNode, SootMethod>> tuppleSet,
          List<WTGEdge> path) {
    if (tupplesCollection.get(tuppleSet).isEmpty()) {
      this.tupplesCollection.get(tuppleSet).add(path);
    } else {
      boolean bAdd = true;
      for (List<WTGEdge> prevPath : this.tupplesCollection.get(tuppleSet)) {
        Set<SensorResNode> setForPrev = Sets.newHashSet(this.mPathResMap.get(prevPath));
        Set<SensorResNode> setForCur = Sets.newHashSet(this.mPathResMap.get(path));
        int prevCount = setForPrev.size();
        Logger.trace("MERGE", "Size before removal " + setForPrev.size());
        if (setForCur.size() == setForPrev.size()) {
          matchAndRemoval(setForPrev, setForCur);
        }
        Logger.trace("MERGE", "Size after removal " + setForPrev.size());
        if (prevCount != setForPrev.size()) {
          for (SensorResNode prevRes : setForPrev) {
            Logger.trace("MERGE", "Remaining: " + prevRes.toString());
          }
          Logger.trace("MERGE", "");
        }
        if (setForPrev.size() == 0) {
          bAdd = false;
        }
      }

      if (bAdd)
        this.tupplesCollection.get(tuppleSet).add(path);
    }
  }

  public SensorResNode retrieveParent(SensorResNode res) {
    SensorResNode ret = res;
    SootClass decl = res.handler.getDeclaringClass();
    SootClass activityClass = Scene.v().getSootClass("android.app.Activity");
    do {
      decl = decl.getSuperclassUnsafe();

      if (decl != null) {
        Logger.trace("MERGE", "On Class " + decl.toString());
        try {
          SootMethod target = decl.getMethod(res.handler.getSubSignature());
          if (target == null)
            continue;
          List<Pair<NObjectNode, SootMethod>> resPairs = Lists.newArrayList();
          for (Pair<NObjectNode, SootMethod> curPair :
                  SensorVarUtil.analyzer.allPairs) {
            if (curPair.getR().equals(target)) {
              resPairs.add(curPair);
            }
          }
          if (resPairs.size() > 1) {
            Logger.trace("MERGE", "Found more than 1 candidate for method: "
                    + target.getSignature());
            for (Pair<NObjectNode, SootMethod> curPair : resPairs) {
              Logger.trace("MERGE", curPair.toString());
            }
          }
          for (Pair<NObjectNode, SootMethod> curPair : resPairs) {
            Set<SensorResNode> resSet = SensorVarUtil.analyzer
                    .pairACQMap.get(curPair);
            if (resSet == null)
              continue;
            for (SensorResNode resNode : resSet) {
              if (res.sensorNode == resNode.sensorNode &&
                      res.listenerNode == resNode.listenerNode &&
                      res.context == resNode.context)
                ret = resNode;
              Logger.trace("MERGE", "Found matching for " + res.toString()
                      + " to " + resNode.toString());
            }
          }
        } catch (Exception e) {
          continue;
        }
      }
    } while (!(decl == null || decl.isPhantom() || decl.equals(activityClass)));
    return ret;
  }

  public void matchAndRemoval(Set<SensorResNode> prev, Set<SensorResNode> cur) {
    for (SensorResNode res: cur) {
      for (Iterator<SensorResNode> iter = prev.iterator(); iter.hasNext();) {
        SensorResNode target = iter.next();
        if (res.sensorNode == target.sensorNode &&
            res.listenerNode == target.listenerNode &&
            res.context == target.context) {
          if (res.handler == target.handler) {
            iter.remove();
            break;
          } else {
            // Test parent activity relationship
            SensorResNode pCur = retrieveParent(res);
            SensorResNode pTar = retrieveParent(target);
            Logger.trace("MERGECMP", pCur.toString());
            Logger.trace("MERGECMP", pTar.toString());
            Logger.trace("MERGECMP", "");
            if (pCur.handler == pTar.handler)
              iter.remove();
              break;
          }
        }
      }
    }
  }



  private String parseLeakingResNode(Set<SensorResNode> resSet){
    StringBuilder sb = new StringBuilder();
    for (SensorResNode curNode : resSet){
      sb.append("\t" + curNode.toString() + "\n");
    }
    return sb.toString();
  }

  public void outputToFileMerge(String fileName,
                                SensorOutputReducer.OutputType type) {
    if (this.mPathResMap == null)
      return;

    if (type == SensorOutputReducer.OutputType.MINIMAL){
      File outputFile;
      try{
        outputFile = new File(fileName);
        if (!outputFile.exists()) {
          outputFile.createNewFile();
        } else {
          outputFile.delete();
          outputFile.createNewFile();
        }
        absPath = outputFile.getAbsolutePath();
        FileWriter fw = new FileWriter(outputFile.getAbsoluteFile());
        BufferedWriter bw = new BufferedWriter(fw);
        bw.write("Paths with Sensor Issues: \n");

        for (Set<Tupple<NNode, NNode, SootMethod>> tuppleSet :
                this.tupplesCollection.keySet()) {
          for (List<WTGEdge> curPath : this.tupplesCollection.get(tuppleSet)) {
            Set<NObjectNode> widgetSet = Sets.newHashSet();
            Set<SensorResNode> curResSet = Sets.newHashSet(this.mPathResMap.get(curPath));
            for (SensorResNode resNode : curResSet) {
              if (resNode.guiWidget != null)
                widgetSet.add(resNode.guiWidget);
            }
            if (widgetSet.isEmpty())
              widgetSet.add(curPath.get(0).getTargetNode().getWindow());

            bw.write("\nFor Window and Widget: \n");
            for (NObjectNode widget : widgetSet) {
              bw.write("\t" + widget.toString() + "\n");
            }


            bw.write("\n\tLeaking Resources: \n");
            bw.write(parseLeakingResNode(curResSet));
            //curPathNode.calculateSevereLevel();
            bw.write("\n\tLeaking Path:\n");
            for (WTGEdge curEdge: curPath){
              //String curLine = curEdge.toString();
              StringBuilder sb = new StringBuilder();
              sb.append("\t" + curEdge.toString());
              Set<SootMethod> handlerMethodSet = curEdge.getEventHandlers();
              for (SootMethod curMethod: handlerMethodSet){
                sb.append("\n\t\t"+curMethod.toString());
              }

              for (EventHandler evt : curEdge.getCallbacks()){
                SootMethod curMethod = evt.getEventHandler();
                sb.append("\n\t\t"+curMethod.toString());
              }
              sb.append("\n\n");
              bw.write(sb.toString());
            }
            bw.write("\tLeaking Path End\n");
          }

        }

        bw.close();
      } catch(Exception e){
        e.printStackTrace();
      }
    }
  }

  public void outputToFile(String fileName, SensorOutputReducer.OutputType type) {
    if (this.mPathResMap == null)
      return;

    if (type == SensorOutputReducer.OutputType.MINIMAL){
      File outputFile;
      try{
        outputFile = new File(fileName);
        if (!outputFile.exists()) {
          outputFile.createNewFile();
        } else {
          outputFile.delete();
          outputFile.createNewFile();
        }
        absPath = outputFile.getAbsolutePath();
        FileWriter fw = new FileWriter(outputFile.getAbsoluteFile());
        BufferedWriter bw = new BufferedWriter(fw);
        bw.write("Paths with Sensor Issues: \n");
        for (Set<NObjectNode> widgetSet : this.mData.keySet()) {
          bw.write("\nFor Window and Widget: \n");
          for (NObjectNode widget : widgetSet) {
            bw.write("\t" + widget.toString() + "\n");
          }
          Set<SensorOutputReducer.Path> curPathSet = this.mData.get(widgetSet);
          for (SensorOutputReducer.Path curPathNode : curPathSet){
            //Output the leaking ResNodes
            bw.write("\n\tLeaking Resources: \n");
            bw.write(parseLeakingResNode(curPathNode.resourceSet));
            //curPathNode.calculateSevereLevel();
            if (curPathNode.severeLevel == 0)
              bw.write("\n\tSevere Rating: High\n");
            else if (curPathNode.severeLevel == 1)
              bw.write("\n\tSevere Rating: Low\n");

            //Output the minimal Path
            bw.write("\n\tLeaking Path:\n");
            for (WTGEdge curEdge: curPathNode.minPath){
              //String curLine = curEdge.toString();
              StringBuilder sb = new StringBuilder();
              sb.append("\t" + curEdge.toString());
              Set<SootMethod> handlerMethodSet = curEdge.getEventHandlers();
              for (SootMethod curMethod: handlerMethodSet){
                sb.append("\n\t\t"+curMethod.toString());
              }

              for (EventHandler evt : curEdge.getCallbacks()){
                SootMethod curMethod = evt.getEventHandler();
                sb.append("\n\t\t"+curMethod.toString());
              }
              sb.append("\n\n");
              bw.write(sb.toString());
            }
            bw.write("\tLeaking Path End\n");
          }
        }
        bw.close();
      }catch(Exception e){
        e.printStackTrace();
      }
    }
  }
}
