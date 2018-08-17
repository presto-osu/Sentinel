package presto.android.gui.clients.sensor;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import presto.android.Logger;
import presto.android.gui.clients.energy.IfNullUtil;
import presto.android.gui.clients.energy.VarUtil;
import presto.android.gui.graph.NNode;
import presto.android.gui.graph.NObjectNode;
import presto.android.gui.wtg.flowgraph.AndroidCallGraph;
import presto.android.gui.wtg.util.Filter;
import presto.android.gui.wtg.util.QueryHelper;
import presto.android.gui.wtg.util.WTGUtil;
import soot.*;
import soot.jimple.*;
import soot.toolkits.exceptions.ThrowableSet;
import soot.toolkits.graph.ExceptionalUnitGraph;
import soot.toolkits.graph.UnitGraph;

import javax.xml.parsers.ParserConfigurationException;
import java.lang.reflect.Field;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by zero on 3/2/17.
 */
public class ExperimentalContextSensitiveTraversal {
  private static ExperimentalContextSensitiveTraversal instance;

  private AndroidCallGraph cg;
  private WTGUtil wtgUtil;

  public static ExperimentalContextSensitiveTraversal getInstance() {
    if (instance == null) {
      instance = new ExperimentalContextSensitiveTraversal();
    }
    return instance;
  }

  private ExperimentalContextSensitiveTraversal() {
    cg = AndroidCallGraph.v();
    wtgUtil = WTGUtil.v();
  }

  private boolean isLocalNotNull(Local l, SootMethod context) {
    int x = 0;
    final String mtdTag = "LOCNULL";
    QueryHelper queryHelper = QueryHelper.v();
    Set<NNode> backReachedNodes = queryHelper.allVariableValues(VarUtil.v().guiOutput.getFlowgraph().simpleNode(l));
    boolean bDebug = false;
    if (bDebug) {
      if (backReachedNodes == null || backReachedNodes.size() == 0) {
        Logger.verb(mtdTag, "For Local " + l.toString() + " Queryhelper return empty");
      } else {
        for (NNode curNode : backReachedNodes) {
          Logger.verb(mtdTag, "For Local " + l.toString() + " Queryhelper return " + curNode.toString());
        }
      }
    }
    for (NNode backReachedNode : backReachedNodes) {
      if (backReachedNode instanceof NObjectNode) {
        x++;
        NObjectNode resource = (NObjectNode) backReachedNode;
        return true;
      }
    }
    return false;
  }

  private void propagateTrueBranch(
          ExceptionalUnitGraph currentCFG,
          IfStmt curIfStmt,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> workingList,
          List<Stmt> visitedSeq,
          SootMethod currentCxt) {
    //True target
    Unit target = curIfStmt.getTarget();
    if (!(target instanceof Stmt)) {
      return;
    }
    Logger.verb("IfStmt", "propagate true branch, "
            + curIfStmt.toString() + "Target " + target.toString());
    propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) target, currentCxt);
  }

  private void propagateFalseBranch(
          ExceptionalUnitGraph currentCFG,
          IfStmt curIfStmt,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> workingList,
          List<Stmt> visitedSeq,
          SootMethod currentCxt) {
    //True target
    Unit target = curIfStmt.getTarget();
    List<Unit> targets =Lists.newArrayList(currentCFG.getUnexceptionalSuccsOf(curIfStmt));
    if (targets.contains(target)) {
      targets.remove(target);
    } else {
      Logger.verb("propagateFalseBranch", "True branch is not found in successors");
    }
    for (Unit fbTarget : targets) {
      if (fbTarget instanceof Stmt) {
        Logger.verb("IfStmt", "propagate false branch, "
                + curIfStmt.toString() + " Target " + fbTarget.toString());
        propagateMod(visitedStmts, workingList, visitedSeq, (Stmt)fbTarget, currentCxt);
      }
    }
  }

  private boolean propageIfStmt(
          Stmt currentStmt,
          SootMethod currentCxt,
          List<Stmt> workingList,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          ExceptionalUnitGraph currentCFG,
          Context executionContext

  ){
    final String mtdTag = "PROIF";


    IfStmt curIfStmt = (IfStmt) currentStmt;
    Value curIFVal = curIfStmt.getCondition();
    if (true && (curIFVal instanceof NeExpr || curIFVal instanceof EqExpr)) {

      BinopExpr binExpr = (BinopExpr) curIFVal;
      Value Op1 = binExpr.getOp1();
      Value Op2 = binExpr.getOp2();
      //Logger.verb(mtdTag, "Op1: " + Op1 + " Type: " + Op1.getClass().getSimpleName());
      //Logger.verb(mtdTag, "Op2: " + Op1 + " Type: " + Op2.getClass().getSimpleName());
      if (Op1 instanceof NullConstant || Op2 instanceof  NullConstant) {

        if (Op1 instanceof NullConstant || Op2 instanceof NullConstant) {
          propagateTrueBranch(currentCFG, curIfStmt, visitedStmts, workingList, visitedSeq, currentCxt);
          return true;
        }
        Local curLocal = null;
        if (Op1 instanceof Local) {
          curLocal = (Local)Op1;
        }
        if (Op2 instanceof Local) {
          curLocal = (Local)Op2;
        }
        if (curLocal != null) {
          boolean localNotNull = isLocalNotNull(curLocal, currentCxt);
          if (curIFVal instanceof NeExpr && localNotNull) {
            propagateTrueBranch(currentCFG, curIfStmt, visitedStmts, workingList, visitedSeq,
                    currentCxt);
            return true;
          } else if (curIFVal instanceof EqExpr && localNotNull) {
            propagateFalseBranch(currentCFG, curIfStmt, visitedStmts, workingList, visitedSeq,
                    currentCxt);
            return true;
          } else {
            return false;
          }
        }
      } else if (true && (Op1 instanceof IntConstant || Op2 instanceof IntConstant)) {
        //Compare to an integer constant
        IntConstant ifConstant = null;
        Local comparingLocal = null;
        boolean constantEq = false;
        if (Op1 instanceof IntConstant && Op2 instanceof IntConstant) {
          //Both ops are constant.
          if (((IntConstant)Op1).value == (((IntConstant)Op2).value)) {
            constantEq = true;
          }
        } else {
          if (Op1 instanceof IntConstant) {
            ifConstant = (IntConstant)Op1;
          } else if (Op1 instanceof Local) {
            comparingLocal = (Local) Op1;
          }

          if (Op2 instanceof IntConstant) {
            ifConstant = (IntConstant)Op2;
          } else if (Op2 instanceof Local) {
            comparingLocal = (Local) Op2;
          }

          if (comparingLocal == null || ifConstant == null) {
            //Cannot compare at this point.
            return false;
          }

          List<NNode> retNode = executionContext.lookupPossibleConstantValue(comparingLocal);
          List<NIntConstantNode> filteredNodes = Lists.newArrayList();
          for (NNode curNode : retNode) {
            if (curNode instanceof NIntConstantNode) {
              filteredNodes.add((NIntConstantNode) curNode);
            }
          }
          if (filteredNodes.isEmpty()) {
            //No constant value can be determined, cannot compare.
            return false;
          }
          NIntConstantNode targetConstantNode = null;
          for (NIntConstantNode curNode : filteredNodes) {
            if (targetConstantNode == null) {
              targetConstantNode = curNode;
            } else {
              if (targetConstantNode.value == curNode.value) {
                continue;
              } else {
                //Multiple value for local, cannot compare
                Logger.trace("IfStmt", "Multiple value for local, cannot compare. In context " +
                        currentCxt.getSignature());
                dumpConstantPool(filteredNodes, ifConstant);
                return false;
              }
            }
          }
          Logger.trace("IfStmt", "target int " + targetConstantNode.value + " compareInt " +
                  ifConstant.value + " in context " + currentCxt.getSignature());
          if (targetConstantNode.value == ifConstant.value) {
            constantEq = true;
          } else {
            constantEq = false;
          }
        }

        if ((curIFVal instanceof EqExpr && constantEq) || ((curIFVal instanceof NeExpr) &&
                (!constantEq))) {
          propagateTrueBranch(currentCFG, curIfStmt, visitedStmts, workingList, visitedSeq,
                  currentCxt);
          return true;
        } else  {
          propagateFalseBranch(currentCFG, curIfStmt, visitedStmts, workingList, visitedSeq,
                  currentCxt);
          return true;
        }
      }
    }

    return false;
  }

  private void dumpConstantPool(List<NIntConstantNode> pool, IntConstant constant) {
    if (constant != null) {
      Logger.trace("IfStmt", "Int constant in if is " + constant.value);
    }
    Logger.trace("IfStmt", "Pool start");
    for (NIntConstantNode nConstant : pool) {
      Logger.trace("IfStmt", "Pool int " + nConstant.value);
    }
    Logger.trace("IfStmt", "Pool end");
  }

  private ExceptionalUnitGraph createOrGetECFG(
          Map<SootMethod, UnitGraph> methodToCFG,
          SootMethod mtd) {
    UnitGraph cfg = methodToCFG.get(mtd);
    if (cfg == null || !(cfg instanceof  ExceptionalUnitGraph)) {
      synchronized (mtd) {
        cfg = new ExceptionalUnitGraph(mtd.retrieveActiveBody());
      }
      methodToCFG.put(mtd, cfg);
    }
    return (ExceptionalUnitGraph)cfg;
  }

  private UnitGraph createOrGetCFG(Map<SootMethod, UnitGraph> methodToCFG,
                                   SootMethod mtd) {
    UnitGraph cfg = methodToCFG.get(mtd);
    if (cfg == null) {
      synchronized(mtd) {
        cfg = new ExceptionalUnitGraph(mtd.retrieveActiveBody());
      }
      methodToCFG.put(mtd, cfg);
    }
    return cfg;
  }

  private void propagateMod(
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> workingList,
          List<Stmt> visitedSeq,
          Stmt s,
          SootMethod cxt) {
    //Logger.verb("PROPAGATE", "Propagate Stmt: " + s + " in method " + cxt.getSignature());
    if (!visitedStmts.containsKey(s)) {
      visitedStmts.put(s, cxt);
      workingList.add(s);
      visitedSeq.add(s);
    }
  }

  private synchronized List<Unit> getUnexceptionalSuccssor(ExceptionalUnitGraph currentCFG, Stmt currentStmt){
    return Lists.newArrayList(currentCFG.getUnexceptionalSuccsOf(currentStmt));
  }

  private synchronized List<ExceptionalUnitGraph.ExceptionDest> getExceptionalDest(ExceptionalUnitGraph currentCFG, Stmt currentStmt){
    return Lists.newArrayList(Lists.newArrayList(currentCFG.getExceptionDests(currentStmt)));
  }

  public boolean traverseWithIfFix(
          List<Stmt> workingList,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          Set<Stmt> escapedStmts,
          Map<SootMethod, UnitGraph> methodToCFG,
          Filter<Stmt, SootMethod> filter,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {
    final boolean bDebug = false;
    final String mtdTag = "TRVIF";
    boolean unexpected = false;
    Set<SootMethod> visitedMethods = Sets.newHashSet();

    //Initialize execution environment
    Context executionContext = new ConstantValContext();

    while (!workingList.isEmpty()) {
      Stmt currentStmt = workingList.remove(0);
      SootMethod currentCxt = visitedStmts.get(currentStmt);
//      Logger.verb("DUMP", "Visiting Stmt : " + currentStmt.toString() + " current Method " +
//              currentCxt.getSignature());
      if (currentCxt == null) {
        Logger.err(getClass().getSimpleName(), "can not find the calling context for stmt: "
                + currentStmt);
      }
      if (wtgUtil.isIgnoredMethod(currentCxt)) {
        continue;
      }
      if (filter.match(currentStmt, currentCxt)) {

        if (escapedStmts != null) {
          escapedStmts.add(currentStmt);
        }
        continue;
      }

      ExceptionalUnitGraph currentCFG = createOrGetECFG(methodToCFG, currentCxt);

      // switch case for 4 conditions
      // case 1: currentStmt is not a call and not exit of cfg
      if (!currentStmt.containsInvokeExpr()
              && !currentCFG.getTails().contains(currentStmt)) {
        //If it is a definition statement
        if (currentStmt instanceof DefinitionStmt) {
          executionContext.processDefinitionStmt((DefinitionStmt) currentStmt);
        }

        //If it is a if stmt
        if (currentStmt instanceof IfStmt) {
          if (propageIfStmt(currentStmt, currentCxt, workingList, visitedStmts, visitedSeq,
                  currentCFG, executionContext)){
            continue;
          }
        } // End of IF Stmt traverse

        //Do propagation for un-exceptional successors
        Collection<Unit> unExceptionalSucessors = getUnexceptionalSuccssor(currentCFG, currentStmt);

        for (Unit succ : unExceptionalSucessors) {
          Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
          if (tgts != null && tgts.contains(succ)) {
            continue;
          }
          propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, currentCxt);
        }
        //Do propagation for exceptional successors
        if (true) {
          Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = getExceptionalDest(currentCFG, currentStmt);
          for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
            ThrowableSet thSet = curDst.getThrowables();
            Unit exSucc = curDst.getHandlerNode();
            if (exSucc == null) {
              continue;
            }
            Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
            boolean ignore = true;
            for (RefType curRefType : exceptionTypes) {
              if (bDebug)
                Logger.verb(mtdTag, "For STMT:" + currentStmt + "Exception Types:" + curRefType);
              if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)) {
                ignore = false;
              }
            }
            if (!ignore) {
              propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) exSucc, currentCxt);
            }
          }
        }
      }
      // case 2: currentStmt is a call but not a call to
      // startActivity/showDialog/etc.
      else if (currentStmt.containsInvokeExpr()) {
        Set<AndroidCallGraph.Edge> outgoings = cg.getEdge(currentStmt);
        Set<SootMethod> infeasibleCallees = infeasibleCalls.get(currentStmt);
        boolean findTarget = false;
        for (AndroidCallGraph.Edge outgoing : outgoings) {
          SootMethod target = outgoing.target;
          if (infeasibleCallees.contains(target)) {
            // we need to ignore analyzing callee
            continue;
          }
          if (target.getDeclaringClass().isApplicationClass()
                  && target.isConcrete()) {
            // Process flow at call
            executionContext.putInvokeParam(currentStmt, target);

            findTarget = true;
            UnitGraph tgtCFG = createOrGetCFG(methodToCFG, target);
            for (Unit entryNode : tgtCFG.getHeads()) {
              propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) entryNode, target);
            }
            if (visitedMethods.contains(target)) {
              //Do propagation of un-exceptional succ
              Collection<Unit> unException = Lists.newArrayList(currentCFG.getUnexceptionalSuccsOf(currentStmt));
              for (Unit succ : unException) {
                Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
                if (tgts != null && tgts.contains(succ)) {
                  continue;
                }
                propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, currentCxt);
              }
              //Do propagation of exceptional succ
              if (true) {
                Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = Lists.newArrayList(currentCFG.getExceptionDests(currentStmt));
                for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
                  ThrowableSet thSet = curDst.getThrowables();
                  Unit exSucc = curDst.getHandlerNode();
                  if (exSucc == null) {
                    continue;
                  }
                  Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
                  boolean ignore = true;
                  for (RefType curRefType : exceptionTypes) {
                    if (bDebug)
                      Logger.verb(mtdTag, "For STMT:" + currentStmt + "Exception Types:" + curRefType);
                    if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)) {
                      ignore = false;
                    }
                  }
                  if (!ignore) {
                    propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) exSucc, currentCxt);
                  }
                }
              }
            }
          }
        }
        // if the target can not be found, then we conservatively think there is
        // no transition
        if (!findTarget) {
          //Do propagation for unexception successors
          Collection<Unit> unException = Lists.newArrayList(currentCFG.getUnexceptionalSuccsOf(currentStmt));
          for (Unit succ : unException) {
            Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
            if (tgts != null && tgts.contains(succ)) {
              continue;
            }
            propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, currentCxt);
          }
          //Do propagation for exceptional successors
          if (true) {
            Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = Lists.newArrayList(currentCFG.getExceptionDests(currentStmt));
            for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
              ThrowableSet thSet = curDst.getThrowables();
              Unit exSucc = curDst.getHandlerNode();
              if (exSucc == null) {
                continue;
              }
              Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
              boolean ignore = true;
              for (RefType curRefType : exceptionTypes) {
                if (bDebug)
                  Logger.verb(mtdTag, "For STMT:" + currentStmt + "Exception Types:" + curRefType);
                if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)) {
                  ignore = false;
                }
              }
              if (!ignore) {
                propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) exSucc, currentCxt);
              }
            }
          }
        }
      }
      // case 3: currentStmt is the exit point and callingContext is not in
      // visitedMethods
      else if (currentCFG.getTails().contains(currentStmt)
              && !visitedMethods.contains(currentCxt)) {
        visitedMethods.add(currentCxt);
        createOrGetCFG(methodToCFG, currentCxt);
        Set<AndroidCallGraph.Edge> incomings = cg.getIncomingEdges(currentCxt);
        for (AndroidCallGraph.Edge e : incomings) {
          Stmt caller = e.callSite;
          if (visitedStmts.containsKey(caller)) {
            SootMethod callerCxt = visitedStmts.get(caller);
            //UnitGraph callerCFG = createOrGetCFG(methodToCFG, callerCxt);
            ExceptionalUnitGraph callerCFG = createOrGetECFG(methodToCFG, callerCxt);
            Collection<Unit> unException = Lists.newArrayList(callerCFG.getUnexceptionalSuccsOf(caller));
            for (Unit succ : unException) {
              Set<Stmt> tgts = infeasibleEdges.get(caller);
              if (tgts != null && tgts.contains(succ)) {
                continue;
              }
              propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, callerCxt);
            }
            //Do propagation for exceptional successors
            if (true) {
              Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = Lists.newArrayList(callerCFG.getExceptionDests(caller));
              for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
                ThrowableSet thSet = curDst.getThrowables();
                Unit exSucc = curDst.getHandlerNode();
                if (exSucc == null) {
                  continue;
                }
                Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
                boolean ignore = true;
                for (RefType curRefType : exceptionTypes) {
                  if (bDebug)
                    Logger.trace(mtdTag, "For STMT:" + currentStmt + "Exception Types:" + curRefType);
                  if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)) {
                    ignore = false;
                  }
                }
                if (!ignore) {
                  propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) exSucc, currentCxt);
                }
              }
            }
          }
        }
      }
    }
    return unexpected;
  }

  /**
   * Full traversal, but bypass several exception handler
   * Does not process null pointer check at if.
   * @param handler
   * @param visitedStmts
   * @param visitedSeq
   * @param escapedStmts
   * @param methodToCFG
   * @param filter
   * @param infeasibleEdges
   * @param infeasibleCalls
   * @return
   */
  public boolean forwardTraversalMod(
          SootMethod handler,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          Set<Stmt> escapedStmts,
          Map<SootMethod, UnitGraph> methodToCFG,
          Filter<Stmt, SootMethod> filter,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {
    if (handler == null) {
      Logger.err(getClass().getSimpleName(), "can not perform forward traversal since the handler is null");
    }
    List<Stmt> workingList = Lists.newArrayList();
    UnitGraph handlerCFG = createOrGetCFG(methodToCFG, handler);
    for (Unit entryNode : handlerCFG.getHeads()) {
      propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) entryNode, handler);
    }
    return traverseMod(workingList, visitedStmts, visitedSeq, escapedStmts, methodToCFG,
            filter, infeasibleEdges, infeasibleCalls);
//    return traverseWithIfFix(workingList, visitedStmts, visitedSeq, escapedStmts, methodToCFG,
//            filter, infeasibleEdges, infeasibleCalls);
  }

  /**
   * Full traversal, but bypass several exception handler
   * Process null pointer and context check at if.
   * @param handler
   * @param visitedStmts
   * @param visitedSeq
   * @param escapedStmts
   * @param methodToCFG
   * @param filter
   * @param infeasibleEdges
   * @param infeasibleCalls
   * @return
   */
  public boolean forwardTraversalIfContext(
          SootMethod handler,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          Set<Stmt> escapedStmts,
          Map<SootMethod, UnitGraph> methodToCFG,
          Filter<Stmt, SootMethod> filter,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {
    if (handler == null) {
      Logger.err(getClass().getSimpleName(), "can not perform forward traversal since the handler is null");
    }
    List<Stmt> workingList = Lists.newArrayList();
    UnitGraph handlerCFG = createOrGetCFG(methodToCFG, handler);
    for (Unit entryNode : handlerCFG.getHeads()) {
      propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) entryNode, handler);
    }
//    return traverseMod(workingList, visitedStmts, visitedSeq, escapedStmts, methodToCFG,
//            filter, infeasibleEdges, infeasibleCalls);
    return traverseWithIfFix(workingList, visitedStmts, visitedSeq, escapedStmts, methodToCFG,
            filter, infeasibleEdges, infeasibleCalls);
  }

  /**
   * A modification of original traverse method. Add support to
   * bypass several exception handler.
   * @param workingList
   * @param visitedStmts
   * @param visitedSeq
   * @param escapedStmts
   * @param methodToCFG
   * @param filter
   * @param infeasibleEdges
   * @param infeasibleCalls
   * @return
   */
  private boolean traverseMod(
          List<Stmt> workingList,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          Set<Stmt> escapedStmts,
          Map<SootMethod, UnitGraph> methodToCFG,
          Filter<Stmt, SootMethod> filter,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {
    final String mtdTag = "TRVMOD";
    final boolean bDebug = false;
    boolean unexpected = false;
    Set<SootMethod> visitedMethods = Sets.newHashSet();
    Context executionContext = new ConstantValContext();

    while (!workingList.isEmpty()) {
      Stmt currentStmt = workingList.remove(0);
      SootMethod currentCxt = visitedStmts.get(currentStmt);
      if (currentCxt == null) {
        Logger.err(getClass().getSimpleName(), "can not find the calling context for stmt: "
                + currentStmt);
      }
      if (wtgUtil.isIgnoredMethod(currentCxt)) {
        continue;
      }
      if (filter.match(currentStmt, currentCxt)) {

        if (escapedStmts != null) {
          escapedStmts.add(currentStmt);
        }
        continue;
      }
      ExceptionalUnitGraph currentCFG = createOrGetECFG(methodToCFG, currentCxt);

      //For context sensitive analysis
      if (currentStmt instanceof DefinitionStmt) {
        //Do sth with data flow.
        SootMethod md = visitedStmts.get(currentStmt);
        if (md != null) {
          executionContext.processDefinitionStmt((DefinitionStmt)currentStmt);
        }
      }

      // switch case for 4 conditions
      // case 1: currentStmt is not a call and not exit of cfg
      if (!currentStmt.containsInvokeExpr()
              && !currentCFG.getTails().contains(currentStmt)) {
        //Do propagation for un-exceptional successors
        Collection<Unit> unExceptionalSucessors = currentCFG.getUnexceptionalSuccsOf(currentStmt);
        //Collection<Unit> success = currentCFG.getSuccsOf(currentStmt);
        for (Unit succ : unExceptionalSucessors) {
          Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
          if (tgts != null && tgts.contains(succ)) {
            continue;
          }
          propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, currentCxt);
        }
        //Do propagation for exceptional successors, if this exception types should not ignored
        Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = currentCFG.getExceptionDests(currentStmt);
        for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
          ThrowableSet thSet = curDst.getThrowables();
          Unit exSucc = curDst.getHandlerNode();
          if (exSucc == null){
            continue;
          }
          Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
          boolean ignore = true;
          for (RefType curRefType : exceptionTypes) {
            if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)){
              ignore = false;
            }
          }
          if (!ignore) {
            propagateMod(visitedStmts, workingList, visitedSeq, (Stmt)exSucc, currentCxt);
          }
        }
      }
      // case 2: currentStmt is a call but not a call to
      // startActivity/showDialog/etc.
      else if (currentStmt.containsInvokeExpr()) {
        Set<AndroidCallGraph.Edge> outgoings = cg.getEdge(currentStmt);
        Set<SootMethod> infeasibleCallees = infeasibleCalls.get(currentStmt);
        boolean findTarget = false;
        for (AndroidCallGraph.Edge outgoing : outgoings) {
          SootMethod target = outgoing.target;
          if (infeasibleCallees.contains(target)) {
            // we need to ignore analyzing callee
            continue;
          }
          if (target.getDeclaringClass().isApplicationClass()
                  && target.isConcrete()) {
            findTarget = true;
            UnitGraph tgtCFG = createOrGetCFG(methodToCFG, target);
            if (!visitedMethods.contains(target)) {
              //process context information
              InvokeExpr ie = currentStmt.getInvokeExpr();
              executionContext.putInvokeParam(currentStmt, target);

            }
            for (Unit entryNode : tgtCFG.getHeads()) {
              propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) entryNode, target);
            }
            if (visitedMethods.contains(target)) {
              //Do propagation of un-exceptional succ
              Collection<Unit> unException = currentCFG.getUnexceptionalSuccsOf(currentStmt);
              for (Unit succ : unException) {
                Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
                if (tgts != null && tgts.contains(succ)) {
                  continue;
                }
                propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, currentCxt);
              }
              //Do propagation of exceptional succ
              Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = currentCFG.getExceptionDests(currentStmt);
              for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
                ThrowableSet thSet = curDst.getThrowables();
                Unit exSucc = curDst.getHandlerNode();
                if (exSucc == null){
                  continue;
                }
                Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
                boolean ignore = true;
                for (RefType curRefType : exceptionTypes) {
                  //Logger.verb(mtdTag, "For STMT:" + currentStmt + "Exception Types:" + curRefType);
                  if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)){
                    ignore = false;
                  }
                }
                if (!ignore) {
                  propagateMod(visitedStmts, workingList, visitedSeq, (Stmt)exSucc, currentCxt);
                }
              }
            }
          }
        }
        // if the target can not be found, then we conservatively think there is
        // no transition
        if (!findTarget) {
          //Do propagation for unexception successors
          Collection<Unit> unException = currentCFG.getUnexceptionalSuccsOf(currentStmt);
          for (Unit succ : unException) {
            Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
            if (tgts != null && tgts.contains(succ)) {
              continue;
            }
            propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, currentCxt);
          }
          //Do propagation for exceptional successors
          Collection<ExceptionalUnitGraph.ExceptionDest> exceptDest = currentCFG.getExceptionDests(currentStmt);
          for (ExceptionalUnitGraph.ExceptionDest curDst : exceptDest) {
            ThrowableSet thSet = curDst.getThrowables();
            Unit exSucc = curDst.getHandlerNode();
            if (exSucc == null){
              continue;
            }
            Set<RefType> exceptionTypes = retriveExceptionSet(thSet);
            boolean ignore = true;
            for (RefType curRefType : exceptionTypes) {
              //Logger.verb(mtdTag, "For STMT:" + currentStmt + "Exception Types:" + curRefType);
              if (!IfNullUtil.ExceptionTypes.v().isIgnoredException(curRefType)){
                ignore = false;
              }
            }
            if (!ignore) {
              propagateMod(visitedStmts, workingList, visitedSeq, (Stmt)exSucc, currentCxt);
            }
          }
        }
      }
      // case 3: currentStmt is the exit point and callingContext is not in
      // visitedMethods
      else if (currentCFG.getTails().contains(currentStmt)
              && !visitedMethods.contains(currentCxt)) {
        visitedMethods.add(currentCxt);
        createOrGetCFG(methodToCFG, currentCxt);
        Set<AndroidCallGraph.Edge> incomings = cg.getIncomingEdges(currentCxt);
        for (AndroidCallGraph.Edge e : incomings) {
          Stmt caller = e.callSite;
          if (visitedStmts.containsKey(caller)) {
            SootMethod callerCxt = visitedStmts.get(caller);
            UnitGraph callerCFG = createOrGetCFG(methodToCFG, callerCxt);
            for (Unit succ : callerCFG.getSuccsOf(caller)) {
              Set<Stmt> tgts = infeasibleEdges.get(caller);
              if (tgts != null && tgts.contains(succ)) {
                continue;
              }
              propagateMod(visitedStmts, workingList, visitedSeq, (Stmt) succ, callerCxt);
            }
          }
        }
      }
    }
    return unexpected;
  }

  public boolean reverseTraversal(
          SootMethod handler,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          Set<Stmt> escapedStmts,
          Map<SootMethod, UnitGraph> methodToCFG,
          Filter<Stmt, SootMethod> filter,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {
    if (handler == null) {
      Logger.err("REVERSETRV", "Can not perform reverse traversal since the handler is null");
    }
    List<Stmt> workingList = Lists.newArrayList();
    UnitGraph handlerCFG = createOrGetCFG(methodToCFG, handler);

    for (Unit exitNode : handlerCFG.getTails()){
      propagate(visitedStmts, workingList, visitedSeq, (Stmt) exitNode, handler);
    }

    return reverseTraverse(workingList, visitedStmts, visitedSeq, escapedStmts, methodToCFG,
            filter, infeasibleEdges, infeasibleCalls);
  }


  private boolean reverseTraverse(
          List<Stmt> workingList,
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> visitedSeq,
          Set<Stmt> escapedStmts,
          Map<SootMethod, UnitGraph> methodToCFG,
          Filter<Stmt, SootMethod> filter,
          HashMultimap<Stmt, Stmt> infeasibleEdges,
          HashMultimap<Stmt, SootMethod> infeasibleCalls) {
    boolean unexpected = false;
    Set<SootMethod> visitedMethods = Sets.newHashSet();
    final String mtdTag = "RVSTRV";

    while (!workingList.isEmpty()) {
      //dumpWorkList(workingList);
      Stmt currentStmt = workingList.remove(0);
      SootMethod currentCxt = visitedStmts.get(currentStmt);
      if (currentCxt == null) {
        Logger.err(getClass().getSimpleName(), "can not find the calling context for stmt: "
                + currentStmt);
      }
      if (wtgUtil.isIgnoredMethod(currentCxt)) {
        continue;
      }
      if (filter.match(currentStmt, currentCxt)) {
        if (escapedStmts != null) {
          escapedStmts.add(currentStmt);
        }
        continue;
      }
      UnitGraph currentCFG = createOrGetCFG(methodToCFG, currentCxt);
      // switch case for 3 conditions
      // case 1: currentStmt is not a call and not exit of cfg
      if (!currentStmt.containsInvokeExpr()
              && !currentCFG.getHeads().contains(currentStmt)) {
        Collection<Unit> predecessors = currentCFG.getPredsOf(currentStmt);
        for (Unit pred : predecessors){
          Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
          if (tgts != null && tgts.contains(pred))
            continue;
          propagate(visitedStmts, workingList, visitedSeq, (Stmt) pred, currentCxt);
        }
      }
      // case 2: currentStmt is a call but not a call to
      // startActivity/showDialog/etc.
      else if (currentStmt.containsInvokeExpr()) {
        Set<AndroidCallGraph.Edge> outgoings = cg.getEdge(currentStmt);
        Set<SootMethod> infeasibleCallees = infeasibleCalls.get(currentStmt);
        boolean findTarget = false;
        for (AndroidCallGraph.Edge outgoing : outgoings) {
          SootMethod target = outgoing.target;
          if (infeasibleCallees.contains(target)) {
            // we need to ignore analyzing callee
            continue;
          }
          if (target.getDeclaringClass().isApplicationClass()
                  && target.isConcrete()) {
            findTarget = true;
            UnitGraph tgtCFG = createOrGetCFG(methodToCFG, target);
            for (Unit entryNode : tgtCFG.getTails()) {
              propagate(visitedStmts, visitedSeq, workingList, (Stmt) entryNode, target);
            }
            if (visitedMethods.contains(target)) {
              for (Unit pred: currentCFG.getPredsOf(currentStmt)){
                Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
                if (tgts != null && tgts.contains(pred))
                  continue;
                propagate(visitedStmts, visitedSeq, workingList, (Stmt) pred, currentCxt);
              }
            }
          }
        }
        // if the target can not be found, then we conservatively think there is
        // no transition
        if (!findTarget) {
          for (Unit pred: currentCFG.getPredsOf(currentStmt)){
            Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
            if (tgts != null && tgts.contains(pred))
              continue;
            propagate(visitedStmts, visitedSeq, workingList, (Stmt) pred, currentCxt);
          }
        }
      } // end of else if
      // case 3: currentStmt is the exit point and callingContext is not in
      // visitedMethods
      else if (currentCFG.getHeads().contains(currentStmt)
              && !visitedMethods.contains(currentCxt)){
        visitedMethods.add(currentCxt);
        createOrGetCFG(methodToCFG, currentCxt);
        Set<AndroidCallGraph.Edge> incomings = cg.getIncomingEdges(currentCxt);
        for (AndroidCallGraph.Edge e : incomings) {
          Stmt caller = e.callSite;
          if (visitedStmts.containsKey(caller)) {
            SootMethod callerCxt = visitedStmts.get(caller);
            UnitGraph callerCFG = createOrGetCFG(methodToCFG, callerCxt);
            for (Unit pred : callerCFG.getPredsOf(caller)) {
              Set<Stmt> tgts = infeasibleEdges.get(currentStmt);
              if (tgts != null && tgts.contains(pred))
                continue;
              propagate(visitedStmts, visitedSeq, workingList, (Stmt) pred, callerCxt);
            }
          }
        }
      }// End of else if
    }
    return unexpected;
  }

  private void propagate(
          Map<Stmt, SootMethod> visitedStmts,
          List<Stmt> workingList,
          List<Stmt> visitedSeq,
          Stmt s,
          SootMethod cxt) {
    if (!visitedStmts.containsKey(s)) {
      visitedStmts.put(s, cxt);
      workingList.add(s);
      visitedSeq.add(s);
    }
  }

  private Set<RefType> retriveExceptionSet(ThrowableSet t){

    Field exceptionField = null;
    try {
      exceptionField = t.getClass().getDeclaredField("exceptionsIncluded");
    }
    catch (NoSuchFieldException e){
      return null;
    }

    exceptionField.setAccessible(true);
    Set ret = null;
    try {
      ret = (Set)exceptionField.get(t);
    }
    catch (IllegalAccessException e) {
      return null;
    }

    Set<RefType> retD = Sets.newHashSet();
    for (Object o :ret){
      if (o instanceof  RefType) {
        retD.add((RefType) o);
      }
    }
    return retD;
  }



}
