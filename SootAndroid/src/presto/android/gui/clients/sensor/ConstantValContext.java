package presto.android.gui.clients.sensor;

import com.google.common.collect.Lists;
import com.google.common.collect.Maps;
import presto.android.Logger;
import presto.android.gui.GraphUtil;
import presto.android.gui.graph.NFieldNode;
import presto.android.gui.graph.NNode;
import presto.android.gui.graph.NStringConstantNode;
import presto.android.gui.graph.NVarNode;
import soot.*;
import soot.jimple.*;

import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by zero on 3/2/17.
 */
public class ConstantValContext extends Context {

  Map<Local, NVarNode> allNVarNodes = Maps.newHashMap();

  @Override
  public void putInvokeParam(Stmt caller, SootMethod callee) {
    // Check & filter
    InvokeExpr ie = caller.getInvokeExpr();
    if (!callee.getDeclaringClass().isApplicationClass()) {
      throw new RuntimeException();
    }
    if (!callee.isConcrete()) {
      return; // could happen for native methods
    }
    // Parameter binding
    Body b = callee.retrieveActiveBody();
    Iterator<Unit> stmts = b.getUnits().iterator();
    int num_param = callee.getParameterCount();
    if (!callee.isStatic()) {
      num_param++;
    }
    Local receiverLocal = null;
    for (int i = 0; i < num_param; i++) {
      if (!stmts.hasNext()) {
        return;
      }
      Stmt s = (Stmt) stmts.next();
      Value actual;
      if (ie instanceof InstanceInvokeExpr) {
        if (i == 0) {
          receiverLocal = (Local) ((InstanceInvokeExpr)ie).getBase();
          actual = receiverLocal;
        } else {
          actual = ie.getArg(i - 1);
        }
      } else {
        //Static invoke
        actual = ie.getArg(i);
      }

      if (!(s instanceof DefinitionStmt)) {
        return;
      }

      DefinitionStmt ds = (DefinitionStmt) s;
      Local formal = (Local) ds.getLeftOp();
      Value rhs = ds.getRightOp();

      NVarNode lhsNode = createOrLookupVarNode(formal);
      NNode rhsNode = processInvocationValue(actual);
      if (rhsNode != null) {
        rhsNode.addEdgeTo(lhsNode, caller);
      }
    }
  }

  @Override
  public void processDefinitionStmt(DefinitionStmt stmt) {
    Value lhs = stmt.getLeftOp();
    Value rhs = stmt.getRightOp();
    NNode nn_lhs = processInvocationValue(lhs);
    NNode nn_rhs = processInvocationValue(rhs);
    if (nn_lhs != null && nn_rhs != null) {
      nn_rhs.addEdgeTo(nn_lhs);
    }
  }

  public NNode processInvocationValue(Value l) {
    if (l instanceof IntConstant) {
      int intValue = ((IntConstant)l).value;
      NIntConstantNode intConstantNode = new NIntConstantNode();
      intConstantNode.value = intValue;
      return intConstantNode;
    } else if (l instanceof StringConstant) {
      String stringValue = ((StringConstant)l).value;
      NStringConstantNode strConstantNode = new NStringConstantNode();
      strConstantNode.value = stringValue;
      return strConstantNode;
    } else if (l instanceof Local) {
      return createOrLookupVarNode((Local)l);
//    } else if (l instanceof FieldRef) {
//      NFieldNode x = new NFieldNode();
//      x.f = ((FieldRef)l).getField();
//      return x;
    } else if (l instanceof NewExpr || l instanceof ThisRef || l instanceof ParameterRef || l
            instanceof CastExpr || l instanceof ArrayRef) {
      return null;
    } else {
      //Logger.verb("DEBUG", "In processInvocationValue, unhandled type " + l.toString());
      return null;
    }
  }

  @Override
  public List<NNode> lookupPossibleConstantValue(Local l) {
    List<NNode> retList = Lists.newArrayList();
    NVarNode varNode = createOrLookupVarNode(l);
    GraphUtil graphUtil = GraphUtil.v();

    Set<NNode> reachedNodes = graphUtil.backwardReachableNodes(varNode);
    for (NNode curNode : reachedNodes) {
      if (curNode instanceof NIntConstantNode || curNode instanceof NStringConstantNode) {
        retList.add(curNode);
      }
    }
    return retList;
  }

  private NVarNode createOrLookupVarNode(Local l) {
    NVarNode x = allNVarNodes.get(l);
    if (x != null) {
      return x;
    }
    x = new NVarNode();
    x.l = l;
    allNVarNodes.put(l, x);
    return x;
  }
}
