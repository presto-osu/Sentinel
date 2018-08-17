package presto.android.gui.graph;

import soot.SootMethod;
import soot.jimple.Stmt;
import soot.toolkits.scalar.Pair;

/**
 * Created by zero on 11/3/16.
 */
public class NGetSensorOpNode extends NOpNode {


  public NGetSensorOpNode(NNode idNode, NNode lhsNode,
          Pair<Stmt, SootMethod> callSite, boolean artificial) {
    super(callSite, artificial);
    //The sensor id flows to sensor object.
    idNode.addEdgeTo(this);
    //No receiver is needed
    this.addEdgeTo(lhsNode);
  }

  @Override
  public boolean hasReceiver() {
    return false;
  }

  @Override
  public boolean hasParameter() {
    return true;
  }

  @Override
  public boolean hasLhs() {
    return true;
  }

  @Override
  public NVarNode getLhs() {
    return (NVarNode) this.getSuccessor(0);
  }

  @Override
  public NNode getParameter() {
    return this.pred.get(0);
  }
}
