package presto.android.gui.graph;

import soot.SootMethod;
import soot.jimple.Stmt;
import soot.toolkits.scalar.Pair;

/**
 * Created by zero on 11/7/16.
 */
public class NRegisterListenerOpNode extends NOpNode {

  public NRegisterListenerOpNode(NVarNode sensorNode, NNode listenerNode,
                                 Pair<Stmt, SootMethod> callSite, boolean artificial) {
    super(callSite, artificial);
    listenerNode.addEdgeTo(this);
    sensorNode.addEdgeTo(this);
  }

  @Override
  public NNode getParameter() {
    return this.pred.get(0);
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
    return false;
  }
}
