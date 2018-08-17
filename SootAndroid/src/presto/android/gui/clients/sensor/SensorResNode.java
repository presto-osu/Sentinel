package presto.android.gui.clients.sensor;

import presto.android.Logger;
import presto.android.gui.clients.energy.EnergyResourceType;
import presto.android.gui.graph.NNode;
import presto.android.gui.graph.NObjectNode;
import soot.SootClass;
import soot.SootMethod;
import soot.jimple.InvokeStmt;
import soot.jimple.Stmt;

/**
 * Created by zero on 2/16/17.
 */
public class SensorResNode {
  //SensorNode
  public NNode sensorNode;
  //ListenerNode
  public NNode listenerNode;
  //Statement that request or release the resourece
  public Stmt stmt;
  //The handler/callbacks request/release the resourece
  public SootMethod handler;
  //The method contains the Stmt
  public SootMethod context;
  //GUIwidget of the WTGEdge. Currently not used.
  public NObjectNode guiWidget;

  public SensorResNode(NNode sensorNode,NNode listenerNode, Stmt stmt, SootMethod handler,
                       SootMethod context){
    this.sensorNode = sensorNode;
    this.listenerNode = listenerNode;
    this.stmt = stmt;
    this.handler = handler;
    this.context = context;
  }

  @Override
  public boolean equals(Object o1){
    if (o1 == null) {
      return false;
    }
    if (o1 instanceof SensorResNode) {
      SensorResNode rO = (SensorResNode) o1;
      if (this.sensorNode == null) {
        if (this.sensorNode == rO.sensorNode &&
                this.listenerNode.equals(rO.listenerNode) &&
                this.context.equals(rO.context) &&
                this.stmt.equals(rO.stmt) &&
                this.handler.equals(rO.handler)) {
          if (this.guiWidget == null && this.guiWidget == rO.guiWidget)
            return true;
          if (this.guiWidget != null && this.guiWidget.equals(rO.guiWidget))
            return true;
        }
      } else {
        if (this.sensorNode.equals(rO.sensorNode) &&
                this.listenerNode.equals(rO.listenerNode) &&
                this.context.equals(rO.context) &&
                this.stmt.equals(rO.stmt) &&
                this.handler.equals(rO.handler)) {
          if (this.guiWidget == null && this.guiWidget == rO.guiWidget)
            return true;
          if (this.guiWidget != null && this.guiWidget.equals(rO.guiWidget))
            return true;
        }
      }
    }
    return false;
  }

  @Override
  public int hashCode(){
    long hash = 0;
    if (this.sensorNode != null )
      hash = this.sensorNode.hashCode();
    if (this.listenerNode != null)
      hash += this.listenerNode.hashCode();
    hash += this.context.hashCode() + this.stmt.hashCode() + this.handler.hashCode();
    if (this.guiWidget != null)
      hash += this.guiWidget.hashCode();
    hash = hash * 7 % 2147483647;
    return (int)hash;
  }

  //Determine if it is a Google Maps framework/Android LocationManager
  public EnergyResourceType.resType getUnitType(){
    InvokeStmt curIvk = (InvokeStmt) stmt;
    SootClass curClz = curIvk.getInvokeExpr().getMethod().getDeclaringClass();
    SootMethod curMethod = curIvk.getInvokeExpr().getMethod();
    EnergyResourceType.resType curType = EnergyResourceType.v().classMethodTypeToResTyoe(curClz, curMethod);
    return curType;

  }

  public boolean compare(NNode sensorNode, NNode listenerNode, Stmt stmt, SootMethod handler,
                         SootMethod context) {
    final String mtdTag = "RESCMP";

    if (this.sensorNode != sensorNode)
      return false;

    if (this.listenerNode != listenerNode)
      return false;

    if (this.stmt != stmt) {
      return false;
    }

    if (this.handler != handler) {
      return false;
    }

    if (this.context != context) {
      return false;
    }

    return true;
  }

  public boolean compare(NNode listenerNode, Stmt stmt, SootMethod context) {
    final String mtdTag = "RESCMP";

    if (this.listenerNode != listenerNode)
      return false;

    if (this.stmt != stmt) {
      return false;
    }

    if (this.context != context) {
      return false;
    }

    return true;
  }



  @Override
  public String toString(){
    StringBuilder sb = new StringBuilder();
    sb.append("ObjectNode: ");
    if (this.sensorNode != null)
      sb.append(this.sensorNode);
    if (this.listenerNode != null)
      sb.append(this.listenerNode);
    sb.append(" ");
    sb.append("Stmt: ");
    sb.append(this.stmt);
    sb.append(" Context: ");
    sb.append(this.context);
    sb.append(" Handler: ");
    sb.append(this.handler);
    sb.append(" Widget: ");
    if (this.guiWidget != null)
      sb.append(this.guiWidget);
    return sb.toString();
  }

}
