package presto.android.gui.clients.sensor;

import presto.android.gui.graph.NNode;
import presto.android.gui.graph.NVarNode;
import soot.Local;
import soot.SootMethod;
import soot.Value;
import soot.jimple.Constant;
import soot.jimple.DefinitionStmt;
import soot.jimple.Stmt;

import java.util.List;

/**
 * Created by zero on 3/2/17.
 */
public abstract class Context {
  public abstract void putInvokeParam(Stmt caller, SootMethod callee);

  public abstract void processDefinitionStmt(DefinitionStmt stmt);

  public abstract List<NNode> lookupPossibleConstantValue(Local l);

}
