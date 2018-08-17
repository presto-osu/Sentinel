package presto.android.gui.clients.sensor;

import com.google.common.collect.Lists;
import com.google.common.collect.Sets;
import presto.android.gui.graph.NMenuItemInflNode;
import presto.android.gui.listener.EventType;
import presto.android.gui.wtg.EventHandler;
import presto.android.gui.wtg.StackOperation;
import presto.android.gui.wtg.ds.WTGEdge;
import presto.android.gui.wtg.ds.WTGNode;
import soot.SootMethod;

import java.util.List;
import java.util.Set;

public class EdgeSet {
  public WTGNode src;
  public WTGNode tgt;
  public WTGEdge edge;
  public EventType type;
  public List<StackOperation> stackOps;
  public Set<SootMethod> callbacks;

  public EdgeSet(WTGEdge e) {
    src = e.getSourceNode();
    tgt = e.getTargetNode();
    edge = e;
    type = e.getEventType();
    stackOps = Lists.newArrayList(e.getStackOps());
    callbacks = Sets.newHashSet();
    for (EventHandler ev : e.getCallbacks()) {
      callbacks.add(ev.getEventHandler());
    }
    callbacks.addAll(e.getEventHandlers());
  }

  @Override
  public int hashCode() {
    int ret = src.hashCode() * 1337 + tgt.hashCode();
    ret = ret * 1337 + type.hashCode();
    ret = ret * 1337 + stackOps.hashCode();
    ret = ret * 1337 + callbacks.hashCode();
    return ret;
  }

  @Override
  public boolean equals(Object e) {
    if (e instanceof EdgeSet) {
      EdgeSet o = (EdgeSet) e;
      if (this.src.equals(o.src) &&
              this.tgt.equals(o.tgt) &&
              this.type.equals(o.type) &&
              this.callbacks.equals(o.callbacks) &&
              this.stackOps.equals(o.stackOps)) {
        if (this.edge.getGUIWidget() instanceof NMenuItemInflNode &&
            (!this.edge.getGUIWidget().equals(o.edge.getGUIWidget()))) {
          return false;
        }
        return true;
      }
    }
    return false;
  }

}
