package presto.android.gui.clients.sensor;

import presto.android.gui.wtg.ds.WTGNode;

import java.util.HashSet;
import java.util.Set;

public class SensorResSet {
  public Set<SensorResNode> acquireSet;
  public Set<SensorResNode> releaseSet;
  public WTGNode node;

  public SensorResSet() {
    acquireSet = new HashSet<>();
    releaseSet = new HashSet<>();
    node = null;
  }

  @Override
  public int hashCode() {
    return acquireSet.hashCode() * 1337 + releaseSet.hashCode() + node.hashCode();
  }

  @Override
  public boolean equals(Object b) {
    if (b instanceof SensorResSet) {
      SensorResSet other = (SensorResSet) b;
      return this.acquireSet.equals(other.acquireSet) &&
              this.releaseSet.equals(other.releaseSet) &&
              this.node == other.node;
    }
    return false;
  }
}
