package presto.android.gui.clients.exam;

import com.google.common.collect.Lists;
import presto.android.gui.clients.energy.Pair;
import presto.android.gui.graph.NNode;
import soot.SootMethod;

import java.util.List;

/**
 * Created by zero on 4/21/17.
 */
public class CallbackSequence {
  private List<Pair<SootMethod, NNode>> callbackSeq;

  public CallbackSequence() {
    callbackSeq = Lists.newArrayList();
  }

  @Override
  public int hashCode() {
    int ret = 0;
    for (Pair<SootMethod, NNode>curPair : callbackSeq) {
      ret ^= curPair.hashCode();
    }
    return ret;
  }

  @Override
  public boolean equals(Object o) {
    if (o instanceof CallbackSequence) {
      CallbackSequence other = (CallbackSequence) o;
      if (this.callbackSeq.size() != other.callbackSeq.size()) {
        return false;
      }
      for (int i = 0; i < this.callbackSeq.size(); i++) {
        if (!this.callbackSeq.get(i).equals(other.callbackSeq.get(i))) {
          return false;
        }
      }
      return true;
    }
    return false;
  }

  @Override
  public String toString() {
    StringBuilder retSB = new StringBuilder();
    for (Pair<SootMethod, NNode> curPair : callbackSeq) {
      retSB.append(curPair.getL().toString());
      retSB.append("\n");
    }
    return retSB.toString();
  }

  public List<Pair<SootMethod, NNode>> getAllPairs() {
    return this.callbackSeq;
  }

  public void addCallback(SootMethod callback, NNode object) {
    assert callback != null;
    assert object != null;
    Pair<SootMethod, NNode> curPair = new Pair(callback, object);
    this.callbackSeq.add(curPair);
  }

}