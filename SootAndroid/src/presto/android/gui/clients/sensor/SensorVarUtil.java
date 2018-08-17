package presto.android.gui.clients.sensor;

import com.beust.jcommander.internal.Sets;
import com.google.common.collect.HashMultimap;
import com.google.common.collect.Maps;
import presto.android.gui.Flowgraph;
import presto.android.gui.GUIAnalysisOutput;
import presto.android.gui.wtg.WTGAnalysisOutput;
import presto.android.gui.wtg.analyzer.ConstantAnalysis;
import presto.android.gui.wtg.ds.WTG;
import presto.android.gui.wtg.ds.WTGEdge;
import soot.jimple.Stmt;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * Created by zero on 2/14/17.
 */
public class SensorVarUtil {

  public static int K;

  public static WTGAnalysisOutput wtgOutput;

  public static WTG wtg;

  public static GUIAnalysisOutput guiOutput;

  public static ConstantAnalysis constantAnalysis = null;

  public static HashMultimap<Stmt, SensorResNode> stmtResNodeMap = HashMultimap.create();

  public static int P1Mark2Measurement = 0;

  public static int P2Mark2Measurement = 0;

  public static int P1Mark3Measurement = 0;

  public static int P2Mark3Measurement = 0;

  public static int P1CandidateCount = 0;

  public static int P2CandidateCount = 0;

  public static int P1UniqueCount = 0;

  public static int P2UniqueCount = 0;

  public static Set<WTGEdge> duplicatedAndInfeasibleEdge = new HashSet<>();

  public static Set<String> declaredActivities = Sets.newHashSet();

  public static SensorRegistrationAnalyzer analyzer;

  public static Flowgraph flowgraph;

}
