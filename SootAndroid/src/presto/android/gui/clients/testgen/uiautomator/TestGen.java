package presto.android.gui.clients.testgen.uiautomator;

import com.google.common.collect.Lists;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;
import presto.android.Logger;
import presto.android.gui.graph.NIdNode;
import presto.android.gui.graph.NObjectNode;
import presto.android.gui.graph.NOptionsMenuNode;
import presto.android.gui.graph.NWindowNode;
import presto.android.gui.listener.EventType;
import presto.android.gui.wtg.ds.WTGEdge;
import presto.android.gui.wtg.ds.WTGNode;
import presto.android.xml.XMLParser;
import soot.SootClass;

import java.io.*;
import java.util.List;

/***
 * This class is responsible to generate test cases for
 * paths in UI automator
 */
public class TestGen {
  private String mOutputPath;
  private String mBaseFilePath;
  private PrintWriter mOutputWriter;
  private String template = "";
  private VelocityContext mContext;
  private List<String> test_list;
  private XMLParser xmlParser;

  public TestGen(String outputPath, String baseFilePath, XMLParser parser) {
    this.mOutputPath = outputPath;
    this.mBaseFilePath = baseFilePath;
    mOutputWriter = null;
    try {
      File templateFile = new File(this.mBaseFilePath);
      if (!templateFile.exists()) {
        throw new RuntimeException("Test cases template file not found");
      }
      this.mBaseFilePath = templateFile.getAbsolutePath();
      Logger.verb("Dev", "template path: " + this.mBaseFilePath);
      FileReader fr = new FileReader(templateFile);
      BufferedReader br = new BufferedReader(fr);

      StringBuilder sb = new StringBuilder();
      String line = br.readLine();
      while (line != null) {
        sb.append(line);
        sb.append("\n");
        line = br.readLine();
      }
      br.close();
      this.template = sb.toString();
    } catch (IOException e) {
      throw new RuntimeException("I/O Exception happened when reading the" +
              " template file");

    }
    try {
      File outputFile = new File(this.mOutputPath);
      if (!outputFile.exists()) {
        outputFile.createNewFile();
      } else {
        outputFile.delete();
        outputFile.createNewFile();
      }
      this.mOutputPath = outputFile.getAbsolutePath();
      FileWriter fw = new FileWriter(outputFile);
      this.mOutputWriter = new PrintWriter(new BufferedWriter(fw));

    } catch (IOException e) {
      throw new RuntimeException("I/O Exception happened when creating" +
              " the output file");
    }
    Velocity.init();
    this.mContext = new VelocityContext();
    this.test_list = Lists.newArrayList();
    this.xmlParser = parser;
  }

  public void feedPath(List<WTGEdge> path) {
//    Logger.verb("Dev", "Generate test case for path: ");
//    for (int i = 0; i < path.size(); i++) {
//      Logger.verb("Dev", path.get(i).toString());
//    }
//    Logger.verb("Dev", "");
    String packageName = xmlParser.getAppPackageName();
    testBody body = new testBody();
    //Turn on the screen
    //body.feedStatement("d.screen.on()");
    //Record sensor state
    body.feedStatement(String.format("killApp(\"%s\")", packageName));
    body.feedStatement("time.sleep(1)");
    body.feedStatement("senset = readAssociatedSensors()");
    //Open target window
    WTGNode targetNode = path.get(0).getTargetNode();
    NWindowNode targetWindow = (NWindowNode) targetNode.getWindow();
    String activityName = targetWindow.getClassType().getName();
    String stmt = String.format("output = startActivity(\"%s\", \"%s\")",
            packageName, activityName);
    body.feedStatement(stmt);
    body.feedStatement("time.sleep(3)");
    //Initial activity opened

    for (int i = 1; i < path.size(); i++) {
      WTGEdge edge = path.get(i);
      if (!genForEdge(edge, body))
        return;
    }

    this.test_list.add(body.toString());
  }

  private boolean genForEdge(WTGEdge e, testBody body) {
    EventType et = e.getEventType();
    if (et == EventType.click || et == EventType.long_click ||
        et == EventType.select || et == EventType.touch) {
      return genForEdgeWithClickEvent(e, body);
    } else if (et == EventType.item_click || et == EventType.item_selected ||
               et == EventType.item_long_click) {
      Logger.verb("DEV", "item series EventType not supported yet");
      Logger.verb("DEV", e.toString());
      return false;
    } else if (et == EventType.implicit_home_event ||
               et == EventType.implicit_power_event ||
               et == EventType.implicit_rotate_event ||
               et == EventType.implicit_back_event ||
               et == EventType.implicit_create_context_menu) {
      return genForEdgeWithImplicitEvent(e, body);
    } else if (et == EventType.implicit_async_event ||
               et == EventType.implicit_launch_event ||
               et == EventType.implicit_lifecycle_event ||
               et == EventType.implicit_on_activity_newIntent ||
               et == EventType.implicit_on_activity_result ||
               et == EventType.implicit_hierarchy_change ||
               et == EventType.implicit_system_ui_change ||
               et == EventType.implicit_time_tick) {
      Logger.verb("DEV", "implicit series EventType are not supported yet");
      Logger.verb("DEV", e.toString());
      return false;
    } else if (et == EventType.dialog_cancel ||
               et == EventType.dialog_dismiss ||
               et == EventType.dialog_negative_button ||
               et == EventType.dialog_neutral_button ||
               et == EventType.dialog_positive_button ||
               et == EventType.dialog_press_key) {
      return genForEdgeWithDialogEvent(e, body);
    } else if (et == EventType.press_key ||
               et == EventType.scroll ||
               et == EventType.drag ||
               et == EventType.swipe ||
               et == EventType.focus_change) {
      Logger.verb("DEV", "Event Not supported yet");
      Logger.verb("DEV", e.toString());
      return false;
    } else if (et == EventType.editor_action || et == EventType.enter_text) {
      return genForEdgeWithEditorActions(e, body);
    } else if (et == EventType.zoom_in || et == EventType.zoom_out) {
      Logger.verb("DEV", "Event Not supported yet");
      Logger.verb("DEV", e.toString());
      return false;
    } else {
      Logger.verb("Dev", "Event not supported");
      Logger.verb("Dev", e.toString());
      return false;
    }
    //return false;
  }

  private boolean genForEdgeWithEditorActions(WTGEdge e, testBody body) {

    String packageName = xmlParser.getAppPackageName();
    EventType et = e.getEventType();
    NObjectNode widgetNode = e.getGUIWidget();
    NIdNode idNode = widgetNode.idNode;
    if (idNode == null) {
      Logger.verb("Dev", "ResourceId not found");
      Logger.verb("Dev", e.toString());
      return false;
    }
    String resourceId = String.format("\"%s:id/%s\"",
            xmlParser.getAppPackageName(), idNode.getIdName());
    if (et == EventType.enter_text) {
      //Generic case
      body.feedStatement(String.format(
              "d(resourceId=%s).set_text(\"TO_DO_SET_YOUR_OWN_TEXT\")", resourceId));
      body.feedStatement("d.wait.idle()");
    } else {
      Logger.verb("Dev", "Event not supported yet");
      Logger.verb("Dev", e.toString());
      return false;
    }
    return true;
  }

  private boolean genForEdgeWithImplicitEvent(WTGEdge e, testBody body) {
    EventType et = e.getEventType();
    if (et == EventType.implicit_home_event) {
      body.feedStatement("d.press.home()");
      body.feedStatement("d.wait.idle()");
      return true;
    }
    if (et == EventType.implicit_power_event) {
      body.feedStatement("d.press.power()");
      body.feedStatement("d.wait.idle()");
      return true;
    }
    if (et == EventType.implicit_back_event) {
      if (xmlParser.getAppPackageName().equals("com.drismo")) {
        // This app requires an extra touch on the target activity
        // Not modeled by WTG
        body.feedStatement("d.click(100,100)");
        body.feedStatement("d.wait.idle()");
      }
      if (xmlParser.getAppPackageName().equals("org.thecongers.mtpms")) {
        // There is a dialog opening not catched by WTG
        body.feedStatement("d(text=\"OK\").click()");
        body.feedStatement("d.wait.idle()");
      }
      body.feedStatement("d.press.back()");
      body.feedStatement("d.wait.idle()");
      return true;
    }
    if (et == EventType.implicit_rotate_event) {
      body.feedStatement("d.orientation = \"l\"");
      body.feedStatement("d.wait.idle()");
      body.feedStatement("d.orientation = \"n\"");
      body.feedStatement("d.wait.idle()");
      return true;
    }
    Logger.verb("DEV", "Event not supported yet");
    return false;
  }

  private boolean genForEdgeWithClickEvent(WTGEdge e, testBody body) {
    //Try to retrieve the resource id of the widget
    NObjectNode widgetNode = e.getGUIWidget();
    EventType et = e.getEventType();
    NIdNode idNode = widgetNode.idNode;
    String tag = "";
    if (idNode != null)
      tag = idNode.getIdName();

    String resourceId = String.format("\"%s:id/%s\"",
            xmlParser.getAppPackageName(), tag);
    // Start from Android 4, actionbar menu no longer contains IDs.
    if (xmlParser.getAppPackageName().equals("com.SecUpwN.AIMSICD") && tag.equals("toggle_cell_tracking")) {
      body.feedStatement("menuItem = d(text=\"Toggle Cell Tracking\").right()");
      body.feedStatement("if menuItem.info['checked'] == False:");
      body.incIndent();
      body.feedStatement("menuItem.click()");
      body.decIndent();
      body.feedStatement("else:");
      body.incIndent();
      body.feedStatement("d.press.back()");
      body.decIndent();
    } else if (widgetNode instanceof NOptionsMenuNode &&
        et == EventType.click) {
      // Handle Options menu here
      //Open the options menu
      body.feedStatement("d.press.menu()");
    } else if (et == EventType.click || et == EventType.select ||
        et == EventType.touch) {
      body.feedStatement(String.format(
              "d(resourceId=%s).click()", resourceId));
      if (xmlParser.getAppPackageName().equals("com.mobeezio.android.dogwhistler")) {
        body.feedStatement("time.sleep(5)");
      }
    } else if (et == EventType.long_click) {
      body.feedStatement(String.format(
              "d(resourceId=%s).long_click()", resourceId));
    } else {
      Logger.verb("Dev", "Unsupported click event");
      Logger.verb("Dev", e.toString());
      return false;
    }
    body.feedStatement("d.wait.idle()");
    return true;
  }

  private boolean genForEdgeWithDialogEvent(WTGEdge e, testBody body) {
    Logger.verb("DEV", "Event not supported yet");
    return false;
  }

  public void outputToFile() {
    if (this.test_list.isEmpty()) {
      Logger.verb("Dev", "No valid test cases generated");
      return;
    } else {
      Logger.verb("Dev", "Number of test cases: " + this.test_list.size());
    }
    this.mContext.put("test_list", this.test_list);
    this.mContext.put("count", 0);
    Velocity.evaluate(this.mContext, this.mOutputWriter, "UI Automator TestGen",this.template);
    this.mOutputWriter.flush();
    this.mOutputWriter.close();
    Logger.verb("TestGen", "UIAutomator testgen finished");
    Logger.verb("TestGen", "Testcases file location: " + this.mOutputPath);
  }

  public class testBody {
    private StringBuilder sb;
    private int indent;

    public testBody() {
      sb = new StringBuilder();
      indent = 1;
    }

    public void feedStatement(String stmt) {
      for (int i = 0; i < indent; i++)
        sb.append("  ");
      sb.append(stmt);
      sb.append("\n");
    }

    public void incIndent() {
      this.indent++;
    }

    public void decIndent() {
      this.indent--;
    }

    @Override
    public String toString() {
      return sb.toString();
    }
  }
}
