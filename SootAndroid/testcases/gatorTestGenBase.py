from uiautomator import device as d
import io, time

class SensorElement:
  def __init__(self, pSensorType, pListener):
    self.sensorType = pSensorType
    self.listener = pListener

  def __eq__(self, other):
    if self.sensorType == other.sensorType and \
       self.listener == other.listener:
      return True
    return False

  def __hash__(self):
    return hash(self.sensorType) + hash(self.listener)

  def __str__(self):
    retStr = "Sensor: {0}, Listener: {1}.".format(self.sensorType,\
             self.listener)
    return retStr

def readAssociatedSensors():
  adbP = d.server.adb.cmd("shell", "dumpsys", "sensorservice")
  (output, errors) = adbP.communicate()
  output = output.decode("utf-8", "strict")
  buf = io.StringIO(output) 
  line = buf.readline()
  retSet = set()
  while len(line) != 0:
    if line[:18] == "Connection Number:":
      retSet.add(readSensorConnection(buf))
    line = buf.readline()
  return retSet
  pass

def startActivity(packageName, activityName):
  """
  Start an activity from adb.
  It uses command adb shell am start -n packageName/activityName
  to explicitly start an activity
  """
  adbP = d.server.adb.cmd("shell", "am", "start", "-n", packageName + "/" + activityName)
  (output, errors) = adbP.communicate()
  output = output.decode("utf-8", "strict")
  return output

def killApp(packageName):
  """
  Kill the application with packageName
  :param packageName: the package name of the application
  :return: none
  """
  adbP = d.server.adb.cmd("shell", "am", "force-stop", packageName)
  (output, errors) = adbP.communicate()
  output = output.decode("utf-8", "strict")
  return output

def readSensorConnection(buf):
  firstLine = buf.readline()
  if "Operating Mode:" in firstLine:
    firstLine  = buf.readline()
  secondLine = buf.readline()
  items1 = firstLine.split('|')
  listener = items1[0].strip()
  items2 = secondLine.split('|')
  sensorType = items2[0].strip()
  return SensorElement(sensorType, listener)
  pass

#foreach( ${test} in ${test_list} )
def test${count}():
  d.screen.on()
${test}
  time.sleep(1)
  senset2 = readAssociatedSensors()
  diffset = senset2 - senset
  if len(diffset) != 0:
    print("test${count} verified to leak following sensor resources:")
    for item in diffset:
      print(item)
  print("test${count} ends")
  pass

#set( $count = $count + 1 )
#end

def setUp():
#foreach( ${setup} in ${setup_list})
  ${setup}
#end
  pass

def testAll():
#set( $count = $count - 1 )
#foreach( ${id} in [0..${count}])
  test${id}();
#end
  pass

def tearDown():
#foreach( ${teardown} in ${teardown_list})
  ${teardown}
#end
  pass

def main():
  print("Device:" + d.info['productName'])
  setUp()
  testAll()
  tearDown()

if __name__ == '__main__':
  main()


