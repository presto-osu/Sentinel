import subprocess, os, tempfile, shutil, sys
import xml.etree.ElementTree as ET

XML_NS = {'android':'http://schemas.android.com/apk/res/android'}

class GlobalConfigs:
    def __init__(self):
      self.APK_NAME=""
      self.ADK_ROOT=""
      self.ZIPALIGN_PATH = '/build-tools/27.0.0/zipalign'
      self.APKSIGNER_PATH = '/build-tools/27.0.0/apksigner'
      self.KEYSTORE_PATH = ""
      self.APKTOOL_PATH=""
      self.OUTPUT_PATH=""
      self.KEEP_DECODE=False

def fatalError(str):
    print(str)
    sys.exit(1)
    pass

def unpackApk(apkFile, unpackDir):
  callList = ['java',\
              '-jar',\
              'apktool.jar',\
              'd', apkFile,\
              '-o', unpackDir,\
              '-f']
  ret = subprocess.call(callList, stdout = None, stderr = None)
  if ret != 0:
    fatalError("APK unpack error")  
  pass

def packApk(apkFile, unpackDir):
  callList = ['java',\
              '-jar',\
              'apktool.jar',\
              'b', unpackDir,\
              '-o', apkFile,\
              '-f']
  ret = subprocess.call(callList, stdout = None, stderr = None)
  if ret != 0:
    fatalError("APK repack error")
  pass

def signApk(apkFileUnsign, apkFileSign, configs):
  if os.access(apkFileSign, os.F_OK):
    os.remove(apkFileSign)
  callList = [configs.ZIPALIGN_PATH, \
              '-v',\
              '-p',\
              '4', \
              apkFileUnsign,\
              apkFileSign] 
  ret = subprocess.call(callList, stdout = None, stderr = None)
  if ret != 0:
    fatalError("APK zipalign error");
  shutil.move(apkFileSign, apkFileUnsign)
  callList = [configs.APKSIGNER_PATH, \
              'sign',\
              '--ks',\
              configs.KEYSTORE_PATH,\
              '--ks-pass',\
              'pass:android',\
              '--out',\
              apkFileSign,\
              apkFileUnsign]
  ret = subprocess.call(callList, stdout = None, stderr = None)
  if ret != 0:
    fatalError("APK signing failed")
  pass

def patchManifest(manifestFile):
  ET.register_namespace('android', XML_NS['android'])
  xmlTree = ET.parse(manifestFile)
  root = xmlTree.getroot()
  for applicationNode in root.iter('application'):
    #if '{' + XML_NS['android'] + '}' + 'debuggable' not in activityNode.attrib:
    applicationNode.set('{' + XML_NS['android'] + '}' + "debuggable", "true")
  for activityNode in root.iter('activity'):
    if '{' + XML_NS['android'] + '}' + 'exported' not in activityNode.attrib:
      activityNode.set('{' + XML_NS['android'] + '}' + "exported", "true")
    if '{' + XML_NS['android'] + '}' + 'permission' in activityNode.attrib:
      del activityNode.attrib['{' + XML_NS['android'] + '}' + 'permission']
  xmlTree.write(manifestFile)
  pass

def parseMainParam():
  params = sys.argv
  homeDir = os.path.expanduser('~')
  configs = GlobalConfigs()
  if 'ANDROID_HOME' in os.environ:
    configs.ADK_ROOT = os.environ['ANDROID_HOME']
  elif 'ADK' in os.environ:
    configs.ADK_ROOT = os.environ['ADK']
  configs.KEYSTORE_PATH = homeDir + "/.android/debug.keystore"
  if len(params) == 1:
    exit(-1)
  i = 0
  while i < len(params) - 1:
    i += 1
    var = params[i]
    if var == "-o" or var == "--out":
      i += 1
      configs.OUTPUT_PATH = params[i]
      continue
    if (var[-4:] == ".apk") and (configs.APK_NAME == ""):
      configs.APK_NAME = var
      continue
    pass
  if len(configs.ADK_ROOT) == 0:
    fatalError("Missing Android SDK location information")
  if len(configs.APK_NAME) == 0:
    fatalError("Missing APK location")
  if len(configs.OUTPUT_PATH) == 0:
    fatalError("Missing Output location")
  configs.ZIPALIGN_PATH = configs.ADK_ROOT + configs.ZIPALIGN_PATH
  configs.APKSIGNER_PATH = configs.ADK_ROOT + configs.APKSIGNER_PATH
  return configs


def main():
  configs = parseMainParam()
  unpackDir = tempfile.mkdtemp()
  apkDir = tempfile.mkdtemp()
  unpackApk(configs.APK_NAME, unpackDir)
  patchManifest(unpackDir + "/AndroidManifest.xml")
  packApk(apkDir + "/packedApk.apk", unpackDir)
  signApk(apkDir + "/packedApk.apk", configs.OUTPUT_PATH, configs)
  shutil.rmtree(unpackDir)
  shutil.rmtree(apkDir)
  print("Done")
  pass

if __name__ == "__main__":
  main()

