__Sentinel__ is a tool for **sen**sor **t**est**in**g to d**e**tect **l**eaks in "regular" Android apps described in the paper “Sentinel: Generating GUI Tests for Android Sensor Leaks” by Haowei Wu, Yan Wang, and Atanas Rountev, which appeared at the IEEE/ACM International Workshop on Automation of Software Test (AST'18) \[[PDF](http://web.cse.ohio-state.edu/presto/pubs/ast18.pdf)\] \[[BibTeX](http://web.cse.ohio-state.edu/presto/pubs/ast18.bib)\].
Additional details are available in Haowei Wu's Ph.D. dissertation \[[PDF](http://web.cse.ohio-state.edu/presto/pubs/wu_phd18.pdf)\] \[[BibTeX](http://web.cse.ohio-state.edu/presto/pubs/wu_phd18.bib)\].

__Update:__ We have generalized Sentinel to handle leaks in Android Wear watch faces. Using the approach introduced in FSE'18 paper "Detection of Energy Inefficiencies in Android Wear Watch Faces" ([link](https://presto-osu.github.io/fse18)) as a starting point, the release now contains a new implementation of that approach using the formalisms and techniques as the orignial Sentinel work. You can find the source code [here](https://github.com/presto-osu/Sentinel/releases/download/1.1/sentinel-wear.tar.gz). The experimental subjects are stored [elsewhere](https://zenodo.org/record/1419134/files/fse18-benchmark.tar.xz?download=1). Please follow the instructions [here](https://presto-osu.github.io/fse18/INSTALL.html#static-analysis) to run the analysis.


## Prerequisites
- Python 3
- [Python UIAutomator](https://github.com/xiaocong/uiautomator)
- Java JDK 8+
- [Apktool](https://ibotpeaches.github.io/Apktool/)
- [Ant](https://ant.apache.org)
- [Android SDK](https://developer.android.com/studio/#downloads)
- POSIX environment such as Linux/OS X/Bash for Windows
- An Android device or emulator

## Install
To download the Sentinel tool:
```bash
git clone https://github.com/presto-osu/Sentinel.git
cd Sentinel
curl -O https://github.com/presto-osu/Sentinel/releases/download/1.1/Apps.tar.gz
tar -xf Apps.tar.gz
```

To install uiautomator for Python 3:
```bash
pip3 install uiautomator
```

To build the tool:
```bash
cd SootAndroid
ant
cd ..
```

Please note Apktool version 2.3.3 is already included under `SootAndroid/apktool.jar` for your convenience, if you encounter any compatibility issues, please upgrade Apktool from the its project website.

After building this tool, please follow the instruction [here](INSTALL.md) to use this tool.

## Structure

- `Apps` includes the open-source apps we used in the evaluation of Sentinel in papers;
- `exportActivities.py` is the preprocessing script for application apk files;
- `INSTALL.md` includes the instructions to run Sentinel;
- `LICENSE` includes the copyright information;
- `README.md` is this file;
- `runSentinel.py` is the starter script of Sentinel;
- `SootAndroid` includes the implementation of Sentinel tool.


## Questions
If you have any question, please contact the authors of the paper.

