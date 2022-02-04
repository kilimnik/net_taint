The scripts in this repository were created during my thesis on analyzing the security of network communications in malware. During this we developed a taint analysis framework based on [Joern](https://joern.io/).

# Content
* the `test` folder is a small C program to test various functionalities the framework should be possible to find
* the `find.sc` is the main script file

# Execution
```bash
git clone https://github.com/kilimnik/net_taint
cd net_taint
docker build -t net_taint .
docker run -v $PWD/examples:/targets net_taint
```
