# Sparrow ![build](https://github.com/prosyslab/sparrow-incubator/actions/workflows/build.yml/badge.svg)

Sparrow is a state-of-the-art static analyzer that aims to verify the absence
of fatal bugs in C source. Sparrow is designed based on the Abstract Interpretation 
framework and the analysis is sound in design. Sparrow adopts a number of well-founded 
static analysis techniques for scalability, precision, and user convenience.
This is the academic version of Sparrow that is different from the [commercial version](http://en.fasoo.com/sparrow).

## Install Sparrow with OPAM
The easiest way to install Sparrow is to use [OPAM](https://opam.ocaml.org).
Once you have cloned the source codes, run the build script to install the prerequisites and Sparrow:
```sh
$ git clone git@github.com:ropas/sparrow.git
$ cd sparrow
$ ./build.sh
$ eval `opam config env`
```
After that, you can directly run ```make``` or ```make install```.

Optionally, you need to set up environment variables to use machine-learning features
depending on the installation prefix.
```sh
$ export SPARROW_BIN_PATH= # PREFIX/bin
$ export SPARROW_DATA_PATH= # PREFIX/etc
```
For example, if you install Sparrow using OPAM:
```sh
$ export SPARROW_BIN_PATH=`opam config var sparrow:bin`
$ export SPARROW_DATA_PATH=`opam config var sparrow:etc`
```
## Run the analysis
You can run Sparrow for buffer overflow detection on pre-processed C files. For example:
```sh
$ ./bin/sparrow test.i
# partially flow-sensitive analysis with degree [0-100]
$ ./bin/sparrow -pfs 10 test.i
# selectively unsound analysis with bugfinder level [0-2]
$ ./bin/sparrow -bugfinder 2 test.i
```
