[![Build Status](https://travis-ci.org/cuplv/hopper.svg?branch=master)](https://travis-ci.org/cuplv/hopper)

Hopper
======

Hopper is a goal-directed static analysis tool for languages that run on the JVM. It is a much-improved and more feature-ful version of [Thresher](https://github.com/cuplv/thresher) written in Scala rather than Java.

Installation
------------
Hopper requires [sbt](http://www.scala-sbt.org/download.html) 0.1 or later.

(1) Download [Droidel](https://github.com/cuplv/droidel) and follow its installation instructions. Publish Droidel to your local Maven repository by running `sbt publishLocal` in the droidel/ directory.

(2) Download [Z3](https://github.com/Z3Prover/z3), compile the Java bindings, and copy the produced *.dylib (OSX), *.so (Linux), and *.jar files to hopper/lib:

```
mkdir lib; cd lib
git clone https://github.com/Z3Prover/z3.git; cd z3
python scripts/mk_make.py --java; cd build
make
cp *.jar ../..
cp *.dylib ../.. || cp *.so ../..
cd ../..
otool -L libz3java.dylib #this should show "libz3.dylib" with some version info behind it
install_name_tool -change libz3.dylib `pwd`/libz3.dylib libz3java.dylib
```

(3) In order to use the Android clients or compile/run the tests, you'll need a Droidel-processed Android framework JAR in lib/: `cp ../droidel/stubs/out/droidel_android-4.4.2_r1.jar lib` (assuming `droidel` and `hopper` are sibling directories).

(4) Build Hopper with `sbt one-jar` and run with `./hopper.sh`.

Usage
-----
Run 

    ./hopper.sh -app <path_to_bytecodes> -<check>

where `<path_to_bytecodes>` is a path to a JAR or directory containing the Java bytecodes to be checked and `<check>` is one of `check_android_derefs` (check nulls for null dereferences with special handling for Android), `-check_casts` (check safety of downcasts), `-check_array_bounds` (check for out-of-bounds array accesses), `-check_nulls` (check for null dereferences), or `-check_android_leaks` (check for Android memory leaks).

The primary advantage of Hopper over Thresher is the `-jumping_execution` flag, which enables goal-directed control-flow abstraction. This flag tells Hopper to try to achieve better scalability by "jumping" between relevant code regions rather than strictly following the program's control-flow. For better precision while jumping, use the `-control_feasibility` flag.

For example, to check for null dereferences in the Android app `app.apk`, you should run `./hopper.sh -check_android_derefs -jumping_execution -control_feasibility -app app.apk`. 

Tests
-----
To compile/run the regression tests, do `sbt test:compile` and then `./hopper.sh -regressions -jumping_execution`. To run a single test, you can do `./hopper.sh -regressions -test <test_name>`.

About
-----
The core functionality of Hopper is an engine for *refuting* queries written in separation logic; that is, showing that no concrete execution can satisfy the query. Hopper performs a form of proof by contradiction: it starts from a query representing a bad program state (such as a null dereference or out-of-bounds array access) and works backward in an attempt to derive **false**. 

Hopper has several built-in clients (as described above) but writing your own clients is meant to be easy: just extend the `Client` class and write a checker that takes a program as input and emits separation logic formulae representing your client.

For more on Hopper and its predecessor tool Thresher, see our OOPSLA '15 [paper](http://www.cs.colorado.edu/~bec/papers/controlfeasibility-oopsla15.pdf), our PLDI '13 [paper](http://www.cs.colorado.edu/~bec/papers/thresher-pldi13.pdf) or the Thresher [project page](http://pl.cs.colorado.edu/projects/thresher/).

Bugs found
----------
Here is a selection of bugs found using the assistance of Hopper/Thresher:

[Android framework](https://code.google.com/p/android/issues/detail?id=48055) - write into all HashMap's (fixed)

[SeriesGuide Android app](https://github.com/UweTrottmann/SeriesGuide/pull/449) - null dereference (fixed)

[SeriesGuide Android app](https://github.com/UweTrottmann/SeriesGuide/pull/450) - null dereference (fixed)

[ConnectBot Android app](https://github.com/connectbot/connectbot/pull/60) - null dereference (fixed)

[ConnectBot Android app](https://github.com/connectbot/connectbot/pull/61) - null dereference (fixed)

[LastFM Android app](https://github.com/lastfm/lastfm-android/pull/5) - null dereference

[K9Mail Android app](https://groups.google.com/forum/?fromgroups=#!topic/k-9-mail/JhoXL2c4UfU) - memory leak (fixed)

[Jython](https://bitbucket.org/jython/jython/pull-request/52/fixing-potential-array-index-out-of-bounds) - array out of bounds error

Troubleshooting
---------------
Problem: Hopper compilation fails with missing dependency from `walautil` or `droidel`.
Solution: Your `walautil` and `droidel` projects might be out of date. Try `git pull; sbt publishLocal` in each directory.

Problem: Hopper fails at runtime with a message like: `java.lang.NoSuchMethodError: scala.collection.immutable.$colon$colon.hd$1()Ljava/lang/Object;`.
Solution: This happens when Hopper is run with the wrong version of Scala; make sure you are using Scala 2.10.

Problem: Hopper fails at runtime with a message like: `java.lang.UnsupportedClassVersionError: edu/colorado/walautil/cg/ImprovedZeroXContainerCFABuilder : Unsupported major.minor version 52.0`.
Solution: This happens when Hopper and `walautil` are built using different JDK versions. You may need to rebuild `walautil` and `sbt publishLocal` again.
