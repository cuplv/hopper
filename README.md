[![Build Status](https://travis-ci.org/cuplv/hopper.svg?branch=master)](https://travis-ci.org/cuplv/hopper)

Hopper
======

Hopper is a goal-directed static analysis tool for languages that run on the JVM. It is a much-improved version and more feature-ful version of [Thresher](https://github.com/cuplv/thresher) written in Scala rather than Java.

Installation
------------
Hopper requires Scala 2.10.2 or later and sbt 0.13 or later.

(1) Download [Droidel](https://github.com/cuplv/droidel) and follow the installation instructions. Publish Droidel to your local Maven repository by running `sbt publishLocal` in the droidel/ directory.   

(2) Download Z3 to hopper/lib and follow the [instructions](http://leodemoura.github.io/blog/2012/12/10/z3-for-java.html) for building the Java bindings of Z3. Copy z3/build/com.microsoft.z3.jar, libz3.dylib and libz3java.dylib (OSX) or libz3.so and libz3java.so (Linux) to hopper/lib.

(3) Build Hopper with `sbt compile` and run with `./hopper.sh`.

Usage
-----
Run 

    ./hopper.sh -app <path_to_bytecodes> -<check>

where `<path_to_bytecodes>` is a path to a JAR or directory containing the Java bytecodes to be checked and `<check>` is one of `check_android_derefs` (check nulls for null dereferences with special handling for Android), `-check_casts` (check safety of downcasts), `-check_array_bounds` (check for out-of-bounds array accesses), `-check_nulls` (check for null dereferences), or `-check_android_leaks` (check for Android memory leaks).

The primary advantage of Hopper over Thresher is the `-jumping_execution` flag, which enables goal-directed control-flow abstraction. This flag tells Hopper to try to achieve better scalability by "jumping" between relevant code regions rather than strictly following the program's control-flow. For better precision while jumping, use the `-control_feasibility` flag.

For example, to check for null dereferences in the Android app `app.apk`, you should run `./hopper.sh -check_android_derefs -jumping_execution -control_feasibility -app app.apk`. 

About
-----
The core functionality of Hopper is an engine for *refuting* queries written in separation logic; that is, showing that no concrete execution can satisfy the query. Hopper performs a form of proof by contradiction: it starts from a query representing a bad program state (such as a null dereference or out-of-bounds array access) and works backward in an attempt to derive **false**. 

Hopper has several built-in clients (as described above) but writing your own clients is meant to be easy: just extend the `Client` class and write a checker that takes a program as input and emits separation logic formulae representing your client.

For more on Hopper and its predecessor tool Thresher, see our PLDI '13 [paper](https://www.cs.colorado.edu/~sabl4745/papers/pldi13-thresher.pdf) or the Thresher [project page](http://pl.cs.colorado.edu/projects/thresher/).

Bugs found
----------
Here is a selection of bugs found using the assistance of Hopper and its predecessor tool Thresher:

[Android framework](https://code.google.com/p/android/issues/detail?id=48055) - write into all HashMap's (fixed)
[SeriesGuide Android app](https://github.com/UweTrottmann/SeriesGuide/pull/449) - null dereference (fixed)
[SeriesGuide Android app](https://github.com/UweTrottmann/SeriesGuide/pull/450) - null dereference (fixed)
[LastFM Android app](https://github.com/lastfm/lastfm-android/pull/5) - null dereference
[ConnectBot Android app](https://github.com/connectbot/connectbot/pull/60) - null dereference
[ConnectBot Android app](https://github.com/connectbot/connectbot/pull/61) - null dereference
[K9Mail Android app](https://groups.google.com/forum/?fromgroups=#!topic/k-9-mail/JhoXL2c4UfU) - memory leak (fixed)
[Jython](https://bitbucket.org/jython/jython/pull-request/52/fixing-potential-array-index-out-of-bounds) - array out of bounds error
