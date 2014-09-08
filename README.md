hopper
======

Refutation analysis tool for Java.

Installation
------------
Hopper requires Scala 2.10.2 or later and sbt 0.13 or later.

(1) Download [Droidel](https://github.com/cuplv/droidel) and follow the installation instructions. Publish Droidel to your local Maven repository by running `sbt publishLocal` in the droidel/ directory.   

(2) Download Z3 to hopper/lib and follow the [instructions](http://leodemoura.github.io/blog/2012/12/10/z3-for-java.html) for building the Java bindings of Z3. Copy z3/build/com.microsoft.z3.jar, libz3.dylib and libz3java.dylib (OSX) or libz3.so and libz3java.so (Linux) to hopper/lib.

(3) Build with `sbt compile` and run with `./droidel.sh`.

