#!/bin/bash

JAR=target/scala-2.10/hopper_2.10-0.1-one-jar.jar
if [ ! -f $JAR ]; then
    echo "Hopper JAR not found; please run 'sbt one-jar'"
    exit 1
fi

LIB=$(pwd)/lib

export LD_LIBRARY_PATH=$LIB:$LD_LIBRARY_PATH
export DYLD_LIBRARY_PATH=$LIB:$DYLD_LIBRARY_PATH

java -Xmx8g -jar $JAR $@
