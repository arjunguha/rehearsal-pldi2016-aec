# Build a docker container containing JRE, JVM and out puppet installer application
# VERSION 1.0

# the base image is a trusted ubuntu build with java 7 (https://index.docker.io/u/dockerfile/java/)
FROM dockerfile/java

MAINTAINER Nimish Gupta, nimish@cs.umass.edu

# we need this because the workdir is modified in dockerfile/java
WORKDIR /

# run the (java) server as the root user
USER root

# copy the locally built fat-jar to the image
ADD target/scala-2.10/puppet-installer-assembly-0.1.jar /app/puppet-installer.jar

# run the application when a container based on this image is being run
# ENTRYPOINT [ "java", "-jar", "/app/puppet-installer.jar" ]
