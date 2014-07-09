# Docker-Spray example
# VERSION 1.0

# the base image is a trusted ubuntu build with java 7 (https://index.docker.io/u/dockerfile/java/)
FROM dockerfile/java

# that's me!
MAINTAINER Nimish Gupta, nimish@cs.umass.edu

# we need this because the workdir is modified in dockerfile/java
WORKDIR /

# run the (java) server as the daemon user
# USER daemon

# copy the locally built fat-jar to the image
ADD target/scala-2.10/puppet-installer-assembly-0.1.jar /app/server.jar

# run the server when a container based on this image is being run
ENTRYPOINT [ "java", "-jar", "/app/server.jar" ]

# the server binds to 8140 - expose that port
#EXPOSE 8140
#EXPOSE 5001
