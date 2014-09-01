# Build a docker container containing JRE, JVM and out puppet installer application
# VERSION 1.0

# the base image is a trusted ubuntu build with java 7 (https://index.docker.io/u/dockerfile/java/)
#FROM dockerfile/java
FROM ubuntu

MAINTAINER Nimish Gupta, nimish@cs.umass.edu

# we need this because the workdir is modified in dockerfile/java
# WORKDIR /

# run the (java) server as the root user
#USER root

RUN sudo apt-get -q -y update
#RUN sudo apt-get install -q -y python-software-properties
RUN sudo apt-get install -q -y software-properties-common
RUN sudo /usr/bin/add-apt-repository ppa:webupd8team/java
RUN sudo apt-get -q -y update
RUN echo debconf shared/accepted-oracle-license-v1-1 select true | sudo debconf-set-selections
RUN echo debconf shared/accepted-oracle-license-v1-1 seen true | sudo debconf-set-selections
RUN sudo apt-get install -q -y oracle-java7-installer

# copy the locally built fat-jar to the image
ADD target/scala-2.10/puppet-installer-assembly-0.1.jar /app/puppet-installer.jar

# run the application when a container based on this image is being run
# ENTRYPOINT [ "java", "-jar", "/app/puppet-installer.jar" ]
