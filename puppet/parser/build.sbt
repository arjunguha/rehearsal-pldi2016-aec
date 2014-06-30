name := "puppet-parser"

version := "0.1"

scalaVersion := "2.10.3"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

resolvers += "scala-docker" at "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies ++= Seq(
  "org.scalatest" % "scalatest_2.10" % "2.1.3" % "test",
  "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
  "com.assembla.scala-incubator" %% "graph-core" % "1.8.1",
  "com.assembla.scala-incubator" %% "graph-json" % "1.8.0",
  "edu.umass.cs" %% "docker" % "0.2-SNAPSHOT"
)
