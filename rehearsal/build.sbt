name := "rehearsal"
version := "0.1"
scalaVersion := "2.11.5"
scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

resolvers ++= Seq(
  "Sonatype Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/",
  "Typesafe Repository" at "http://repo.akka.io/snapshots/",
  "PLASMA" at "https://dl.bintray.com/plasma-umass/maven"
)

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "2.2.1" % "test",
  "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
  "com.assembla.scala-incubator" %% "graph-core" % "1.9.0",
  "edu.umass.cs" %% "scala-puppet" % "0.2.3")

parallelExecution in Test := false

// Logging dependencies
libraryDependencies ++=
  Seq("com.typesafe.scala-logging" %% "scala-logging" % "3.1.0",
      "org.slf4j" % "slf4j-simple" % "1.7.12")