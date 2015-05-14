name := "bdd"
version := "0.1"
organization := "edu.umass.cs"
scalaVersion := "2.11.5"
scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

libraryDependencies ++= Seq(
  "org.scalatest" %% "scalatest" % "2.2.1" % "test")