name := "puppet-parser"

version := "0.1"

scalaVersion := "2.10.3"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.1.3" % "test"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"

libraryDependencies += "com.assembla.scala-incubator" %% "graph-core" % "1.8.1"
