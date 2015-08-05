name := "parser"
version := "0.1"
organization := "edu.umass.cs"
scalaVersion := "2.11.6"
scalacOptions ++= Seq(
    "-deprecation",
      "-unchecked",
        "-feature",
          "-Xfatal-warnings"
        )

libraryDependencies += "org.scalatest" %% "scalatest" % "2.2.1" % "test"
libraryDependencies += "org.scala-lang.modules" %% "scala-parser-combinators" % "1.0.4"
