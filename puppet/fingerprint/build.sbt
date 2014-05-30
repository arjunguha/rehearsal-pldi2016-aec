version := "0.1-SNAPSHOT"

scalaVersion := "2.11.0"

scalacOptions ++=
Seq("-deprecation",
    "-unchecked",
    "-feature",
    "-Xfatal-warnings")

resolvers += "spray" at "http://repo.spray.io/"

libraryDependencies += "org.apache.directory.studio" % "org.apache.commons.codec" % "1.8"

libraryDependencies ++=
  Seq("io.spray" %%  "spray-json" % "1.2.6",
      "net.databinder.dispatch" %% "dispatch-core" % "0.11.1",
      "org.scala-lang.modules" %% "scala-async" % "0.9.1",
      "org.scalatest" %% "scalatest" % "2.1.6" % "test")
