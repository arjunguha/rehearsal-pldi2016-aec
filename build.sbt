scalaVersion := "2.11.4"

scalacOptions ++=
 Seq("-deprecation",
     "-unchecked",
     "-feature",
     "-Xfatal-warnings")

libraryDependencies ++=
  Seq("org.scalatest" % "scalatest_2.11" % "2.2.1" % "test")
