scalaVersion := "2.11.4"

scalacOptions ++=
 Seq("-deprecation",
     "-unchecked",
     "-feature",
     "-Xfatal-warnings")

resolvers += "Arjun" at "http://dl.bintray.com/arjunguha/maven"

libraryDependencies ++=
  Seq("org.scalatest" % "scalatest_2.11" % "2.2.1" % "test",
      "edu.umass.cs" %% "scalaz3-mac" % "2.1")
