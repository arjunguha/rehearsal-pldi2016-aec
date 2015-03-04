scalaVersion := "2.11.5"

scalacOptions ++=
 Seq("-deprecation",
     "-unchecked",
     "-feature",
     "-Xfatal-warnings")

resolvers += "Arjun" at "http://dl.bintray.com/arjunguha/maven"

resolvers +=   "Sonatype Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/"

libraryDependencies ++=
  Seq("org.scalatest" % "scalatest_2.11" % "2.2.1" % "test",
      "edu.umass.cs" %% "scalaz3" % "2.1-SNAPSHOT")
