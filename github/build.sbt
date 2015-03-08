scalaVersion := "2.10.4"

resolvers += "PLASMA" at "https://dl.bintray.com/plasma-umass/maven"

libraryDependencies ++=
  Seq("edu.umass.cs" %% "github" % "0.1",
      "com.typesafe.scala-logging" %% "scala-logging-slf4j" % "2.1.2",
      "ch.qos.logback" % "logback-classic" % "1.0.3")