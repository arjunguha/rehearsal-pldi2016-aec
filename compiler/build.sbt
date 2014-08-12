name := "puppet-parser"

version := "0.1"

scalaVersion := "2.10.3"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

resolvers ++= Seq(
  "scala-docker" at "https://oss.sonatype.org/content/repositories/snapshots/",
  "Typesafe Repository" at "http://repo.akka.io/snapshots/"
)


libraryDependencies ++= {
  val akkaV = "2.3.4"
  val graphMajorV = "1.9"
  Seq(
    "org.scalatest" % "scalatest_2.10" % "2.1.3" % "test",
    "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
    "com.assembla.scala-incubator" %% "graph-core" % s"${graphMajorV}.0",
    "com.assembla.scala-incubator" %% "graph-json" % s"${graphMajorV}.2",
    "com.assembla.scala-incubator" %% "graph-dot"  % s"${graphMajorV}.0",
    "edu.umass.cs" %% "docker" % "0.2",
    "com.typesafe.akka" %% "akka-actor"  % akkaV,
    "com.typesafe.akka" %% "akka-kernel" % akkaV,
    "com.typesafe.akka" %% "akka-remote" % akkaV
  )
}

parallelExecution in Test := false
