name := "worker"

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
  Seq(
    "org.scalatest" % "scalatest_2.10" % "2.1.3" % "test",
    "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
    "edu.umass.cs" %% "docker" % "0.3-SNAPSHOT",
    "com.typesafe.akka" %% "akka-actor"  % akkaV,
    "com.typesafe.akka" %% "akka-kernel" % akkaV,
    "com.typesafe.akka" %% "akka-remote" % akkaV
  )
}