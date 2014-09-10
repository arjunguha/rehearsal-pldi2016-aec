import sbtassembly.Plugin.AssemblyKeys._

name := "puppet-installer"

version := "0.1"

scalaVersion := "2.10.3"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.akka.io/snapshots/"
)

libraryDependencies ++= {
  val akkaV = "2.3.4"
  Seq(
    "com.typesafe.akka" %% "akka-actor"  % akkaV,
    "com.typesafe.akka" %% "akka-kernel" % akkaV,
    "com.typesafe.akka" %% "akka-remote" % akkaV
  )
}

assemblySettings
