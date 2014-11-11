version in ThisBuild := "0.1"

scalaVersion in ThisBuild := "2.10.3"

scalacOptions in ThisBuild ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

resolvers in ThisBuild ++= Seq(
  "Sonatype Snapshots" at "https://oss.sonatype.org/content/repositories/snapshots/",
  "Typesafe Repository" at "http://repo.akka.io/snapshots/"
)

libraryDependencies in ThisBuild ++= Seq(
  "org.scalatest" %% "scalatest" % "2.1.3" % "test"
  )

lazy val compiler = project.dependsOn(common)

lazy val installer = project.dependsOn(common)

lazy val common = project

lazy val master = project.in(file("verification/master"))
                         .dependsOn(common)

lazy val worker = project.in(file("verification/worker"))
                         .dependsOn(common)

lazy val equiv = project.dependsOn(compiler)