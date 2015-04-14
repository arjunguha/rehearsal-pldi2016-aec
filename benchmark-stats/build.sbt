scalaVersion := "2.11.5"

scalacOptions ++= Seq(
  "-deprecation",
  "-unchecked",
  "-feature",
  "-Xfatal-warnings"
)

resolvers ++= Seq(
  "PLASMA" at "https://dl.bintray.com/plasma-umass/maven"
)

libraryDependencies ++= {
  val graphV = "1.9.0"
  Seq(
    "org.scalatest" %% "scalatest" % "2.2.1" % "test",
    "org.scalacheck" %% "scalacheck" % "1.10.1" % "test",
    "com.assembla.scala-incubator" %% "graph-core" % graphV,
    "edu.umass.cs" %% "scala-puppet" % "0.2.2"
  )
}
