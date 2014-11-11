name := "equiv"

libraryDependencies ++= Seq(
  "edu.umass.cs" %% "scalaz3" % "2.1-SNAPSHOT"
)

parallelExecution in Test := false

excludeFilter in unmanagedSources := "old_sat.scala"

/*
 * D - Show durations for each test
 * F - Show full stack traces on exception
 */
testOptions in Test += Tests.Argument("-oF")
