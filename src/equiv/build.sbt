name := "equiv"

libraryDependencies ++= Seq(
  "ch.epfl.lara" %% "scalaz3" % "2.1"
)

parallelExecution in Test := false

excludeFilter in unmanagedSources := "old_sat.scala"

/*
 * D - Show durations for each test
 * F - Show full stack traces on exception
 */
testOptions in Test += Tests.Argument("-oF")
