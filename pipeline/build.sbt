name := "pipeline"

parallelExecution in Test := false

libraryDependencies ++= Seq(
  "edu.umass.cs" %% "scala-puppet" % "0.2.3")

/*
 * D - Show durations for each test
 * F - Show full stack traces on exception
 */
testOptions in Test += Tests.Argument("-oDF")
