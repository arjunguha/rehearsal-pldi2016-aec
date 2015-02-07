name := "pipeline"

excludeFilter in unmanagedSources := "Tractable.scala"

parallelExecution in Test := false

/*
 * D - Show durations for each test
 * F - Show full stack traces on exception
 */
testOptions in Test += Tests.Argument("-oDF")
