name := "puppet-parser"

version := "0.1"

scalacOptions += "-deprecation"

scalacOptions += "-unchecked"

scalacOptions += "-feature"

libraryDependencies += "org.scalatest" % "scalatest_2.10" % "2.1.3" % "test"

libraryDependencies += "org.scalacheck" %% "scalacheck" % "1.10.1" % "test"

excludeFilter in unmanagedSources := "desugar.scala"
