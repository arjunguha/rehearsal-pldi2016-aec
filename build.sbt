name := "cook"

version := "0.1"

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.akka.io/snapshots/",
  "spray repo" at "http://repo.spray.io/"
)

libraryDependencies ++= {
  val akkaV = "2.1.4"
  val sprayV = "1.1.0"
  Seq(
    "io.spray"          %  "spray-can"       % sprayV,
    "io.spray"          %  "spray-http"      % sprayV,
    "com.typesafe.akka" %% "akka-actor"      % akkaV,
    "com.typesafe.akka" %% "akka-slf4j"      % akkaV
  )
}

