lazy val common  = project
                   /* .aggregate (drivers, agent, cmder) */

lazy val drivers = project.dependsOn (common)

lazy val agent   = project.dependsOn (common, drivers) 

lazy val master  = project.dependsOn (common, drivers)


name := "cook"

version := "0.1"

resolvers ++= Seq(
  "Typesafe Repository" at "http://repo.akka.io/snapshots/"
)

libraryDependencies ++= {
  val akkaV = "2.2.3"
  Seq(
    "com.typesafe.akka" %% "akka-actor"  % akkaV,
    "com.typesafe.akka" %% "akka-kernel" % akkaV,
    "com.typesafe.akka" %% "akka-remote" % akkaV    
  )
}

