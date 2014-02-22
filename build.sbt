lazy val common  = project
                   /* .aggregate (drivers, agent, cmder) */

lazy val drivers = project.dependsOn (common)

lazy val agent   = project.dependsOn (common)

lazy val cmder   = project.dependsOn (common)


name := "cook"

version := "0.1"
