lazy val compiler = project.dependsOn(common)

lazy val installer = project.dependsOn(common)

lazy val common = project

lazy val master = project.in(file("verification/master"))
                         .dependsOn(common)

lazy val worker = project.in(file("verification/worker"))
                         .dependsOn(common)
