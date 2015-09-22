lazy val bdd = project

lazy val rehearsal = project.dependsOn(bdd)

lazy val  root = project.in(file("."))
  .aggregate(rehearsal)
