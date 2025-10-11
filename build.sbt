ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.3.6"

lazy val root = (project in file("."))
  .settings(
    name := "ziglin",
    libraryDependencies += "com.github.j-mie6" %% "parsley" % "4.6.1",
    libraryDependencies += "org.typelevel" %% "cats-core" % "2.13.0",
    libraryDependencies += "com.github.j-mie6" %% "parsley-cats" % "1.5.0",
    libraryDependencies += "io.circe" %% "circe-core" % "0.14.15",
    libraryDependencies += "io.circe" %% "circe-generic" % "0.14.15",
    Compile / run / fork := true,
    Compile / scalacOptions += "-Wall"
  )
