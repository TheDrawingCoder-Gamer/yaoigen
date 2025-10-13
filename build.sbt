ThisBuild / version := "0.1.0-SNAPSHOT"

ThisBuild / scalaVersion := "3.7.3"

lazy val yaoigen = crossProject(JVMPlatform, NativePlatform)
  .crossType(CrossType.Full)
  .in(file("yaoigen"))
  .settings(
    name := "yaoigen",
    libraryDependencies += "com.github.j-mie6" %%% "parsley" % "4.6.1",
    libraryDependencies += "org.typelevel" %%% "cats-core" % "2.13.0",
    libraryDependencies += "com.github.j-mie6" %%% "parsley-cats" % "1.5.0",
    libraryDependencies += "io.circe" %%% "circe-core" % "0.14.15",
    libraryDependencies += "io.circe" %%% "circe-generic" % "0.14.15",
    Compile / run / fork := true,
    Compile / run / baseDirectory := file("."),
    Compile / scalacOptions ++= List("-Wall", "-feature", "-deprecation"),
  ).nativeSettings(
    bspEnabled := false,
  )
