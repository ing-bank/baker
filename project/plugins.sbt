externalResolvers := Seq(
  "Flock." at "https://flock.jfrog.io/artifactory/flock-sbt/"
)

addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.2")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "1.2.0")

addSbtPlugin("com.github.sbt" % "sbt-release" % "1.1.0")

addSbtPlugin("org.scoverage" % "sbt-scoverage" % "2.0.0")

addSbtPlugin("org.xerial.sbt" % "sbt-sonatype" % "3.9.13")

addSbtPlugin("net.vonbuchholtz" % "sbt-dependency-check" % "4.1.0")

addSbtPlugin("com.jsuereth" % "sbt-pgp" % "2.1.1")

addSbtPlugin("com.typesafe.sbt" % "sbt-multi-jvm" % "0.4.0")

addSbtPlugin("com.github.sbt" % "sbt-native-packager" % "1.9.9")

addSbtPlugin("com.lightbend.sbt" % "sbt-javaagent" % "0.1.6")

addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.4.0")

addSbtPlugin("no.arktekk.sbt" % "aether-deploy" % "0.27.0")

addSbtPlugin("com.hanhuy.sbt" % "kotlin-plugin" % "2.0.1-SNAPSHOT")

libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.36"
