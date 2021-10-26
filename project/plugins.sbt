addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.2")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "1.1.0")

addSbtPlugin("com.github.gseitz" % "sbt-release" % "1.0.13")

addSbtPlugin("org.scoverage" % "sbt-scoverage" % "1.9.1")

addSbtPlugin("org.xerial.sbt" % "sbt-sonatype" % "3.9.10")

addSbtPlugin("net.vonbuchholtz" % "sbt-dependency-check" % "3.2.0")

addSbtPlugin("com.jsuereth" % "sbt-pgp" % "2.1.1")

addSbtPlugin("com.typesafe.sbt" % "sbt-multi-jvm" % "0.4.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.8.1")

addSbtPlugin("com.lightbend.sbt" % "sbt-javaagent" % "0.1.6")

addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.4.0")

addSbtPlugin("no.arktekk.sbt" % "aether-deploy" % "0.27.0")

libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.30"
