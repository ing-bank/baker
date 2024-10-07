addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "2.2.0")

addSbtPlugin("com.github.sbt" % "sbt-ci-release" % "1.6.1")

addSbtPlugin("org.scoverage" % "sbt-scoverage" % "2.2.1")

addSbtPlugin("net.vonbuchholtz" % "sbt-dependency-check" % "5.1.0")

addSbtPlugin("com.github.sbt" % "sbt-multi-jvm" % "0.6.0")

addSbtPlugin("com.github.sbt" % "sbt-native-packager" % "1.10.4")

addSbtPlugin("com.github.sbt" % "sbt-javaagent" % "0.1.8")

addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.4.2")

addSbtPlugin("no.arktekk.sbt" % "aether-deploy" % "0.29.1")

addSbtPlugin("community.flock.sbt" % "sbt-kotlin-plugin" % "3.0.1")

addSbtPlugin("ch.epfl.scala" % "sbt-scalafix" % "0.12.1")

libraryDependencies += "org.slf4j" % "slf4j-nop" % "2.0.16"
