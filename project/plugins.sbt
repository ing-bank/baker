addSbtPlugin("com.typesafe.sbt" % "sbt-git" % "1.0.0")

addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.10")

addSbtPlugin("com.github.gseitz" % "sbt-release" % "1.0.13")

addSbtPlugin("org.scoverage" % "sbt-scoverage" % "1.6.1")

addSbtPlugin("org.xerial.sbt" % "sbt-sonatype" % "3.8.1")

addSbtPlugin("com.jsuereth" % "sbt-pgp" % "2.0.1")

addSbtPlugin("com.typesafe.sbt" % "sbt-multi-jvm" % "0.4.0")

addSbtPlugin("com.typesafe.sbt" % "sbt-native-packager" % "1.7.0")

addSbtPlugin("org.vaslabs.kube" % "sbt-kubeyml" % "0.3.4")

addSbtPlugin("no.arktekk.sbt" % "aether-deploy" % "0.23.0")

addSbtPlugin("ch.epfl.scala" % "sbt-scalafix" % "0.9.13")
libraryDependencies += "org.slf4j" % "slf4j-nop" % "1.7.30"