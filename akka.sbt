val AkkaToken = sys.env.get("AKKA_TOKEN") match {
  case Some(token) if token.nonEmpty => token
  case _ => throw new Exception("Environment variable AKKA_TOKEN is not set or is empty. Please set it to access the secure Akka repository.")
}

ThisBuild / resolvers += "akka-secure-mvn" at s"https://repo.akka.io/" + AkkaToken + "/secure"
ThisBuild / resolvers += Resolver.url("akka-secure-ivy", url("https://repo.akka.io/" + AkkaToken + "/secure"))(Resolver.ivyStylePatterns)

// For local development you can comment out the above lines and uncomment the lines below and replace it with your token.
//ThisBuild / resolvers += "akka-secure-mvn" at s"https://repo.akka.io/YOUR_TOKEN/secure"
//ThisBuild / resolvers += Resolver.url("akka-secure-ivy", url("https://repo.akka.io/YOUR_TOKEN/secure"))(Resolver.ivyStylePatterns)