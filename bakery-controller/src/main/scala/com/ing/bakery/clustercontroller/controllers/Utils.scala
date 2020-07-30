package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import cats.data.{NonEmptyList, Validated, ValidatedNel}
import cats.effect.{IO, Timer}
import com.ing.bakery.clustercontroller.MutualAuthKeystoreConfig
import com.ing.bakery.clustercontroller.controllers.BakerResource.SidecarSpec
import skuber.{ConfigMap, Container, Resource}

import scala.concurrent.duration._
import scala.util.Try


object Utils {

  implicit class ConfigurableContainer(container: Container) {
    def withMaybeInteractionTLSEnvironmentVariables(interactionClientTLS: Option[MutualAuthKeystoreConfig]): Container = interactionClientTLS map { tls =>
      container
        .setEnvVar("INTERACTION_CLIENT_HTTPS_ENABLED", "true")
        .setEnvVar("INTERACTION_CLIENT_HTTPS_KEYSTORE_PATH", "/bakery-config/" + tls.fileName)
        .setEnvVar("INTERACTION_CLIENT_HTTPS_KEYSTORE_PASSWORD", tls.password)
        .setEnvVar("INTERACTION_CLIENT_HTTPS_KEYSTORE_TYPE", tls._type)
    } getOrElse
      container
        .setEnvVar("INTERACTION_CLIENT_HTTPS_ENABLED", "false")

    def withMaybeLimitMemory(qty: Option[Resource.Quantity]): Container = qty.map(container.limitMemory).getOrElse(container)
    def withMaybeLimitCpu(qty: Option[Resource.Quantity]): Container = qty.map(container.limitCPU).getOrElse(container)
    def withMaybeRequestMemory(qty: Option[Resource.Quantity]): Container = qty.map(container.requestMemory).getOrElse(container)
    def withMaybeRequestCpu(qty: Option[Resource.Quantity]): Container = qty.map(container.requestCPU).getOrElse(container)

    def withMaybeResources(resources: Option[Resource.Requirements]): Container = resources.map(r =>
      container
        .withMaybeLimitMemory(r.limits.get("memory"))
        .withMaybeLimitCpu(r.limits.get("cpu"))
        .withMaybeRequestMemory(r.requests.get("memory"))
        .withMaybeRequestCpu(r.requests.get("cpu"))).getOrElse(container)

    def withMaybeKafkaSink(kafkaBootstrapServers: Option[String]): Container = kafkaBootstrapServers.map(servers =>
      container
        .setEnvVar("KAFKA_EVENT_SINK_BOOTSTRAP_SERVERS", servers)  // todo add missing kafka configuration later (topics + identity/tls)
        .setEnvVar("KAFKA_EVENT_SINK_ENABLED", "true")
    ).getOrElse(container.setEnvVar("KAFKA_EVENT_SINK_ENABLED", "false"))
  }

  /** Tries every second f until it succeeds or until 20 attempts have been made. */
  def eventually[A](f: IO[A])(implicit timer: Timer[IO]): IO[A] =
    within(60.seconds, 24)(f)

  /** Retries the argument f until it succeeds or time/split attempts have been made,
    * there exists a delay of time for each retry.
    */
  def within[A](time: FiniteDuration, split: Int)(f: IO[A])(implicit timer: Timer[IO]): IO[A] = {
    def inner(count: Int, times: FiniteDuration): IO[A] = {
      if (count < 1) f else f.attempt.flatMap {
        case Left(_) => IO.sleep(times) *> inner(count - 1, times)
        case Right(a) => IO(a)
      }
    }

    inner(split, time / split)
  }

  type FromConfigMapValidation[+A] = ValidatedNel[String, A]

  def extractValidatedString(configMap: ConfigMap, path: String): FromConfigMapValidation[String] =
    configMap.data.get(path).fold(s"required path '$path' not found in ConfigMap '${configMap.name}'".invalidNel[String])(_.validNel)

  def extractValidatedStringOption(configMap: ConfigMap, path: String): FromConfigMapValidation[Option[String]] =
    configMap.data.get(path).map(Some(_).validNel).getOrElse(None.validNel)

  def extractListValidated(configMap: ConfigMap, path: String): FromConfigMapValidation[List[String]] = {
    val ArrayReg = s"^${path.replace(".", "\\.")}\\.(\\d+)$$".r
    val elements = configMap.data.toList.mapFilter {
      case (ArrayReg(index), value) =>  Some(index.toInt -> value)
      case _ => None
    }.sortBy(_._1).map(_._2)
    if(elements.isEmpty) s"no element of array '$path' found in ConfigMap '${configMap.name}''".invalidNel[List[String]] else elements.validNel
  }

  def optional[A](fromConfigMapValidation: FromConfigMapValidation[A]): FromConfigMapValidation[Option[A]] =
    fromConfigMapValidation.map(Some(_)).orElse(None.validNel)

  def extractListWithSubPaths(configMap: ConfigMap, path: String): FromConfigMapValidation[List[ConfigMap]] = {
    val ArrayReg = s"^${path.replace(".", "\\.")}\\.(\\d+)\\.(.+)$$".r
    val elements = configMap.data.toList.mapFilter {
      case (ArrayReg(index, subpath), value) =>  Some(index.toInt -> (subpath, value))
      case _ => None
    }
      .groupBy(_._1)
      .values.toList
      .map(_.map(_._2))
      .map(subpaths => configMap.copy(data = subpaths.toMap))
    if(elements.isEmpty) s"no element of array '$path' found in ConfigMap '${configMap.name}''".invalidNel[List[ConfigMap]] else elements.validNel
  }

  def extractAndParseValidated[A](configMap: ConfigMap, path: String, parse: String => Try[A]): FromConfigMapValidation[A] =
    extractValidatedString(configMap, path).andThen(raw => parseValidated(parse(raw), path))

  def parseValidated[A](t: Try[A], fromPath: String): FromConfigMapValidation[A] =
    Validated.fromTry(t).leftMap(e => NonEmptyList.one(s"parsing error from path '$fromPath': ${e.getMessage}'"))

  def resourcesFromConfigMap(configMap: ConfigMap, prefix: Option[String] = None): FromConfigMapValidation[Resource.Requirements] = {
    val p = prefix.map(_ + ".").getOrElse("")
    (Utils.optional(Utils.extractValidatedString(configMap, s"${p}resources.requests.memory"))
      , Utils.optional(Utils.extractValidatedString(configMap, s"${p}resources.requests.cpu"))
      , Utils.optional(Utils.extractValidatedString(configMap, s"${p}resources.limits.memory"))
      , Utils.optional(Utils.extractValidatedString(configMap, s"${p}resources.limits.cpu"))
      ).mapN { (requestMemory, requestCpu, limitsMemory, limitsCpu) =>
      val rm = requestMemory.map(q => Map("memory" -> Resource.Quantity(q))).getOrElse(Map.empty)
      val rc = requestCpu.map(q => Map("cpu" -> Resource.Quantity(q))).getOrElse(Map.empty)
      val lm = limitsMemory.map(q => Map("memory" -> Resource.Quantity(q))).getOrElse(Map.empty)
      val lc = limitsCpu.map(q => Map("cpu" -> Resource.Quantity(q))).getOrElse(Map.empty)
      Resource.Requirements(
        requests = rm ++ rc,
        limits = lm ++ lc
      )
    }
  }

  def sidecarFromConfigMap(configMap: ConfigMap): FromConfigMapValidation[SidecarSpec] =
     ( Utils.extractValidatedString(configMap, "sidecar.image"),
      Utils.extractValidatedString(configMap, "sidecar.clusterHostSuffix"),
      Utils.extractValidatedString(configMap, "sidecar.configVolumeMountPath"),
      Utils.optional(Utils.resourcesFromConfigMap(configMap, Some("sidecar"))),
      Utils.optional(Utils.probeFromConfigMap(configMap, "sidecar.livenessProbe")),
      Utils.optional(Utils.probeFromConfigMap(configMap, "sidecar.readinessProbe"))) mapN {
      (sidecarImage, clusterHostSuffix, configVolumeMountPath, maybeResources, maybeLivenessProbe, maybeReadinessProbe) =>
        SidecarSpec(sidecarImage, maybeResources, clusterHostSuffix, configVolumeMountPath, maybeLivenessProbe, maybeReadinessProbe)
    }

  def probeFromConfigMap(configMap: ConfigMap, path: String): FromConfigMapValidation[skuber.Probe] =
    (Utils.extractValidatedString(configMap, s"$path.scheme"),
     Utils.extractValidatedString(configMap, s"$path.port"),
     Utils.extractValidatedString(configMap, s"$path.path")) mapN { (scheme, port, path) =>
      skuber.Probe(
        action = skuber.HTTPGetAction(
          port = Right(port),
          path = path,
          schema = scheme
        ),
        initialDelaySeconds = 15,
        timeoutSeconds = 10
      )
  }
}
