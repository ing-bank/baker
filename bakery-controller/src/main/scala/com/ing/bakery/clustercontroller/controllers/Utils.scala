package com.ing.bakery.clustercontroller.controllers

import cats.implicits._
import cats.data.{NonEmptyList, Validated, ValidatedNel}
import cats.effect.{IO, Timer}
import skuber.{ConfigMap, Container, Resource}

import scala.concurrent.duration._
import scala.util.Try

object Utils {

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

  def addResourcesSpec(container0: Container, resources0: Option[Resource.Requirements]): Container = {
    resources0.map { resources =>
      val container1 = resources.limits.get("memory").map(container0.limitMemory).getOrElse(container0)
      val container2 = resources.limits.get("cpu").map(container1.limitCPU).getOrElse(container1)
      val container3 = resources.requests.get("memory").map(container2.requestMemory).getOrElse(container2)
      val container4 = resources.requests.get("cpu").map(container3.requestCPU).getOrElse(container3)
      container4
    }.getOrElse(container0)
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

  def resourcesFromConfigMap(configMap: ConfigMap): FromConfigMapValidation[Resource.Requirements] =
    ( Utils.optional(Utils.extractValidatedString(configMap, "resources.requests.memory"))
      , Utils.optional(Utils.extractValidatedString(configMap, "resources.requests.cpu"))
      , Utils.optional(Utils.extractValidatedString(configMap, "resources.limits.memory"))
      , Utils.optional(Utils.extractValidatedString(configMap, "resources.limits.cpu"))
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
