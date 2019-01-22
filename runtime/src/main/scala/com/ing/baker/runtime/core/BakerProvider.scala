package com.ing.baker.runtime.core

import com.typesafe.config.{Config, ConfigFactory}
import net.ceedubs.ficus.Ficus._

object BakerProvider {

  def get(config: Config): Baker = {
    config.getAs[String]("baker.engine-provider")
      .map { engineProviderName: String =>
        try {
          val clazz = Class.forName(engineProviderName).newInstance()
          clazz match {
            case provider: BakerProvider => provider.apply(config)
            case _ => throw new IllegalArgumentException("baker.engine-provider does not point to a correct BakerProvider class")
          }
        } catch {
          case _: InstantiationException => throw new IllegalArgumentException("baker.engine-provider points to a class without default constructor")
          case e: Throwable => throw e
        }
      }.getOrElse(new BakerAkkaProvider().apply(config))
  }

  def get(): Baker = BakerProvider.get(ConfigFactory.load())

  def apply(config: Config): Baker = BakerProvider.get(config)

  def apply(): Baker = BakerProvider.get()
}

trait BakerProvider {
  def apply(config: Config): Baker
}