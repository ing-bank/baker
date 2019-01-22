package com.ing.baker.runtime.core

import com.typesafe.config.{Config, ConfigFactory}

object BakerProvider {

  def get(config: Config): Baker = {
    val enginePath = "baker.engine-provider"
    if (config.hasPath("baker.engine-provider")) {
      try {
        val clazz = Class.forName(config.getString(enginePath)).newInstance()
        clazz match {
          case provider: BakerProvider => provider.apply(config)
          case _ => throw new IllegalArgumentException("baker.engine-provider does not point to a correct BakerProvider class")
        }
      } catch {
        case _ : InstantiationException => throw new IllegalArgumentException("baker.engine-provider points to a class without default constructor")
        case e: Throwable => throw e
      }
    }
    else {
      new BakerAkkaProvider().apply(config)
    }
  }

  def get(): Baker = BakerProvider.get(ConfigFactory.load())

  def apply(config: Config): Baker = BakerProvider.get(config)

  def apply(): Baker = BakerProvider.get()
}

trait BakerProvider {
  def apply(config: Config): Baker
}