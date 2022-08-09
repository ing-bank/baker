package com.ing.baker.http.server.scaladsl

import com.typesafe.config.Config

case class Http4sBakerServerConfiguration(apiHost: String,
                                          apiPort: Int,
                                          apiUrlPrefix: String,
                                          loggingEnabled: Boolean)

object Http4sBakerServerConfiguration {
  def fromConfig(config: Config) : Http4sBakerServerConfiguration = {
    val bakerConfig = config.getConfig("baker")

    Http4sBakerServerConfiguration(
      apiHost = bakerConfig.getString("api-host"),
      apiPort = bakerConfig.getInt("api-port"),
      apiUrlPrefix = bakerConfig.getString("api-url-prefix"),
      loggingEnabled = bakerConfig.getBoolean("api-logging-enabled")
    )
  }
}
