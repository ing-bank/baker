package kamon

import kamon.prometheus.{PrometheusFormatter, PrometheusReporter}

object KamonBridge extends kamon.Configuration
  with kamon.Utilities
  with kamon.Metrics
  with kamon.Tracing
  with kamon.ModuleLoading
  with kamon.ContextPropagation
  with kamon.ContextStorage
  with kamon.CurrentStatus
  with kamon.Init {

  val prometheusFormatter = new PrometheusFormatter()
  _moduleRegistry.register("PrometheusFormatter", None, prometheusFormatter)

}