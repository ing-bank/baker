package com.ing.baker.runtime.testkit

/**
  * Minimal runtime adapter used by shared contract tests.
  *
  * Runtime-specific modules provide concrete implementations for Akka and Pekko.
  */
trait RuntimeTestAdapter[Runtime] {

  /** Name used in test output and diagnostics. */
  def runtimeName: String

  /**
    * Build a runtime instance and pass it into the test body.
    *
    * Implementations should handle setup/teardown so shared tests remain framework-agnostic.
    */
  def withRuntime(test: Runtime => Any): Any
}

