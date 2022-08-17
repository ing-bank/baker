package com.ing.baker.http

import com.typesafe.config.{Config, ConfigFactory}
import org.scalatest.flatspec._
import org.scalatest.matchers._

import scala.io.Source
import scala.util.Try


class DashboardAndConfigurationSpec extends AnyFlatSpec with should.Matchers {

  "The dashboard object" should "list the static files" in {
    Dashboard.files.find(_ == "index.html") should not be empty
  }

  "The safe get resource url" should "return a valid resource" in {
    val path = Dashboard.safeGetResourcePath("index.html")
    path should not be empty
    Try(Source.fromResource(path.get)).toOption should not be empty
  }

  "The versionJson" should "return a valid response" in {
    val configuration = DashboardConfiguration(
      enabled = true,
      applicationName = "application name",
      clusterInformation = Map(
        "version1" -> "1.0",
        "version2" -> "2.0"
      )
    )
    Dashboard.dashboardConfigJson("/test/path", configuration).replace(" ", "") shouldEqual
      """{
        |   "applicationName": "application name",
        |   "apiPath": "/test/path",
        |   "clusterInformation": {
        |     "version1": "1.0",
        |     "version2": "2.0"
        |   }
        | }
        |""".stripMargin.replace(" ", "")
  }

  "The dashboard object" should "match correct urls" in {
    //TODO Revert this commit once scala-212 is no longer supported.
    "".matches(Dashboard.indexPattern.regex) shouldBe true
    "/".matches(Dashboard.indexPattern.regex) shouldBe true
    "/recipes".matches(Dashboard.indexPattern.regex) shouldBe true
    "/interactions".matches(Dashboard.indexPattern.regex) shouldBe true
    "/instances".matches(Dashboard.indexPattern.regex) shouldBe true
    "/instances/instance-id".matches(Dashboard.indexPattern.regex) shouldBe true
    "/instanceand".matches(Dashboard.indexPattern.regex) shouldBe false
    "/instance/".matches(Dashboard.indexPattern.regex) shouldBe false
  }

  "DashboardConfiguration" should "parse default configuration correctly" in {
    val referenceConfig = ConfigFactory.load()

    DashboardConfiguration.fromConfig(referenceConfig) shouldBe DashboardConfiguration(
      enabled = true,
      applicationName = "Baker OSS",
      clusterInformation = Map.empty
    )
  }

}
