package com.ing.bakery.clustercontroller

import com.ing.baker.runtime.scaladsl.InteractionInstance
import com.ing.baker.types.CharArray
import com.ing.bakery.clustercontroller.controllers.BakerResource.SidecarSpec
import com.ing.bakery.clustercontroller.controllers._
import skuber.{EnvVar, ObjectMeta}

import scala.concurrent.Future

object BakeryControllerFixtures {

  val interactionResource: InteractionResource = InteractionResource(
    metadata = ObjectMeta(name = "localhost"),
    spec = InteractionResource.Spec(
      image = "interaction.image:1.0.0",
      imagePullSecret = None,
      replicas = 2,
      env = List(
        EnvVar("ONE", EnvVar.StringValue("one")),
        EnvVar("TWO", EnvVar.ConfigMapKeyRef(name = "my-config-map", key = "two")),
        EnvVar("THREE", EnvVar.SecretKeyRef(name = "my-secret", key = "three"))
      ),
      configMapMounts = Some(List("test-config")),
      secretMounts = Some(List("my-secret")),
      resources = Some(skuber.Resource.Requirements(
        requests = Map("cpu" -> skuber.Resource.Quantity("600m"), "memory" -> skuber.Resource.Quantity("500Mi")),
        limits = Map("cpu" -> skuber.Resource.Quantity("6000m"), "memory" -> skuber.Resource.Quantity("1000Mi"))
      ))
    )
  )

  val interactionConfigMapResource: skuber.ConfigMap = skuber.ConfigMap(
    metadata = ObjectMeta(name = "localhost"),
    data = Map(
      "image" -> "interaction.image:1.0.0",
      "replicas" -> "2",
      "env.0.name" -> "ONE",
      "env.0.value" -> "1",
      "env.1.name" -> "TWO",
      "env.1.valueFrom.configMapKeyRef.name" -> "test-config",
      "env.1.valueFrom.configMapKeyRef.key" -> "ONE",
      "env.2.name" -> "THREE",
      "env.2.valueFrom.secretKeyRef.name" -> "test-secret",
      "env.2.valueFrom.secretKeyRef.key" -> "username",
      "configMapMounts.0" -> "test-config",
      "secretMounts.0" -> "test-secret",
      "resources.requests.cpu" -> "600m",
      "resources.requests.memory" -> "500Mi",
      "resources.limits.cpu" -> "6000m",
      "resources.limits.memory" -> "1000Mi"
    )
  )

  val interaction: InteractionInstance = InteractionInstance(
    name = "interaction-one",
    input = Seq(CharArray),
    run = _ => Future.successful(None)
  )

  val bakerResource: BakerResource = BakerResource(
    metadata = ObjectMeta(name = "test-recipe"),
    spec = BakerResource.Spec(
      image = "bakery-baker:local",
      imagePullSecret = None,
      serviceAccountSecret = None,
      kafkaBootstrapServers = None,
      replicas = 2,
      recipes = List("CgdXZWJzaG9wErEQChYKFAoQdW5hdmFpbGFibGVJdGVtcxABCkVaQwo/ChdTaGlwcGluZ0FkZHJlc3NSZWNlaXZlZBIkCg9zaGlwcGluZ0FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREAEKEwoRCg1yZXNlcnZlZEl0ZW1zEAEKCwoJCgVpdGVtcxABCg8KDQoJU2hpcEl0ZW1zEAIKnANimQMKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCk8KDUl0ZW1zUmVzZXJ2ZWQSPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWEkQKGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIoChB1bmF2YWlsYWJsZUl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERJPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFiIcCgdvcmRlcklkEhEiDwoNCgdvcmRlcklkEgIIESIdCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEqDFJlc2VydmVJdGVtczIMUmVzZXJ2ZUl0ZW1zUhAaDgjoBxEAAAAAAAAAQBgFCkhaRgpCChpQYXltZW50SW5mb3JtYXRpb25SZWNlaXZlZBIkChJwYXltZW50SW5mb3JtYXRpb24SDiIMCgoKBGluZm8SAggREAEKFVoTCg8KDVBheW1lbnRGYWlsZWQQAApQWk4KSgoLT3JkZXJQbGFjZWQSHAoHb3JkZXJJZBIRIg8KDQoHb3JkZXJJZBICCBESHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAEKFQoTCg9zaGlwcGluZ0FkZHJlc3MQAQpKWkgKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAAK2wNi2AMKcQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggRCg8KDVBheW1lbnRGYWlsZWQScQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREg8KDVBheW1lbnRGYWlsZWQiFgoQcmVjaXBlSW5zdGFuY2VJZBICCBEiPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWIiQKD3NoaXBwaW5nQWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEiJAoScGF5bWVudEluZm9ybWF0aW9uEg4iDAoKCgRpbmZvEgIIESoLTWFrZVBheW1lbnQyC01ha2VQYXltZW50UhAaDgjoBxEAAAAAAAAAQBgFClVaUwpPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFhAAChMKEQoNc2hpcHBpbmdPcmRlchABChlaFwoTChFTaGlwcGluZ0NvbmZpcm1lZBAACndadQpxChFQYXltZW50U3VjY2Vzc2Z1bBJcCg1zaGlwcGluZ09yZGVyEksiSQodCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEKCgoEZGF0YRICCBYKHAoHYWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEQAAoRCg8KC01ha2VQYXltZW50EAIKGAoWChJwYXltZW50SW5mb3JtYXRpb24QAQoSChAKDFJlc2VydmVJdGVtcxACCrMBYrABChMKEVNoaXBwaW5nQ29uZmlybWVkEhMKEVNoaXBwaW5nQ29uZmlybWVkIlwKDXNoaXBwaW5nT3JkZXISSyJJCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFgocCgdhZGRyZXNzEhEiDwoNCgdhZGRyZXNzEgIIESoJU2hpcEl0ZW1zMglTaGlwSXRlbXNSEBoOCOgHEQAAAAAAAABAGAUKDQoLCgdvcmRlcklkEAESBggLEBAYARIGCBEQCxgBEiAIEhAKGAEiGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIVCBIQDBgBIg1JdGVtc1Jlc2VydmVkEgYIAhALGAESBggGEBEYARIGCAgQFBgBEgYICBADGAESBggBEAkYARIGCAkQCxgBEgYIBRASGAESBggDEAUYARIGCAwQAhgBEgYIChAAGAESBggNEBMYARIZCAQQDhgBIhFTaGlwcGluZ0NvbmZpcm1lZBIGCA8QDRgBEhkIEBAPGAEiEVBheW1lbnRTdWNjZXNzZnVsEhUIEBAHGAEiDVBheW1lbnRGYWlsZWQSBggTEAQYARIGCBQQBRgBOhA5YTJmOGMyODgwZWE4ZmMw"),
      resources = Some(skuber.Resource.Requirements(
        requests = Map("cpu" -> skuber.Resource.Quantity("600m"), "memory" -> skuber.Resource.Quantity("500Mi")),
        limits = Map("cpu" -> skuber.Resource.Quantity("6000m"), "memory" -> skuber.Resource.Quantity("1000Mi"))
      )),
      config = Some("test-config"),
      secrets = None,
      apiLoggingEnabled = true,
      sidecar = None
    )
  )

  val bakerConfigMapResource: skuber.ConfigMap = skuber.ConfigMap(
    metadata = ObjectMeta(name = "test-recipe"),
    data = Map(
      "image" -> "bakery-baker:local",
      "replicas" -> "2",
      "config" -> "test-config",
      "recipes.0" -> "CgdXZWJzaG9wErEQChYKFAoQdW5hdmFpbGFibGVJdGVtcxABCkVaQwo/ChdTaGlwcGluZ0FkZHJlc3NSZWNlaXZlZBIkCg9zaGlwcGluZ0FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREAEKEwoRCg1yZXNlcnZlZEl0ZW1zEAEKCwoJCgVpdGVtcxABCg8KDQoJU2hpcEl0ZW1zEAIKnANimQMKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCk8KDUl0ZW1zUmVzZXJ2ZWQSPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWEkQKGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIoChB1bmF2YWlsYWJsZUl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERJPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFiIcCgdvcmRlcklkEhEiDwoNCgdvcmRlcklkEgIIESIdCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEqDFJlc2VydmVJdGVtczIMUmVzZXJ2ZUl0ZW1zUhAaDgjoBxEAAAAAAAAAQBgFCkhaRgpCChpQYXltZW50SW5mb3JtYXRpb25SZWNlaXZlZBIkChJwYXltZW50SW5mb3JtYXRpb24SDiIMCgoKBGluZm8SAggREAEKFVoTCg8KDVBheW1lbnRGYWlsZWQQAApQWk4KSgoLT3JkZXJQbGFjZWQSHAoHb3JkZXJJZBIRIg8KDQoHb3JkZXJJZBICCBESHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAEKFQoTCg9zaGlwcGluZ0FkZHJlc3MQAQpKWkgKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAAK2wNi2AMKcQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggRCg8KDVBheW1lbnRGYWlsZWQScQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREg8KDVBheW1lbnRGYWlsZWQiFgoQcmVjaXBlSW5zdGFuY2VJZBICCBEiPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWIiQKD3NoaXBwaW5nQWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEiJAoScGF5bWVudEluZm9ybWF0aW9uEg4iDAoKCgRpbmZvEgIIESoLTWFrZVBheW1lbnQyC01ha2VQYXltZW50UhAaDgjoBxEAAAAAAAAAQBgFClVaUwpPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFhAAChMKEQoNc2hpcHBpbmdPcmRlchABChlaFwoTChFTaGlwcGluZ0NvbmZpcm1lZBAACndadQpxChFQYXltZW50U3VjY2Vzc2Z1bBJcCg1zaGlwcGluZ09yZGVyEksiSQodCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEKCgoEZGF0YRICCBYKHAoHYWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEQAAoRCg8KC01ha2VQYXltZW50EAIKGAoWChJwYXltZW50SW5mb3JtYXRpb24QAQoSChAKDFJlc2VydmVJdGVtcxACCrMBYrABChMKEVNoaXBwaW5nQ29uZmlybWVkEhMKEVNoaXBwaW5nQ29uZmlybWVkIlwKDXNoaXBwaW5nT3JkZXISSyJJCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFgocCgdhZGRyZXNzEhEiDwoNCgdhZGRyZXNzEgIIESoJU2hpcEl0ZW1zMglTaGlwSXRlbXNSEBoOCOgHEQAAAAAAAABAGAUKDQoLCgdvcmRlcklkEAESBggLEBAYARIGCBEQCxgBEiAIEhAKGAEiGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIVCBIQDBgBIg1JdGVtc1Jlc2VydmVkEgYIAhALGAESBggGEBEYARIGCAgQFBgBEgYICBADGAESBggBEAkYARIGCAkQCxgBEgYIBRASGAESBggDEAUYARIGCAwQAhgBEgYIChAAGAESBggNEBMYARIZCAQQDhgBIhFTaGlwcGluZ0NvbmZpcm1lZBIGCA8QDRgBEhkIEBAPGAEiEVBheW1lbnRTdWNjZXNzZnVsEhUIEBAHGAEiDVBheW1lbnRGYWlsZWQSBggTEAQYARIGCBQQBRgBOhA5YTJmOGMyODgwZWE4ZmMw",
      "resources.requests.cpu" -> "600m",
      "resources.requests.memory" -> "500Mi",
      "resources.limits.cpu" -> "6000m",
      "resources.limits.memory" -> "1000Mi"
    )
  )

  val bakerResourceSidecar: BakerResource = BakerResource(
    metadata = ObjectMeta(name = "test-recipe"),
    spec = BakerResource.Spec(
      image = "bakery-baker:local",
      imagePullSecret = None,
      serviceAccountSecret = None,
      kafkaBootstrapServers = None,
      replicas = 2,
      recipes = List("CgdXZWJzaG9wErEQChYKFAoQdW5hdmFpbGFibGVJdGVtcxABCkVaQwo/ChdTaGlwcGluZ0FkZHJlc3NSZWNlaXZlZBIkCg9zaGlwcGluZ0FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREAEKEwoRCg1yZXNlcnZlZEl0ZW1zEAEKCwoJCgVpdGVtcxABCg8KDQoJU2hpcEl0ZW1zEAIKnANimQMKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCk8KDUl0ZW1zUmVzZXJ2ZWQSPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWEkQKGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIoChB1bmF2YWlsYWJsZUl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERJPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFiIcCgdvcmRlcklkEhEiDwoNCgdvcmRlcklkEgIIESIdCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEqDFJlc2VydmVJdGVtczIMUmVzZXJ2ZUl0ZW1zUhAaDgjoBxEAAAAAAAAAQBgFCkhaRgpCChpQYXltZW50SW5mb3JtYXRpb25SZWNlaXZlZBIkChJwYXltZW50SW5mb3JtYXRpb24SDiIMCgoKBGluZm8SAggREAEKFVoTCg8KDVBheW1lbnRGYWlsZWQQAApQWk4KSgoLT3JkZXJQbGFjZWQSHAoHb3JkZXJJZBIRIg8KDQoHb3JkZXJJZBICCBESHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAEKFQoTCg9zaGlwcGluZ0FkZHJlc3MQAQpKWkgKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAAK2wNi2AMKcQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggRCg8KDVBheW1lbnRGYWlsZWQScQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREg8KDVBheW1lbnRGYWlsZWQiFgoQcmVjaXBlSW5zdGFuY2VJZBICCBEiPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWIiQKD3NoaXBwaW5nQWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEiJAoScGF5bWVudEluZm9ybWF0aW9uEg4iDAoKCgRpbmZvEgIIESoLTWFrZVBheW1lbnQyC01ha2VQYXltZW50UhAaDgjoBxEAAAAAAAAAQBgFClVaUwpPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFhAAChMKEQoNc2hpcHBpbmdPcmRlchABChlaFwoTChFTaGlwcGluZ0NvbmZpcm1lZBAACndadQpxChFQYXltZW50U3VjY2Vzc2Z1bBJcCg1zaGlwcGluZ09yZGVyEksiSQodCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEKCgoEZGF0YRICCBYKHAoHYWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEQAAoRCg8KC01ha2VQYXltZW50EAIKGAoWChJwYXltZW50SW5mb3JtYXRpb24QAQoSChAKDFJlc2VydmVJdGVtcxACCrMBYrABChMKEVNoaXBwaW5nQ29uZmlybWVkEhMKEVNoaXBwaW5nQ29uZmlybWVkIlwKDXNoaXBwaW5nT3JkZXISSyJJCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFgocCgdhZGRyZXNzEhEiDwoNCgdhZGRyZXNzEgIIESoJU2hpcEl0ZW1zMglTaGlwSXRlbXNSEBoOCOgHEQAAAAAAAABAGAUKDQoLCgdvcmRlcklkEAESBggLEBAYARIGCBEQCxgBEiAIEhAKGAEiGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIVCBIQDBgBIg1JdGVtc1Jlc2VydmVkEgYIAhALGAESBggGEBEYARIGCAgQFBgBEgYICBADGAESBggBEAkYARIGCAkQCxgBEgYIBRASGAESBggDEAUYARIGCAwQAhgBEgYIChAAGAESBggNEBMYARIZCAQQDhgBIhFTaGlwcGluZ0NvbmZpcm1lZBIGCA8QDRgBEhkIEBAPGAEiEVBheW1lbnRTdWNjZXNzZnVsEhUIEBAHGAEiDVBheW1lbnRGYWlsZWQSBggTEAQYARIGCBQQBRgBOhA5YTJmOGMyODgwZWE4ZmMw"),
      resources = Some(skuber.Resource.Requirements(
        requests = Map("cpu" -> skuber.Resource.Quantity("600m"), "memory" -> skuber.Resource.Quantity("500Mi")),
        limits = Map("cpu" -> skuber.Resource.Quantity("6000m"), "memory" -> skuber.Resource.Quantity("1000Mi"))
      )),
      config = Some("test-config"),
      secrets = None,
      apiLoggingEnabled = true,
      sidecar = Some(
        SidecarSpec(
          image = "bakery-baker:local",
          resources = Some(skuber.Resource.Requirements(
            requests = Map("cpu" -> skuber.Resource.Quantity("600m"), "memory" -> skuber.Resource.Quantity("500Mi")),
            limits = Map("cpu" -> skuber.Resource.Quantity("6000m"), "memory" -> skuber.Resource.Quantity("1000Mi"))
          )),
          environment = Some(Map(
            "POD_IP" -> "@status.podIP",
            "CLUSTER_DNS_SUFFIX" -> ".test.local"
          )),
          configVolumeMountPath = Some("/home/app/config"),
          readinessProbe = Some(skuber.Probe(
            action = skuber.HTTPGetAction(
              port = Right("8443"),
              path = "/metrics",
              schema = "https"
            ),
            initialDelaySeconds = 15,
            timeoutSeconds = 10
          )),
          livenessProbe = Some(
            skuber.Probe(
              action = skuber.HTTPGetAction(
                port = Right("8443"),
                path = "/metrics",
                schema = "https"
              ),
              initialDelaySeconds = 15,
              timeoutSeconds = 10
            )
          )
        )
      )
    )
  )

  val bakerConfigMapResourceSidecar: skuber.ConfigMap = skuber.ConfigMap(
    metadata = ObjectMeta(name = "test-recipe"),
    data = Map(
      "image" -> "bakery-baker:local",
      "replicas" -> "2",
      "config" -> "test-config",
      "recipes.0" -> "CgdXZWJzaG9wErEQChYKFAoQdW5hdmFpbGFibGVJdGVtcxABCkVaQwo/ChdTaGlwcGluZ0FkZHJlc3NSZWNlaXZlZBIkCg9zaGlwcGluZ0FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREAEKEwoRCg1yZXNlcnZlZEl0ZW1zEAEKCwoJCgVpdGVtcxABCg8KDQoJU2hpcEl0ZW1zEAIKnANimQMKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCk8KDUl0ZW1zUmVzZXJ2ZWQSPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWEkQKGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIoChB1bmF2YWlsYWJsZUl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIERJPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFiIcCgdvcmRlcklkEhEiDwoNCgdvcmRlcklkEgIIESIdCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEqDFJlc2VydmVJdGVtczIMUmVzZXJ2ZUl0ZW1zUhAaDgjoBxEAAAAAAAAAQBgFCkhaRgpCChpQYXltZW50SW5mb3JtYXRpb25SZWNlaXZlZBIkChJwYXltZW50SW5mb3JtYXRpb24SDiIMCgoKBGluZm8SAggREAEKFVoTCg8KDVBheW1lbnRGYWlsZWQQAApQWk4KSgoLT3JkZXJQbGFjZWQSHAoHb3JkZXJJZBIRIg8KDQoHb3JkZXJJZBICCBESHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAEKFQoTCg9zaGlwcGluZ0FkZHJlc3MQAQpKWkgKRAoYT3JkZXJIYWRVbmF2YWlsYWJsZUl0ZW1zEigKEHVuYXZhaWxhYmxlSXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggREAAK2wNi2AMKcQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggRCg8KDVBheW1lbnRGYWlsZWQScQoRUGF5bWVudFN1Y2Nlc3NmdWwSXAoNc2hpcHBpbmdPcmRlchJLIkkKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWChwKB2FkZHJlc3MSESIPCg0KB2FkZHJlc3MSAggREg8KDVBheW1lbnRGYWlsZWQiFgoQcmVjaXBlSW5zdGFuY2VJZBICCBEiPgoNcmVzZXJ2ZWRJdGVtcxItIisKHQoFaXRlbXMSFBoSChAiDgoMCgZpdGVtSWQSAggRCgoKBGRhdGESAggWIiQKD3NoaXBwaW5nQWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEiJAoScGF5bWVudEluZm9ybWF0aW9uEg4iDAoKCgRpbmZvEgIIESoLTWFrZVBheW1lbnQyC01ha2VQYXltZW50UhAaDgjoBxEAAAAAAAAAQBgFClVaUwpPCg1JdGVtc1Jlc2VydmVkEj4KDXJlc2VydmVkSXRlbXMSLSIrCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFhAAChMKEQoNc2hpcHBpbmdPcmRlchABChlaFwoTChFTaGlwcGluZ0NvbmZpcm1lZBAACndadQpxChFQYXltZW50U3VjY2Vzc2Z1bBJcCg1zaGlwcGluZ09yZGVyEksiSQodCgVpdGVtcxIUGhIKECIOCgwKBml0ZW1JZBICCBEKCgoEZGF0YRICCBYKHAoHYWRkcmVzcxIRIg8KDQoHYWRkcmVzcxICCBEQAAoRCg8KC01ha2VQYXltZW50EAIKGAoWChJwYXltZW50SW5mb3JtYXRpb24QAQoSChAKDFJlc2VydmVJdGVtcxACCrMBYrABChMKEVNoaXBwaW5nQ29uZmlybWVkEhMKEVNoaXBwaW5nQ29uZmlybWVkIlwKDXNoaXBwaW5nT3JkZXISSyJJCh0KBWl0ZW1zEhQaEgoQIg4KDAoGaXRlbUlkEgIIEQoKCgRkYXRhEgIIFgocCgdhZGRyZXNzEhEiDwoNCgdhZGRyZXNzEgIIESoJU2hpcEl0ZW1zMglTaGlwSXRlbXNSEBoOCOgHEQAAAAAAAABAGAUKDQoLCgdvcmRlcklkEAESBggLEBAYARIGCBEQCxgBEiAIEhAKGAEiGE9yZGVySGFkVW5hdmFpbGFibGVJdGVtcxIVCBIQDBgBIg1JdGVtc1Jlc2VydmVkEgYIAhALGAESBggGEBEYARIGCAgQFBgBEgYICBADGAESBggBEAkYARIGCAkQCxgBEgYIBRASGAESBggDEAUYARIGCAwQAhgBEgYIChAAGAESBggNEBMYARIZCAQQDhgBIhFTaGlwcGluZ0NvbmZpcm1lZBIGCA8QDRgBEhkIEBAPGAEiEVBheW1lbnRTdWNjZXNzZnVsEhUIEBAHGAEiDVBheW1lbnRGYWlsZWQSBggTEAQYARIGCBQQBRgBOhA5YTJmOGMyODgwZWE4ZmMw",
      "resources.requests.cpu" -> "600m",
      "resources.requests.memory" -> "500Mi",
      "resources.limits.cpu" -> "6000m",
      "resources.limits.memory" -> "1000Mi",
      "sidecar.image" -> "bakery-baker:local",
      "sidecar.configVolumeMountPath" -> "/home/app/config",
      "sidecar.resources.requests.cpu" -> "600m",
      "sidecar.resources.requests.memory" -> "500Mi",
      "sidecar.resources.limits.cpu" -> "6000m",
      "sidecar.resources.limits.memory" -> "1000Mi",
      "sidecar.livenessProbe.scheme" -> "https",
      "sidecar.livenessProbe.port" -> "10080",
      "sidecar.livenessProbe.path" -> "/metrics",
      "sidecar.readinessProbe.scheme" -> "https",
      "sidecar.readinessProbe.port" -> "10080",
      "sidecar.readinessProbe.path" -> "/metrics",
      "sidecar.environment.POD_IP" -> "@status.podIP",
      "sidecar.environment.CLUSTER_DNS_SUFFIX" -> ".test.local"
    )
  )

}
