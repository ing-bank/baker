import java.io.FileReader

import com.ing.baker.baas.state.KubernetesFunctions
import io.kubernetes.client.openapi.Configuration
import io.kubernetes.client.util.{ClientBuilder, KubeConfig}
import org.scalatest.WordSpecLike

class KubernetesTest extends WordSpecLike {
  "kubernetes API" should {
    "Connect from the outside" in {
      //Working remote
      // file path to your KubeConfig// file path to your KubeConfig
      val kubeConfigPath = "C:/Users/XK00LJ/.kube/config"

      // loading the out-of-cluster config, a kubeconfig from file-system
      val client = ClientBuilder.kubeconfig(KubeConfig.loadKubeConfig(new FileReader(kubeConfigPath))).build

      // set the global default api-client to the in-cluster one from above
      Configuration.setDefaultApiClient(client)

      KubernetesFunctions.getInteractionPods()
        .foreach(pod => println(pod.getMetadata.getName))
    }
  }
}