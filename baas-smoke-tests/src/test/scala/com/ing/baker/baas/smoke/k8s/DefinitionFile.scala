package com.ing.baker.baas.smoke.k8s

import cats.effect.{IO, Resource, Timer}
import cats.syntax.functor._
import com.ing.baker.baas.smoke.k8s.KubernetesCommands.exec
import com.ing.baker.baas.smoke.{ prefixGreen, prefixCyan }

case class DefinitionFile(path: String, namespace: Option[Namespace]) {

  def delete(implicit timer: Timer[IO]): IO[Unit] = {
    val kubernetesConfigPath = DefinitionFile.getPathSafe("/kubernetes")
    exec(
      prefix = prefixCyan(s"deleting file $path $namespace"),
      command = s"kubectl delete -f $kubernetesConfigPath/$path ${namespace.fold("")(ns => "-n " + ns)}"
    ).void
  }
}

object DefinitionFile {

  def apply(path: String, namespace: Namespace): IO[DefinitionFile] =
    apply(path, Some(namespace))

  def apply(path: String, namespace: Option[Namespace]): IO[DefinitionFile] = {
    val kubernetesConfigPath = getPathSafe("/kubernetes")
    exec(prefixGreen(s"applying file $path $namespace"), command = s"kubectl apply -f $kubernetesConfigPath/$path ${namespace.fold("")(ns => "-n " + ns)}")
      .map(_ => new DefinitionFile(path, namespace))
  }

  def resource(path: String, namespace: Namespace)(implicit timer: Timer[IO]): Resource[IO, DefinitionFile] = {
    Resource.make(apply(path, Some(namespace)))(_.delete)
  }

  def resource(path: String)(implicit timer: Timer[IO]): Resource[IO, DefinitionFile] = {
    Resource.make(apply(path, None))(_.delete)
  }

  private[k8s] def getPathSafe(resourcePath: String): String = {
    val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
    val safePath = getClass.getResource(resourcePath).getPath
    if (isWindows) safePath.tail
    else safePath
  }
}
