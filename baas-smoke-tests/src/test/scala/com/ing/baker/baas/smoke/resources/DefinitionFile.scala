package com.ing.baker.baas.smoke.resources

import cats.effect.{IO, Resource, Timer}
import com.ing.baker.baas.smoke.exec
import cats.syntax.functor._

case class DefinitionFile(path: String, namespace: Option[String])

object DefinitionFile {

  private def getPathSafe(resourcePath: String): String = {
    val isWindows: Boolean = sys.props.get("os.name").exists(_.toLowerCase().contains("windows"))
    val safePath = getClass.getResource(resourcePath).getPath
    if (isWindows) safePath.tail
    else safePath
  }

  def resource(path: String, namespace: String)(implicit timer: Timer[IO]): Resource[IO, DefinitionFile] = {
    Resource.make(applyFileResource(path, Some(namespace)))(deleteFileResource)
  }

  def resource(path: String)(implicit timer: Timer[IO]): Resource[IO, DefinitionFile] = {
    Resource.make(applyFileResource(path, None))(deleteFileResource)
  }

  private def applyFileResource(path: String, namespace: Option[String]): IO[DefinitionFile] = {
    val kubernetesConfigPath = getPathSafe("/kubernetes")
    val prefix = s"[${Console.GREEN}applying file $path $namespace${Console.RESET}]"
    exec(prefix, command = s"kubectl apply -f $kubernetesConfigPath/$path ${namespace.fold("")(ns => "-n " + ns)}")
      .map(_ => DefinitionFile(path, namespace))
  }

  private def deleteFileResource(definitionFile: DefinitionFile)(implicit timer: Timer[IO]): IO[Unit] = {
    val kubernetesConfigPath = getPathSafe("/kubernetes")
    val prefix = s"[${Console.CYAN}deleting file ${definitionFile.path} ${definitionFile.namespace}${Console.RESET}]"
    exec(prefix, command = s"kubectl delete -f $kubernetesConfigPath/${definitionFile.path} ${definitionFile.namespace.fold("")(ns => "-n " + ns)}").void
  }
}
