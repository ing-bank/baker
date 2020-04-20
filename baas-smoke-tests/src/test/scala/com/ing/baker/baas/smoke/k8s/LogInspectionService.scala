package com.ing.baker.baas.smoke.k8s

import java.net.InetSocketAddress

import cats.effect.concurrent.{MVar, Ref}
import cats.effect.{ContextShift, IO, Resource, Timer}
import cats.implicits._
import com.ing.baker.baas.smoke.printYellow
import org.http4s._
import org.http4s.dsl.io._
import org.http4s.headers.`Content-Type`
import org.http4s.implicits._
import org.http4s.server.Router
import org.http4s.server.blaze.BlazeServerBuilder

import scala.sys.process._

object LogInspectionService {

  class Inspector private(podsF: Ref[IO, Map[String, Ref[IO, List[String]]]], lock: MVar[IO, Unit]) {

    def awaitLock: IO[Unit] =
      lock.take

    def terminateTests: IO[Unit] =
      lock.put(())

    def addPod(name: String): IO[Unit] =
      for {
        pods <- podsF.get
        _ <- if (pods.contains(name)) IO.unit else for {
          lines <- Ref.of[IO, List[String]](List.empty)
          _ <- podsF.update(_ + (name -> lines))
        } yield ()
      } yield ()

    def getPodNames: IO[List[String]] =
      podsF.get.map(_.keys.toList)

    def addLine(name: String, line: String): IO[Unit] =
      for {
        pods <- podsF.get
        _ <- pods.get(name) match {
          case None => IO.unit
          case Some(linesF) =>
            linesF.update(line :: _)
        }
      } yield ()

    def getPodLines(name: String): IO[List[String]] =
      for {
        pods <- podsF.get
        lines <- pods.get(name)
          .map(_.get)
          .getOrElse(IO.pure(List.empty[String]))
      } yield lines

    def watchLogs(name: String, container: Option[String], namespace: Namespace): IO[Unit] = {
      podsF.get.map(_.get(name)).flatMap {
        case None =>
          val command = s"kubectl logs $name ${container.map(_ + " ").getOrElse("")}-n $namespace"
          val logger = ProcessLogger(fn = line => addLine(name, line).unsafeRunAsyncAndForget())
          for {
            outcome <- IO(command.run(logger)).attempt
            _ <- outcome match {
              case Left(e) => IO.unit
              case Right(_) => addPod(name)
            }
          } yield ()

        case _ =>
          IO.unit
      }
    }

    def watchLogsWithPrefix(prefix: String, container: Option[String], namespace: Namespace): IO[Unit] =
      for {
        pods <- Pod.getPodsNames(prefix, namespace)
        _ <- pods.traverse { pod =>
          watchLogs(pod, container, namespace)
        }
      } yield ()
  }

  object Inspector {

    def empty(implicit cs: ContextShift[IO]): IO[Inspector] =
      for {
        pods <- Ref.of[IO, Map[String, Ref[IO, List[String]]]](Map.empty)
        lock <- MVar.empty[IO, Unit]
      } yield new Inspector(pods, lock)
  }


  def resource(testsName: String, hostname: InetSocketAddress, awaitLock: Boolean)(implicit cs: ContextShift[IO], timer: Timer[IO]): Resource[IO, Inspector] = {
    for {
      state <- Resource.liftF(Inspector.empty)
      _ <- BlazeServerBuilder[IO]
        .bindSocketAddress(hostname)
        .withHttpApp(new LogInspectionService(testsName, state).build)
        .resource
      _ <- Resource.make(IO.pure(state)) { inspector =>
        if(awaitLock) printYellow(s"To inspect the pods, please visit http://localhost:${hostname.getPort}/") *> printYellow(s"To terminate the tests, please visit http://localhost:${hostname.getPort}/terminate") *> inspector.awaitLock
        else IO.unit
      }
    } yield state
  }
}

final class LogInspectionService private(testName: String, state: LogInspectionService.Inspector)(implicit cs: ContextShift[IO], timer: Timer[IO]) {

  def build: HttpApp[IO] =
    api.orNotFound

  def api: HttpRoutes[IO] = Router("/" -> HttpRoutes.of[IO] {

    case GET -> Root =>
      for {
        pods <- state.getPodNames
        links = pods.sorted.map(podName => s""" <li> <a href="$podName">$podName</a> </li> """)
        response <- Ok(s"""
          |<head><title>$testName</title></head>
          |<body>
          |<h1>$testName</h1>
          |<a href="terminate">Terminate tests</a>
          |<ul>
          |${links.mkString("\n")}
          |</ul>
          |</body>
          |""".stripMargin)
      } yield response.withContentType(`Content-Type`(MediaType.text.html))

    case GET -> Root / "terminate" =>
      for {
        _ <- state.terminateTests
        response <- Ok(s"Terminating $testName now...")
      } yield response

    case GET -> Root / podName =>
      for {
        lines <- state.getPodLines(podName)
        commonStyle = "padding: 3px; font-family: 'Lucida Console', Courier, monospace; margin: 2px; "
        normalLineStyle = commonStyle
        errorStyle = commonStyle + "border-radius: 2px; color: red; border: 1px solid red; background-color: #ffe6e6;"
        debugStyle = commonStyle + "border-radius: 2px; color: #3366ff; border: 1px solid #b3c6ff; background-color: #e6ecff;"
        style = (line: String) =>
          if(line.toLowerCase.contains("debug")) debugStyle
          else if(line.toLowerCase.contains("error")) errorStyle
          else normalLineStyle
        html = lines.reverse.map(line => s""" <p style="${style(line)}"> $line </p> """)
        response <- Ok(s"""
          |<head><title>$testName / $podName </title></head>
          |<body>
          |<h1 style="font-family: 'Lucida Console', Courier, monospace;">$testName / $podName</h1>
          |${html.mkString("\n")}
          |</body>
          |""".stripMargin)
      } yield response.withContentType(`Content-Type`(MediaType.text.html))
  })
}
