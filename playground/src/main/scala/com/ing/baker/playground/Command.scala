package com.ing.baker.playground

import cats.implicits._
import com.ing.baker.playground.AppUtils._
import com.ing.baker.playground.Command.RunCommand
import com.ing.baker.playground.commands.{BaaS, Terminal}

trait Command {
  def name: String
  def help: String = "No help for this command"
  def run: RunCommand
}

object Command {

  type RunCommand = PartialFunction[String, App[Unit]]

  val commands: List[Command] =
    List(
      Help,
      StartBaaS,
      BuildImage
    )

  case object Help extends Command {

    override def name: String = "help"

    override def help: String = "Displays this help menu"

    override def run: RunCommand = {
      case "help" =>
        printLn("") *>
          commands.traverse { command =>
            val spaces = List.fill(20 - command.name.length)(".").mkString
            printLn(command.name + " " + spaces + " " + command.help)
          } *>
          printLn("")
    }
  }

  case object StartBaaS extends Command {

    override def name: String = "start-baas"

    override def help: String = "Starts Cassandra, Haproxy and a cluster of 3 baas state nodes"

    override def run: RunCommand = { case "start-baas" => BaaS.startBaaS }
  }

  case object BuildImage extends Command {

    override def name: String = "build"

    override def help: String = "Builds all playground required images from the baker repository"

    override def run: RunCommand = {
      case "build" => BaaS.buildStateNodesHAProxyImage
    }
  }
}
