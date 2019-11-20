package com.ing.baker.playground

import cats.effect.IO

import scala.util.Random

object ColorPrint {

  private val colors: Array[String] = Array(
    Console.MAGENTA,
    Console.RED,
    Console.YELLOW,
    Console.GREEN,
    Console.CYAN,
    Console.BLUE
  )

  implicit class PrettyColorPrint[A](a: A) {

    def print: IO[Unit] =
      IO { println(a.toString) }

    def magenta: String =
      Console.MAGENTA + a.toString + Console.RESET

    def green: String =
      Console.GREEN + a.toString + Console.RESET

    def red: String =
      Console.RED + a.toString + Console.RESET

    def yellow: String =
      Console.YELLOW + a.toString + Console.RESET

    def randomColor: String =
      colors(Random.nextInt(colors.length)) + a.toString + Console.RESET

    def prompt(prepend: String): String =
      a.toString.lines.map(prepend + _).mkString("\n")

    def notice: String =
      " [>>>] " + a.toString + " [<<<] "
  }
}
