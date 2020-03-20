package com.ing.baker.il.pnml

import com.ing.baker.compiler.RecipeCompiler
import fr.lip6.move.pnml.validation.impl.CheckPnmlFileImpl
import org.scalatest.{FunSuite, Matchers}
import java.io.{File, PrintWriter}

import com.ing.baker.recipe.TestRecipe

class RecipePnmlExporterTest extends FunSuite with Matchers {

  test("generated PNML is valid") {
    val compiled = RecipeCompiler.compileRecipe(TestRecipe.getRecipe("pnml-test"))
    val pnmlString = RecipePnmlExporter.exportToPnml(compiled.petriNet)
    val pnmlFile = writeToTempFile(pnmlString, prefix = Some("pnml-test"), suffix = Some(".pnml"))
    val checker = new CheckPnmlFileImpl()
    val result = checker.checkPnmlFile(pnmlFile.getAbsolutePath)
    println(result)
  }


  /** Creates a temporary file, writes the input string to the file, and the file handle.
    *
    * NOTE: This funciton uses the createTempFile function from the File class. The prefix and
    * suffix must be at least 3 characters long, otherwise this function throws an
    * IllegalArgumentException.
    */
  def writeToTempFile(contents: String,
                      prefix: Option[String] = None,
                      suffix: Option[String] = None): File = {
    val tempFi = File.createTempFile(prefix.getOrElse("prefix-"),
      suffix.getOrElse("-suffix"))
    tempFi.deleteOnExit()
    new PrintWriter(tempFi) {
      // Any statements inside the body of a class in scala are executed on construction.
      // Therefore, the following try-finally block is executed immediately as we're creating
      // a standard PrinterWriter (with its implementation) and then using it.
      // Alternatively, we could have created the PrintWriter, assigned it a name,
      // then called .write() and .close() on it. Here, we're simply opting for a terser representation.
      try {
        write(contents)
      } finally {
        close()
      }
    }
    tempFi
  }
}
