package com.ing

import java.io.{File, PrintWriter}

package object baker {

  def dumpToFile(fileName: String, data: String): Unit = {
    val outFile = new File(fileName)
    val writer = new PrintWriter(outFile)

    try {
      writer.write(data)
    } finally {
      writer.close()
    }
  }

}
