package com.ing.bakery.kubeapi

object TextUtils {

  def mkJsonString(data: Map[String, String]): String =
    data.toList
      .map { case (tag, value) => s""""$tag": "$value""""}
      .mkString("{ ", ", ", " }")
}
