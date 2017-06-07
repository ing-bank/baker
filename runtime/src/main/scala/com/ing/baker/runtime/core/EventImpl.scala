package com.ing.baker.runtime.core

trait EventImpl {
  def name: String = this.getClass.getSimpleName
}
