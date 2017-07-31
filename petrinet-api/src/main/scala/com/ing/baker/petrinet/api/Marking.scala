package com.ing.baker.petrinet.api

object Marking {

  def empty[P[_]]: Marking[P] = HMap[P, MultiSet](Map.empty)

  def apply[P[_], A](m1: MarkedPlace[P, A]): Marking[P] = {
    HMap[P, MultiSet](Map[P[_], MultiSet[_]](m1))
  }

  def apply[P[_], A, B](m1: MarkedPlace[P, A], m2: MarkedPlace[P, B]): Marking[P] = {
    HMap[P, MultiSet](Map[P[_], MultiSet[_]](m1, m2))
  }

  def apply[P[_], A, B, C](m1: MarkedPlace[P, A], m2: MarkedPlace[P, B], m3: MarkedPlace[P, C]): Marking[P] = {
    HMap[P, MultiSet](Map[P[_], MultiSet[_]](m1, m2, m3))
  }

  def apply[P[_], A, B, C, D](m1: MarkedPlace[P, A], m2: MarkedPlace[P, B], m3: MarkedPlace[P, C], m4: MarkedPlace[P, D]): Marking[P] = {
    HMap[P, MultiSet](Map[P[_], MultiSet[_]](m1, m2, m3, m4))
  }

  def apply[P[_], A, B, C, D, E](m1: MarkedPlace[P, A], m2: MarkedPlace[P, B], m3: MarkedPlace[P, C], m4: MarkedPlace[P, D], m5: MarkedPlace[P, E]): Marking[P] = {
    HMap[P, MultiSet](Map[P[_], MultiSet[_]](m1, m2, m3, m4, m5))
  }
}