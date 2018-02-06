package com.ing.baker.il

import com.ing.baker.petrinet.api._

import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object petrinet {

  type RecipePetriNet = PetriNet[Place[_], Transition[_, _]]

  def arc(t: Transition[_, _], p: Place[_], weight: Long): Arc = WLDiEdge[Node, Edge[Any]](Right(t), Left(p))(weight, Edge[Any](None))

  def arc[C](p: Place[C], t: Transition[_, _], weight: Long, eventFilter: Option[String] = None): Arc = {
    WLDiEdge[Node, Edge[C]](Left(p), Right(t))(weight, Edge[C](eventFilter))
  }

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place[_], Transition[_, _]]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]

  case class Label(value: String) extends AnyVal

  type Labeled[T] = T => Label

  implicit def placeLabel[C](p: Place[C]): Label = Label(p.label)

  implicit def transitionLabeler(t: Transition[_, _]): Label = Label(t.label)

  implicit class LabeledOps[T : Labeled](seq: Iterable[T]) {
    def findByLabel(label: String): Option[T] = seq.find(e ⇒ implicitly[Labeled[T]].apply(e).value == label)
    def getByLabel(label: String): T = findByLabel(label).getOrElse { throw new IllegalStateException(s"No element found with label: $label") }
  }

  implicit def placeIdentifier(p: Place[_]): Id = Id(p.id)

  implicit def transitionIdentifier(t: Transition[_, _]): Id = Id(t.id)

  def createPetriNet(params: Arc*): RecipePetriNet = {
    val petriNet = new ScalaGraphPetriNet(Graph(params: _*))

    requireUniqueElements(petriNet.places.toSeq.map(_.id), "Place identifier")
    requireUniqueElements(petriNet.transitions.toSeq.map(_.id), "Transition identifier")

    petriNet
  }

}
