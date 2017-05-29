package com.ing.baker.compiledRecipe

import com.ing.baker.compiledRecipe.ingredientExtractors.IngredientExtractor
import com.ing.baker.core.ProcessState
import fs2.Strategy
import io.kagera.api._
import io.kagera.execution.ExceptionStrategy.BlockTransition
import io.kagera.execution._

import scalax.collection.edge.WLDiEdge
import scalax.collection.immutable.Graph

package object petrinet {

  type RecipePetriNet = PetriNet[Place[_], Transition[_, _, _]]

  val jobPicker = new JobPicker[Place, Transition](new RecipeTokenGame()) {
    override def isFireable[S](instance: Instance[Place, Transition, S], t: Transition[_, _, _]): Boolean = t match {
      case EventTransition(_, isSensoryEvent, _) => !isSensoryEvent
      case _ => true
    }
  }

  val transitionExceptionHandler: Transition[_,_,_] => TransitionExceptionHandler = {
    case interaction: InteractionTransition[_] => interaction.exceptionStrategy
    case _ => (e, n) => BlockTransition
  }

  def transitionEventSource(ingredientExtractor: IngredientExtractor): Transition[_,_,_] => (ProcessState => Any => ProcessState) = {
    case t: InteractionTransition[_] => EventSource.updateIngredientState(t, ingredientExtractor)
    case t: EventTransition[_]       => EventSource.updateEventState(t, ingredientExtractor)
    case t                           => s => e => s
  }

  def jobExecutor(topology: RecipePetriNet, interactions: Map[Class[_], () => AnyRef], ingredientExtractor: IngredientExtractor, evaluationStrategy: Strategy) =
    new JobExecutor[ProcessState, Place, Transition](topology, new TaskProvider(interactions, ingredientExtractor), transitionExceptionHandler)(evaluationStrategy)

  def arc(t: Transition[_, _, _], p: Place[_], weight: Long): Arc = WLDiEdge[Node, String](Right(t), Left(p))(weight, "")

  def arc[C](p: Place[C], t: Transition[_, _, _], weight: Long, filter: C ⇒ Boolean = (token: C) ⇒ true): Arc = {
    val innerEdge = new PTEdge[C](weight, filter)
    WLDiEdge[Node, PTEdge[C]](Left(p), Right(t))(weight, innerEdge)
  }

  /**
    * Type alias for the node type of the scalax.collection.Graph backing the petri net.
    */
  type Node = Either[Place[_], Transition[_, _, _]]

  /**
    * Type alias for the edge type of the scalax.collection.Graph backing the petri net.
    */
  type Arc = WLDiEdge[Node]

  implicit def placeLabel[C](p: Place[C]): Label = Label(p.label)

  implicit def placeIdentifier(p: Place[_]): Id = Id(p.id)

  implicit def transitionLabeler(t: Transition[_, _, _]): Label = Label(t.label)

  implicit def transitionIdentifier(t: Transition[_, _, _]): Id = Id(t.id)

  def createPetriNet[S](params: Arc*): RecipePetriNet = {
    val petriNet = new ScalaGraphPetriNet(Graph(params: _*))

    requireUniqueElements(petriNet.places.toSeq.map(_.id), "Place identifier")
    requireUniqueElements(petriNet.transitions.toSeq.map(_.id), "Transition identifier")

    petriNet
  }

}
