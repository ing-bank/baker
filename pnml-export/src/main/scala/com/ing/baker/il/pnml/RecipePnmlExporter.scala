package com.ing.baker.il.pnml

import com.ing.baker.il.RecipeVisualizer.RecipePetriNetGraph
import com.ing.baker.il.petrinet.{Place, RecipePetriNet, Transition}
import fr.lip6.move.pnml.framework.utils.ModelRepository
import fr.lip6.move.pnml.pnmlcoremodel.hlapi._


object RecipePnmlExporter {
  def exportToPnml(graph: RecipePetriNet): String = {
    ModelRepository.getInstance.createDocumentWorkspace("void")
    val doc: PetriNetDocHLAPI = new PetriNetDocHLAPI()
    val net: PetriNetHLAPI = new PetriNetHLAPI("net0",
      PNTypeHLAPI.COREMODEL,
      new NameHLAPI("baker-petri-net"),
      doc)
    val page: PageHLAPI =
      new PageHLAPI("toppage", new NameHLAPI("toppage"), null, net)
    def createGraphics(x: Int, y: Int) = new NodeGraphicsHLAPI(new PositionHLAPI(x, y), null, null, null)
    val places = graph.places.map{p =>
      val place = new PlaceHLAPI(s"place${p.id}", new NameHLAPI(p.label), createGraphics(100, 100))
      place.setContainerPageHLAPI(page)
      p.id -> place
    }.toMap
    val transitions = graph.transitions.map { t =>
      val transition = new TransitionHLAPI(s"transition${t.id}", new NameHLAPI(t.label), createGraphics(200, 200))
      transition.setContainerPageHLAPI(page)
      t.id -> transition
    }.toMap
    def lookupNode(placeOrTransistion: Either[Place, Transition]): NodeHLAPI =
      placeOrTransistion.fold(p => places(p.id), t => transitions(t.id))
    def recipeEdgeTransformer(innerEdge: RecipePetriNetGraph#EdgeT): ArcHLAPI = {
      val source = lookupNode(innerEdge.edge.source.value)
      val target = lookupNode(innerEdge.edge.target.value)
      new ArcHLAPI(s"${source.getId}->${target.getId}", source, target, page)
    }
    graph.innerGraph.edges.foreach { e =>
       recipeEdgeTransformer(e)
    }
    val res = doc.toPNML
    ModelRepository.getInstance.destroyCurrentWorkspace()
    res
  }
}
