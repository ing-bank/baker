package com.ing.baker.runtime.actor.serialization

import com.esotericsoftware.kryo.io.{Input, Output}
import com.esotericsoftware.kryo.{Kryo, Serializer}
import com.ing.baker.petrinet.api.{BiPartiteGraph, ScalaGraphPetriNet}

import scalax.collection.edge.WLDiEdge

case class SerializableEdge(from: Int, to: Int, weight: Long, label: Any)

case class SerializableGraph[P, T](nodes: List[Either[P, T]], edges: List[SerializableEdge]) {

  def buildGraph: BiPartiteGraph[P, T, WLDiEdge] = {

    val params = edges.map { e =>

      val fromNode = nodes.apply(e.from)
      val toNode = nodes.apply(e.to)

      WLDiEdge[Either[P, T], Any](fromNode, toNode)(e.weight, e.label)
    }

    scalax.collection.immutable.Graph(params: _*)
  }
}

class KryoGraphSerializer extends Serializer[ScalaGraphPetriNet[_,_]]{

  override def write(kryo: Kryo, output: Output, petriNet: ScalaGraphPetriNet[_, _]) = {

    val nodeList = petriNet.nodes.toList

    val edges = petriNet.innerGraph.edges.toList.map { e =>

      val from = nodeList.indexOf(e.source.value.asInstanceOf[Either[_, _]])
      val to = nodeList.indexOf(e.target.value.asInstanceOf[Either[_, _]])

      SerializableEdge(from, to, e.weight, e.label)
    }

    val serializableGraph = SerializableGraph(nodeList, edges)

    kryo.writeObject(output, serializableGraph)
  }

  override def read(kryo: Kryo, input: Input, aClass: Class[ScalaGraphPetriNet[_, _]]): ScalaGraphPetriNet[_,_] = {

    val serializeableGraph = kryo.readObject(input, classOf[SerializableGraph[_, _]])

    new ScalaGraphPetriNet(serializeableGraph.buildGraph)
  }
}
