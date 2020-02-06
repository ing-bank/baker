package com.ing.baker.baas.dashboard

import akka.actor.Actor
import com.ing.baker.runtime.scaladsl.Baker

import scala.concurrent.Future

class BakeryInteractions(bakerClient: Baker) extends Actor {

  //def getAllRecipes: Future[]
}

object BakeryInteractions {


  case class BakeryEvent()

  case class GetAllRecipesRequest()

  case class GetAllRecipesResponse()



}

