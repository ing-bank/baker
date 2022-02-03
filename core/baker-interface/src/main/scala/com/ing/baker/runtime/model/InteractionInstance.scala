package com.ing.baker.runtime.model

import java.lang.reflect
import java.lang.reflect.{Method, Parameter}
import java.security.MessageDigest
import java.util
import java.util.concurrent.CompletableFuture
import java.util.{Base64, Optional}

import cats.implicits._
import cats.{Applicative, ~>}
import com.ing.baker.recipe.annotations.{FiresEvent, RequiresIngredient}
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.scaladsl.{EventInstance, IngredientInstance, InteractionInstanceInput}
import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.types.{Converters, Type}

import scala.collection.JavaConverters._
import scala.concurrent.Future
import scala.reflect.ClassTag
import scala.util.Try

abstract class InteractionInstance[F[_]] extends common.InteractionInstance[F] with ScalaApi { self =>

  val run: Seq[IngredientInstance] => F[Option[EventInstance]]

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override type Input = InteractionInstanceInput

  override def execute(input: Seq[IngredientInstance]): F[Option[Event]] =
    run(input)

  def shaBase64: String = {
    val nameBytes: Array[Byte] = name.getBytes("UTF-8")
    val interfaceBytes: Array[Byte] = input.toArray.map(_.hashCode().toByte)
    val sha: Array[Byte] = MessageDigest.getInstance("SHA-256").digest(nameBytes ++ interfaceBytes)
    val base64: Array[Byte] = Base64.getEncoder.encode(sha)
    new String(base64)
  }

  def translate[G[_]](mapK: F ~> G): InteractionInstance[G] =
    new InteractionInstance[G] {
      override val run: Seq[IngredientInstance] => G[Option[EventInstance]] =
        (i: Seq[IngredientInstance]) => mapK(self.run(i))
      override val name: String =
        self.name
      override val input: Seq[InteractionInstanceInput] =
        self.input
      override val output: Option[Map[String, Map[String, Type]]] =
        self.output
    }

  def asDeprecatedFutureImplementation(transform: F ~> Future): com.ing.baker.runtime.scaladsl.InteractionInstance = {
    val transformedRun = (in: Seq[IngredientInstance]) => transform(run(in))
    com.ing.baker.runtime.scaladsl.InteractionInstance(
      name = name, input = input, run = transformedRun, output = output)
  }
}

object InteractionInstance {

  type Constructor[F[_]] = (
    String,
    Seq[Type],
    Seq[IngredientInstance] => F[Option[EventInstance]],
    Option[Map[String, Map[String, Type]]]) => InteractionInstance[F]

  def build[F[_]](_name: String, _input: Seq[InteractionInstanceInput], _run: Seq[IngredientInstance] => F[Option[EventInstance]], _output: Option[Map[String, Map[String, Type]]] = None): InteractionInstance[F] =
    new InteractionInstance[F] {
      override val name: String = _name
      override val input: Seq[InteractionInstanceInput] = _input
      override val run: Seq[IngredientInstance] => F[Option[EventInstance]] = _run
      override val output: Option[Map[String, Map[String, Type]]] = _output
    }

  def unsafeFromList[F[_]](implementations: List[AnyRef])(implicit effect: Applicative[F], classTag: ClassTag[F[Any]]): List[InteractionInstance[F]] = {
    implementations.map(unsafeFrom[F](_))
  }

  def unsafeFrom[F[_]](implementation: AnyRef)(implicit effect: Applicative[F], classTag: ClassTag[F[Any]]): InteractionInstance[F] = {
    val method: Method = {
      val unmockedClass = common.unmock(implementation.getClass)
      unmockedClass.getMethods.count(_.getName == "apply") match {
        case 0          => throw new IllegalArgumentException(s"Implementation ${implementation.getClass.getName} does not have a apply function")
        case n if n > 1 => throw new IllegalArgumentException(s"Implementation ${implementation.getClass.getName} has multiple apply functions")
        case _          => unmockedClass.getMethods.find(_.getName == "apply").get
      }
    }

    val parentDefinition: Option[Class[_]] =
      common.unmock(implementation.getClass).getInterfaces.find {
        clazz => {
          Try {
            clazz.getMethod(method.getName, method.getParameterTypes.toSeq: _*)
          }.isSuccess
        }
      }

    val parentMethod: Option[Method] = {
      parentDefinition.map(_.getMethod(method.getName, method.getParameterTypes.toSeq: _*))
    }

    def getNameFieldName(method: Method): Option[String] = {
      Try {
        method.getDeclaringClass.getDeclaredField("name")
      }.toOption match {
        // In case a specific 'name' field was found, this is used
        case Some(field) if field.getType == classOf[String] =>
          field.setAccessible(true)
          Some(field.get(implementation).asInstanceOf[String])
        case None => None
      }
    }

    val name: String =
    //First we check if the class of the method has a name field defined.
      getNameFieldName(method)
        .getOrElse(
          parentMethod match {
            //else If a parent method is defined we check the name field of this.
            case Some(parentMethod) => getNameFieldName(parentMethod)
              //If parent is defined but no name field we take the name of the parent.
              .getOrElse(parentMethod.getDeclaringClass.getSimpleName)
            //If no parent method is defined we take the class name
            case None => method.getDeclaringClass.getSimpleName
          })

    def hasInputAnnotations(method: Method): Boolean = {
      method.getGenericParameterTypes.zip(method.getParameters).exists {
        case (_, parameter: Parameter) => parameter.isAnnotationPresent(classOf[RequiresIngredient])
      }
    }

    def getInputWithAnnotatedNames(method: Method): Seq[InteractionInstanceInput] = {
      method.getGenericParameterTypes.zip(method.getParameters).map { case (typ: reflect.Type, parameter: Parameter) =>
        try {
          if (parameter.isAnnotationPresent(classOf[RequiresIngredient])) {
            val name = parameter.getAnnotationsByType(classOf[RequiresIngredient]).map((requiresIngredient: RequiresIngredient) => {
              requiresIngredient.value()
            }).head
            InteractionInstanceInput(Option(name), Converters.readJavaType(typ))
          }
          else {
            // We are not taking parameter.name as default since with Java reflection this will not be filled correctly with a name.
            InteractionInstanceInput(None, Converters.readJavaType(typ))
          }
        }
        catch { case e: Exception =>
          throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
        }
      }
    }

    val input: Seq[InteractionInstanceInput] = {
      if(hasInputAnnotations(method)) {
        getInputWithAnnotatedNames(method)
      } else if(parentMethod.isDefined && hasInputAnnotations(parentMethod.get)) {
        getInputWithAnnotatedNames(parentMethod.get)
      } else {
        getInputWithAnnotatedNames(method)
      }
    }

    def extractOutput(method: Method): Map[String, Map[String, Type]] = {
      val outputEventClasses: Seq[Class[_]] = method.getAnnotation(classOf[FiresEvent]).oneOf()
      outputEventClasses.map(eventClass =>
        eventClass.getSimpleName ->
          eventClass.getDeclaredFields.toIndexedSeq
            .filter(field => !field.isSynthetic)
            .map(f => f.getName -> Converters.readJavaType(f.getGenericType)).toMap
      ).toMap
    }

    val output: Option[Map[String, Map[String, Type]]] = {
      //Check the class itself for the FiresEvent annotation
      if (method.isAnnotationPresent(classOf[FiresEvent])) {
        Some(extractOutput(method))
      }
      // Check the direct parent interfaces for the class for the apply method and FiresEvent annotations.
      else {
        parentMethod match {
          case Some(parentMethod) =>
            if(parentMethod.isAnnotationPresent(classOf[FiresEvent]))
              Some(extractOutput(parentMethod))
            else None
          case None => None
        }
      }
    }

    val run: Seq[IngredientInstance] => F[Option[EventInstance]] = runtimeInput => {
      // Translate the Value objects to the expected runtimeInput types
      val inputArgs: Seq[AnyRef] = runtimeInput.zip(method.getGenericParameterTypes).map {
        case (value, targetType) => value.value.as(targetType).asInstanceOf[AnyRef]
      }
      val callOutput = method.invoke(implementation, inputArgs: _*)
      val futureClass: ClassTag[CompletableFuture[Any]] = implicitly[ClassTag[CompletableFuture[Any]]]

      Option(callOutput) match {
        case Some(event) =>
          event match {
            // Async interactions using java CompletableFuture
            // TODO rewrite this to not block in in case of java CompletableFutures.
            case runtimeEventAsyncJava if futureClass.runtimeClass.isInstance(runtimeEventAsyncJava) =>
              effect.pure(Some(EventInstance.unsafeFrom(runtimeEventAsyncJava.asInstanceOf[CompletableFuture[Any]].get())))
            // Async interactions using F
            case runtimeEventAsync if classTag.runtimeClass.isInstance(runtimeEventAsync) =>
              runtimeEventAsync
                .asInstanceOf[F[Any]]
                .map(event0 => Some(EventInstance.unsafeFrom(event0)))
            case other =>
              effect.pure(Some(EventInstance.unsafeFrom(other)))
          }
        case None =>
          effect.pure(None)
      }
    }
    build[F](name, input, run, output)
  }
}
