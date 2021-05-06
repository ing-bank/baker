package com.ing.baker.runtime.scaladsl

import java.lang.reflect.Method
import java.security.MessageDigest
import java.util
import java.util.concurrent.CompletableFuture
import java.util.{Base64, Optional}

import cats.implicits._
import cats.{Applicative, ~>}
import com.ing.baker.recipe.annotations.FiresEvent
import com.ing.baker.runtime.common.LanguageDataStructures.ScalaApi
import com.ing.baker.runtime.{common, javadsl}
import com.ing.baker.types.{Converters, Type}

import scala.collection.JavaConverters._
import scala.concurrent.Future
import scala.reflect.ClassTag
import scala.util.Try

abstract class InteractionInstanceF[F[_]] extends common.InteractionInstance[F] with ScalaApi { self =>

  val run: Seq[IngredientInstance] => F[Option[EventInstance]]

  override type Event = EventInstance

  override type Ingredient = IngredientInstance

  override def execute(input: Seq[IngredientInstance]): F[Option[Event]] =
    run(input)

  def shaBase64: String = {
    val nameBytes: Array[Byte] = name.getBytes("UTF-8")
    val interfaceBytes: Array[Byte] = input.toArray.map(_.hashCode().toByte)
    val sha: Array[Byte] = MessageDigest.getInstance("SHA-256").digest(nameBytes ++ interfaceBytes)
    val base64: Array[Byte] = Base64.getEncoder.encode(sha)
    new String(base64)
  }

  def translate[G[_]](mapK: F ~> G): InteractionInstanceF[G] =
    new InteractionInstanceF[G] {
      override val run: Seq[IngredientInstance] => G[Option[EventInstance]] =
        (i: Seq[IngredientInstance]) => mapK(self.run(i))
      override val name: String =
        self.name
      override val input: Seq[Type] =
        self.input
      override val output: Option[Map[String, Map[String, Type]]] =
        self.output
    }

  def asJava(converter: F ~> CompletableFuture): javadsl.InteractionInstance =
    new javadsl.InteractionInstance {
      override val name: String =
        self.name
      override val input: util.List[Type] =
        self.input.asJava
      override val output: Optional[util.Map[String, util.Map[String, Type]]] =
        self.output match {
          case Some(out) => Optional.of(out.mapValues(_.asJava).asJava)
          case None => Optional.empty[util.Map[String, util.Map[String, Type]]]()
        }
      override def execute(input: util.List[javadsl.IngredientInstance]): CompletableFuture[Optional[javadsl.EventInstance]] =
        converter(self.run(input.asScala.map(_.asScala)))
          .thenApply(
            _.fold(Optional.empty[javadsl.EventInstance]())(
            e => Optional.of(e.asJava)))
    }

  def asDeprecatedFutureImplementation(transform: F ~> Future): InteractionInstance = {
    val transformedRun = (in: Seq[IngredientInstance]) => transform(run(in))
    InteractionInstance(
      name = name, input = input, run = transformedRun, output = output)
  }
}

object InteractionInstanceF {

  type Constructor[F[_]] = (
    String,
    Seq[Type],
    Seq[IngredientInstance] => F[Option[EventInstance]],
    Option[Map[String, Map[String, Type]]]) => InteractionInstanceF[F]

  def build[F[_]](_name: String, _input: Seq[Type], _run: Seq[IngredientInstance] => F[Option[EventInstance]], _output: Option[Map[String, Map[String, Type]]] = None): InteractionInstanceF[F] =
    new InteractionInstanceF[F] {
      override val name: String = _name
      override val input: Seq[Type] = _input
      override val run: Seq[IngredientInstance] => F[Option[EventInstance]] = _run
      override val output: Option[Map[String, Map[String, Type]]] = _output
    }

  def unsafeFromList[F[_]](implementations: List[AnyRef])(implicit effect: Applicative[F], classTag: ClassTag[F[Any]]): List[InteractionInstanceF[F]] = {
    implementations.map(unsafeFrom[F](_))
  }

  def unsafeFrom[F[_]](implementation: AnyRef)(implicit effect: Applicative[F], classTag: ClassTag[F[Any]]): InteractionInstanceF[F] = {
    val method: Method = {
      val unmockedClass = common.unmock(implementation.getClass)
      unmockedClass.getMethods.count(_.getName == "apply") match {
        case 0          => throw new IllegalArgumentException(s"Implementation ${implementation.getClass.getName} does not have a apply function")
        case n if n > 1 => throw new IllegalArgumentException(s"Implementation ${implementation.getClass.getName} has multiple apply functions")
        case _          => unmockedClass.getMethods.find(_.getName == "apply").get
      }
    }

    val name: String = {
      Try {
        method.getDeclaringClass.getDeclaredField("name")
      }.toOption match {
        // In case a specific 'name' field was found, this is used
        case Some(field) if field.getType == classOf[String] =>
          field.setAccessible(true)
          field.get(implementation).asInstanceOf[String]
        // Otherwise, try to find the interface that declared the method or falls back to the implementation class
        case None =>
          method.getDeclaringClass.getInterfaces.find {
            clazz => Try {
              clazz.getMethod(method.getName, method.getParameterTypes.toSeq: _*)
            }.isSuccess
          }.getOrElse(method.getDeclaringClass).getSimpleName
      }
    }
    val input: Seq[Type] = {
      method.getGenericParameterTypes.zip(method.getParameters).map { case (typ, _) =>
        try { Converters.readJavaType(typ) }
        catch { case e: Exception =>
          throw new IllegalArgumentException(s"Unsupported parameter type for interaction implementation '$name'", e)
        }
      }
    }

    val output: Option[Map[String, Map[String, Type]]] = {
      if (method.isAnnotationPresent(classOf[FiresEvent])) {
        val outputEventClasses: Seq[Class[_]] = method.getAnnotation(classOf[FiresEvent]).oneOf()
        val temp = Some(outputEventClasses.map(eventClass =>
          eventClass.getSimpleName ->
          eventClass.getDeclaredFields
            .filter(field => !field.isSynthetic)
            .map(f => f.getName -> Converters.readJavaType(f.getType)).toMap
        ).toMap)
        println("Output calculated")
        println(temp)
        temp
      }
      else None
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
              // Async interactions using java CompletableFuture needed for backwards compatibility
              // Blocking since mapping on it does not seem to work.
            case runtimeEventAsyncJava if futureClass.runtimeClass.isInstance(runtimeEventAsyncJava) =>
              effect.pure(Some(EventInstance.unsafeFrom(runtimeEventAsyncJava.asInstanceOf[CompletableFuture[Any]].get())))
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
