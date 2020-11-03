package com.ing.baker.runtime.scaladsl

import java.lang.reflect.Method
import java.security.MessageDigest
import java.util
import java.util.{Base64, Optional}
import java.util.concurrent.CompletableFuture

import cats.Applicative
import cats.~>
import cats.implicits._
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
          .thenApply(_.fold(Optional.empty[javadsl.EventInstance]())(e => Optional.of(e.asJava)))
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
        case 0          => throw new IllegalArgumentException("Implementation does not have a apply function")
        case n if n > 1 => throw new IllegalArgumentException("Implementation has multiple apply functions")
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
    val run: Seq[IngredientInstance] => F[Option[EventInstance]] = runtimeInput => {
      // Translate the Value objects to the expected runtimeInput types
      val inputArgs: Seq[AnyRef] = runtimeInput.zip(method.getGenericParameterTypes).map {
        case (value, targetType) => value.value.as(targetType).asInstanceOf[AnyRef]
      }
      val output = method.invoke(implementation, inputArgs: _*)
      Option(output) match {
        case Some(event) =>
          event match {
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
    build[F](name, input, run, None)
  }
}
