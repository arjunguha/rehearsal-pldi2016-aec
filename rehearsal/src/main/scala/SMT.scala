package rehearsal

case class SMTError(resp: smtlib.parser.CommandsResponses.FailureResponse)
  extends RuntimeException(resp.toString)

object SMT {

  import smtlib.parser.Terms._
  import smtlib.theories.Core._

  private val names = collection.mutable.Map[String,Int]()

  def freshName(base: String = "x"): SSymbol = {
    names.get(base) match {
      case None => {
        names += (base -> 1)
        SSymbol(base + "0")
      }
      case Some(n) => {
        names += (base -> (n + 1))
        SSymbol(s"$base$n")
      }
    }
  }

  object Implicits {

    import scala.language.implicitConversions

    implicit class RichTerm(term: Term) {

      def &&(other: Term) = other match {
        case True() => term
        case False() => other
        case And(e1, e2) => And(term, e1, e2)
        case _ => And(term, other)
      }

    }

    implicit def stringToQualID(str: String): QualifiedIdentifier = {
      QualifiedIdentifier(Identifier(SSymbol(str)))
    }

    implicit def symbolToQualID(s: SSymbol): QualifiedIdentifier = {
      QualifiedIdentifier(Identifier(s))
    }

  }


}

class SMT(outputFile: Option[String]) extends smtlib.Interpreter with com.typesafe.scalalogging.LazyLogging {

  import java.nio.file._
  import smtlib.parser.Commands._
  import smtlib.parser.CommandsResponses._
  import smtlib.interpreters.Z3Interpreter

  private val interpreter = Z3Interpreter.buildDefault

  private val outputPath = outputFile.map(p => Paths.get(p))

  def free(): Unit = {
    interpreter.free()
  }

  def interrupt(): Unit = {
    interpreter.interrupt()
  }

  def eval(command: Command) : CommandResponse = {
    logger.debug(command.toString)

    outputPath match {
      case None => ()
      case Some(p) => {
        Files.write(p, command.toString.getBytes, StandardOpenOption.APPEND,
                    StandardOpenOption.CREATE)
        Files.write(p, "\n".getBytes, StandardOpenOption.APPEND)
      }
    }

    val resp = interpreter.eval(command)
    resp match {
      case Error(msg) => {
        logger.error(s"Error from SMT solver: $msg")
        throw SMTError(Error(msg))
      }
      case Unsupported => {
        logger.error("Unsupported from SMT solver")
        throw SMTError(Unsupported)
      }
      case _ => {
        logger.debug(resp.toString)
        resp
      }
    }
  }

}
