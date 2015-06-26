package rehearsal

case class SMTError(resp: smtlib.parser.CommandsResponses.FailureResponse)
  extends RuntimeException(resp.toString)

class SMT(outputFile: Option[String]) extends com.typesafe.scalalogging.LazyLogging {

  import java.nio.file._
  import smtlib.parser.Commands._
  import smtlib.parser.CommandsResponses._
  import smtlib.interpreters.Z3Interpreter

  private val interpreter = Z3Interpreter.buildDefault

  private val outputPath = outputFile.map(p => Paths.get(p))

  def process(command: Command) : CommandResponse = {
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
