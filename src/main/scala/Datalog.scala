package rehearsal

object Datalog {

  import scala.util.parsing.combinator.{PackratParsers, RegexParsers}

  val illegalIdentifierChars = List(':', '(', '`', '\'', ')', '=', ':', '.',
    '~', '?', '\"', '%', ' ')

  def isValidIdentifier(str: String): Boolean = {
    str.length >= 1 &&
    str(0).isUpper == false &&
    str.forall(ch => illegalIdentifierChars.contains(ch) == false)
  }

  type Pred = String

  sealed trait Term
  case class Lit(name: String) extends Term {
    assert(isValidIdentifier(name))
    override def toString(): String = name
  }
  case class Var(name: String) extends Term {
    assert(name.length >= 1 && name(0).isUpper &&
           name.forall(ch => ch.isLetterOrDigit || ch == '_'))
    override def toString(): String = name
  }

  case class Fact(pred: Pred, terms: List[Term]) {
    assert(isValidIdentifier(pred))

    override def toString(): String = {
      val termsStr = terms.mkString(",")
      s"$pred($termsStr)"
    }
  }

  sealed trait Assertion
  case class GroundFact(fact: Fact) extends Assertion {
    override def toString(): String = fact.toString + "."
  }
  case class Rule(head: Fact, body: List[Fact]) extends Assertion {
    override def toString(): String = {
     head.toString + " :- " + body.mkString(", ") + "."
    }
  }
  case class Query(fact: Fact) extends Assertion {
    override def toString(): String = fact.toString + "?"
  }


  object Parser extends RegexParsers with PackratParsers {

    lazy val id: PackratParser[String] = """[0-9a-z]([0-9a-zA-Z_])*""".r ^^ identity

    lazy val term: PackratParser[Term] = (
      id ^^ { x => Lit(x) }
      )

    lazy val fact: PackratParser[Fact] = (
      id ~ "(" ~ repsep(term, ",") ~ ")" ~ "." ^^
        { case pred ~ _ ~ terms ~ _ ~ _ => Fact(pred, terms) }
      )

    lazy val facts: PackratParser[List[Fact]] = rep(fact)



  }

  /** Produces a list of ground facts. */
  def eval(assertions: List[Assertion]): List[Fact] = {
    import java.nio.file.{Paths, Files}
    import sys.process._
    val db = Files.createTempFile("datalog", ".rkt")
    val dbString = "#lang datalog\n" + assertions.mkString("\n")
    Files.write(db, dbString.getBytes())
    val facts = Seq("racket", db.toString).lineStream.mkString("\n")
    Files.deleteIfExists(db)
    Parser.parseAll(Parser.facts, facts) match {
      case Parser.Success(facts, _) => facts
      case Parser.NoSuccess(msg, _) => throw new Exception(msg.toString)
    }
  }




}
