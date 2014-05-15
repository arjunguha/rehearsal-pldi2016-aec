package test.puppet

import puppet.driver._
import org.scalatest._

class CompilerSpec extends FlatSpec {

  val smoke_test = "./example/simple_relation.pp"

  "Compiler" should "not throw an exception" in {

      val content = scala.io.Source.fromFile (smoke_test).getLines () mkString "\n"
      PuppetDriver (content)
  }
}
