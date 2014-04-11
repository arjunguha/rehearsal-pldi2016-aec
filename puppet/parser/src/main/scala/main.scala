object main {

  def main (args: Array[String]) {

    // val reader = new FileReader (args (0))
    val src1 = scala.io.Source.fromFile (args (0)).mkString
    val ast1 = PuppetParser (src1) match {
      case PuppetParser.Success (ast, _) => ast
      case e: PuppetParser.NoSuccess => throw new RuntimeException ("Parsing original source failed: " + e)
    }

    
    val src2 = PrettyPrintAST.printAST (ast1)
    val ast2 = PuppetParser (src2) match {
      case PuppetParser.Success (ast, _) => ast
      case e: PuppetParser.NoSuccess => println (src1); println (ast1); println (src2); throw new RuntimeException ("Parsing pretty source failed:" + e)
    }

    if (ast1 == ast2)
      println ("Success")
    else {
      // TODO : Print both AST
      println ("Failure")
      println (src1)
      println (ast1)
      println (src2)
      println (ast2)
    }
  }
}
