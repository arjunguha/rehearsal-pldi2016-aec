
import rehearsal.fsmodel._
import FSSyntax._

import java.nio.file.Paths
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge
import rehearsal.ppmodel._
import puppet.syntax.parse
import puppet.graph._
import puppet.Facter
import rehearsal.fsmodel.Implicits._
import java.nio.file.Path
import java.nio.file.Paths
class Test extends org.scalatest.FunSuite {

  import exp.SymbolicEvaluator2.{predEquals, exprEquals, isDeterministic}

  val zeros = "00000"

  val x = 
    If(TestFileState(Paths.get("/arjun"), IsFile),
      Rm(Paths.get("/arjun")) >> CreateFile(Paths.get("/arjun"), zeros),
      If(TestFileState(Paths.get("/arjun"), DoesNotExist), 
         CreateFile(Paths.get("/arjun"), zeros), 
         Skip)) >>
    If(TestFileState(Paths.get("/home/aaron"), IsFile), 
       Rm(Paths.get("/home/aaron")), 
       Skip) >>
    CreateFile(Paths.get("/home/aaron"), zeros)

  val y = 
    If(TestFileState(Paths.get("/home/aaron"), IsFile),
       Rm(Paths.get("/home/aaron")) >> CreateFile(Paths.get("/home/aaron"), zeros),
       If(TestFileState(Paths.get("/home/aaron"), DoesNotExist), 
          CreateFile(Paths.get("/home/aaron"), zeros),
          Skip))

  println(exprEquals(x, y))

}
