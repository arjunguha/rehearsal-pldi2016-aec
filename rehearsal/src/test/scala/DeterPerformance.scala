import rehearsal._
import FSSyntax._
import scala.util.Random
import java.nio.file.Paths
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge


class DeterPerformance extends org.scalatest.FunSuite {
  val maxPathComponentLen = 10
  val maxFileLen = 10
  val paths = Seq()

  def randAlphaNumString(length: Int) = {
    val rand = new Random()
    val alphabet = ('a' to 'z') ++ ('A' to 'Z') ++ ('0' to '9')

    var str = ""
    for(j<-0 to length){
      val i = rand.nextInt(alphabet.length)
      str += alphabet(i)
    }
    str
  }

  def genRandomPath(pathLen: Int) = {
    var path = randAlphaNumString(maxPathComponentLen)
    for(i <- 1 to pathLen-1){
      path += "/" + randAlphaNumString(maxPathComponentLen)
    }
    paths = path :: paths
    Paths.get(path)
  }

  def genRandomProg(length: Int, maxPathLen: Int) = {
    var x = List(CreateFile(genRandomPath(maxPathLen), randAlphaNumString(maxFileLen)))

    for(i <- 2 to length){
      x = x.:::(List(CreateFile(genRandomPath(maxPathLen), randAlphaNumString(maxFileLen))))
    }

    x.foldRight(Skip: Expr)((e, expr) => FSSyntax.Seq(e, expr))
  }

  def genRandomGraph(numProgs: Int, progLength: Int, maxPathLen: Int, overlap: Int) = {
    val g = Graph[Expr, DiEdge]()
    for(i <- 1 to numProgs){
      g.add(genRandomProg(progLength, maxPathLen))
    }
    g
  }

  val rand = new Random()
  println(genRandomGraph(rand.nextInt(10), rand.nextInt(10), 10))
}