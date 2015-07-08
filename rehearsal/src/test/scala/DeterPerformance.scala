import rehearsal._
import FSSyntax._
import scala.util.Random
import java.nio.file.Paths
import java.nio.file.Path
import scalax.collection.Graph
import scalax.collection.GraphEdge.DiEdge


class DeterPerformance extends org.scalatest.FunSuite {
  val maxPathComponentLen = 3
  val maxFileLen = 10
  var paths: List[Path] = List()

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
    paths = paths.:::(List(Paths.get(path)))
    Paths.get(path)
  }

  def getRandomPath() = {
    val rand = new Random()
    val i = rand.nextInt(paths.length - 1)
    if(i ==0){
      paths = paths.drop(i)
    }else if(i == paths.length-1){
      paths = paths.dropRight(i)
    }else{
      paths = paths.dropRight(i) ++ paths.drop(i)
    }    
    paths(i)
  }

  def genRandomProg(length: Int, pathLen: Int) = {
    var x: List[Expr] = List()

    for(i <- 1 to length){
      val path = getRandomPath()
      x = x.:::(List(CreateFile(path, randAlphaNumString(maxFileLen))))
    }

    x.foldRight(Skip: Expr)((e, expr) => FSSyntax.Seq(e, expr))
  }

  def genRandomGraph(numProgs: Int, progLength: Int, pathLen: Int, overlap: Int) = {
    val numPaths = numProgs * progLength - overlap;
    for(i <- 1 to numPaths){
      genRandomPath(pathLen)
    }
    for(j <- 1 to overlap){
      paths = paths.:::(List(paths(new Random().nextInt(paths.length))))
    }
    var g = Graph[Expr, DiEdge]()
    for(i <- 1 to numProgs){
      g = g + (genRandomProg(progLength, pathLen))
    }
    g
  }

  val rand = new Random()
  genRandomGraph(10, 3, 3, 2)
  println(paths)
}