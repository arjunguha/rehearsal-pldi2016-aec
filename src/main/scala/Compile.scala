package rehearsal

object Compile {

  import java.nio.file.{Path, Paths}
  import rehearsal.{FSSyntax => F}
  import F.{Seq => FSeq}
  import F._
  import rehearsal.Implicits._
  import rehearsal.{Syntax => P}
  import P._
  import ResourceModel.{Res => ResModel, File, Package, User, Group}
  import Evaluator.ResourceGraph
  import scalax.collection.mutable.Graph
  import scalax.collection.mutable.Graph._
  import scalax.collection.GraphEdge._

  case class FSCompileError(msg: String) extends RuntimeException(msg)

  //compile to ResourceModel.Res

  def attrsToMap(attrs: scala.collection.Seq[Attribute]): Map[String, P.Expr] = attrs match {
    case scala.collection.Seq() => Map()
    case Attribute(Str(name), value) :: t => attrsToMap(t) + Tuple2(name, value)
  }
  

  //these are the file cuttently types accepted by isPrimitiveType in PuppetEval
  def compileResource(r: Resource): ResModel = {
    val attrsMap = attrsToMap(r.attrs)
    r.typ match {
      //TODO
      case "file" => File(Paths.get(""), "", false)
      //TODO
      case "package" => Package("", false)
      //TODO
      case "user" => User("", false, false)
      case "group" => {
        val nameAttr = attrsMap.get("name")
        val ensureAttr = attrsMap.get("ensure")
        val name: String = nameAttr match {
          case None => r.title match {
            case Str(n) => n
            case _ => throw FSCompileError(s"invalid value for resource title: $r.title")
          }          
          case Some(Str(n)) => n
          case _ => throw FSCompileError(s"invalid value for 'name' attribute: $nameAttr")
        }
        val present = ensureAttr match {
          case Some(Str("present")) => true
          case Some(Str("absent")) => false
          //TODO: find out if there is a default value for 'ensure'
          case _ => throw FSCompileError(s"invalid value for 'ensure' attribute: $ensureAttr")
        }
        Group(name, present)
      }
    }
  }
  
  //TODO(rian)
  //use compile function in ResourceModel to go from ResModel to FS
  def compile(g: ResourceGraph): FileScriptGraph = Graph()
}
