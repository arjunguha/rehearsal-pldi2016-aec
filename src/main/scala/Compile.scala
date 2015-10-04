package rehearsal

object Compile {

  import java.nio.file.{Path, Paths}
  import rehearsal.{FSSyntax => F}
  import F.{Seq => FSeq}
  import F._
  import rehearsal.Implicits._
  import rehearsal.{Syntax => P}
  import P._
  import ResourceModel.{Res => ResModel, File, Package, User, Group, EnsureFile, AbsentPath}
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
    val nameExpr = attrsMap.get("name")
    val ensureExpr = attrsMap.get("ensure")
    val name: String = nameExpr match {
      case None => r.title match {
        case Str(n) => n
        case _ => throw FSCompileError(s"invalid value for resource title: $r.title")
      }          
      case Some(Str(n)) => n
      case _ => throw FSCompileError(s"invalid value for 'name' attribute: $nameExpr")
    }
    val present = ensureExpr match {
      case Some(Str("present")) => true
      case Some(Str("absent")) => false
      //TODO: find out if there is a default value for 'ensure'
      case _ => throw FSCompileError(s"invalid value for 'ensure' attribute: $ensureExpr")
    }
    r.typ match {
      //TODO
      //assusming the only difference between File and EnsureFile is that File does not have ensure attribute
      case "file" => {
        val pathExpr = attrsMap.get("path")
        val contentExpr = attrsMap.get("content")
        val forceExpr = attrsMap.get("force")
        val path: String = pathExpr match {
          case None => r.title match {
            case Str(n) => n
            case _ => throw FSCompileError(s"invalid value for resource title: $r.title")
          }          
          case Some(Str(n)) => n
          case _ => throw FSCompileError(s"invalid value for 'path' attribute: $pathExpr")
        }
        val content: String = contentExpr match {
          case None => ""        
          case Some(Str(n)) => n
          case _ => throw FSCompileError(s"invalid value for 'content' attribute: $contentExpr")
        }
        val force = forceExpr match {
          case Some(Str("yes")) | Some(Bool(true)) => true
          case Some(Str("no")) | Some(Bool(false)) | None => false
          case _ => throw FSCompileError(s"invalid value for 'force' attribute: $forceExpr")
        }
        ensureExpr match {
          case None => File(Paths.get(path), content, force)
          case Some(Str("present")) => EnsureFile(Paths.get(path), content)
          case Some(Str("absent")) => AbsentPath(Paths.get(path), force)
          case _ => throw FSCompileError(s"invalid value for 'ensure' attribute $ensureExpr")
        }
      }
      case "package" => Package(name, present)
      case "user" => {
        val manageHomeExpr = attrsMap.get("managehome")
        val manageHome = manageHomeExpr match {
          case Some(Str("yes")) | Some(Bool(true)) => true
          case Some(Str("no")) | Some(Bool(false)) | None => false
          case _ => throw FSCompileError(s"invalid value for 'managehome' attribute: $manageHomeExpr")
        }        
        User(name, present, manageHome)
      }
      case "group" => Group(name, present)
    }
  }
  
  //TODO(rian)
  //use compile function in ResourceModel to go from ResModel to FS
  def compile(g: ResourceGraph): FileScriptGraph = Graph()
}
