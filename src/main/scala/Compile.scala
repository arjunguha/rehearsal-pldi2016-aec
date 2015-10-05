package rehearsal

object Compile {

  import java.nio.file.{Path, Paths}
  import rehearsal.{FSSyntax => F}
  import F.{Seq => FSeq}
  import F._
  import rehearsal.Implicits._
  import rehearsal.{Syntax => P}
  import P._
  import ResourceModel.{Res => ResModel,_}
  import Evaluator.ResourceGraph
  import scalax.collection.mutable.Graph
  import scalax.collection.mutable.Graph._
  import scalax.collection.GraphEdge._

  case class FSCompileError(msg: String) extends RuntimeException(msg)

  def attrsToMap(attrs: scala.collection.Seq[Attribute]): Map[String, P.Expr] = attrs match {
    case scala.collection.Seq() => Map()
    case Attribute(Str(name), value) :: t => attrsToMap(t) + Tuple2(name, value)
  }
  
  //compile to ResourceModel.Res
  //these are the file cuttently types accepted by isPrimitiveType in PuppetEval
  def convertResource(r: Resource): ResModel = {
    val attrsMap = attrsToMap(r.attrs)
    val name: String = attrsMap.get("name") match {
      case None => r.title match {
        case Str(n) => n
        case s => throw FSCompileError(s"invalid value for resource title: $s")
      }          
      case Some(Str(n)) => n
      case e => throw FSCompileError(s"invalid value for 'name' attribute: $e")
    }
    r.typ match {
      case "file" => {
        val path: String = attrsMap.get("path") match {
          case None => r.title match {
            case Str(n) => n
            case _ => throw FSCompileError(s"invalid value for resource title: $r.title")
          }          
          case Some(Str(n)) => n
          case e => throw FSCompileError(s"invalid value for 'path' attribute: $e")
        }
        val content: String = attrsMap.get("content") match {
          case None => ""        
          case Some(Str(n)) => n
          case e => throw FSCompileError(s"invalid value for 'content' attribute: $e")
        }
        val force = attrsMap.get("force") match {
          case Some(Str("yes")) | Some(Bool(true)) => true
          case Some(Str("no")) | Some(Bool(false)) | None => false
          case e => throw FSCompileError(s"invalid value for 'force' attribute: $e")
        }
        attrsMap.get("ensure") match {
          case None => File(Paths.get(path), content, force)
          case Some(Str("present")) => File(Paths.get(path), content, force)
          case Some(Str("absent")) | Some(Bool(false)) => AbsentPath(Paths.get(path), force)
          case Some(Str("file")) => EnsureFile(Paths.get(path), content)
          case Some(Str("directory")) => Directory(Paths.get(path))
          case Some(Str("link")) => {
            attrsMap.get("target") match {
              case None => 
                throw FSCompileError(s"Missing target attribute. Target is required with ensure => link")
              case Some(Str(target)) => File(path, target, true)
              case target => throw FSCompileError(s"invalid value for 'target' attribute $target")
            }
          }
          case e => throw FSCompileError(s"invalid value for 'ensure' attribute $e")
        }
      }
      case "package" => {
        val present = attrsMap.get("ensure") match {
          case Some(Str("present")) | Some(Str("installed")) | Some(Str("latest")) => true
          case Some(Str("absent")) | Some(Str("purged")) => false
          case Some(Str("held")) => throw NotImplemented("NYI package held") // TODO
          case e => throw FSCompileError(s"invalid value for 'ensure' attribute: $e")
        }  
        Package(name, present)
      }
      case "user" => {
        val present = attrsMap.get("ensure") match {
          case Some(Str("present")) => true
          case Some(Str("absent")) => false
          case Some(Str("role")) => throw NotImplemented("NYI user role") // TODO
          case e => throw FSCompileError(s"invalid value for 'ensure' attribute: $e")
        }        
        val manageHome = attrsMap.get("managehome") match {
          case Some(Str("yes")) | Some(Bool(true)) => true
          case Some(Str("no")) | Some(Bool(false)) | None => false
          case e => throw FSCompileError(s"invalid value for 'managehome' attribute: $e")
        }        
        User(name, present, manageHome)
      }
      case "group" => {
        val present = attrsMap.get("ensure") match {
          case Some(Str("present")) => true
          case Some(Str("absent")) => false
          case e => throw FSCompileError(s"invalid value for 'ensure' attribute: $e")
        }
        Group(name, present)
      }
      case "service" => Service(name)
      case "ssh_authorized_key" => {
        val user = attrsMap.get("user") match {
          case Some(Str(s)) => s
          case e => throw FSCompileError(s"invalid value for 'user' attribute: $e")
        }
        val present = attrsMap.get("ensure") match {
          case Some(Str("present")) => true
          case Some(Str("absent")) => false
          case e => throw FSCompileError(s"invalid value for 'ensure' attribute: $e")
        }
        val key = attrsMap.get("key") match {
          case Some(Str(s)) => s
          case e => throw FSCompileError(s"invalid value for 'ensure' attribute: $e")
        }        
        SshAuthorizedKey(user, present, name, key: String)
      }
      case s => throw NotImplemented(s"Not Implemented or invalid resource type: $s")
    }
  }
  
  //use compile function in ResourceModel to go from ResModel to FS
  def toFileScriptGraph(g: ResourceGraph): FileScriptGraph = 
    nodeMap((r: Resource) => compile(convertResource(r)), g)
}
