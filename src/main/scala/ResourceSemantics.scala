package rehearsal

object ResourceSemantics {

  import Implicits._
  import PuppetSyntax2._
  import ResourceModel._

  case class FSCompileError(msg: String) extends RuntimeException(msg)

  // It is easy to forget to support an optional attribute. For example,
  // file resources can optionally take mode-attribute (to set permissions)
  // that is easy to overlook. Instead of accessing the attribute map directly,
  // we use the consume methods of this class to mark attributes read.
  // Before returning a resource, we use the assertAllUsed to ensure that
  // all attributes have been read.
  //
  // For convenience, the consume methods don't return raw attribute values.
  // Instead, they use extracts (defined in Implicits.scala) to map attribute
  // values to Scala values. For example, the Boolean extractor maps
  // the attribute-strings "yes" and "no" to true and false in Scala.
  class AttrExtractor(attrs: Map[String, Expr]) {

    import scala.collection.mutable.{Map => MutableMap}

    private val state = MutableMap[String, Expr](attrs.toSeq: _*)

    def consume[T](key: String, default: => T)(implicit extractor: Extractor2[T]): T = {
      state.get(key) match {
        case Some(v) => {
          val r = v.value[T].getOrElse(throw FSCompileError(s"unexpected value for $key"))
          state -= key
          r
        }
        case None => default
      }
    }

    def consume[T](key: String)(implicit extractor: Extractor2[T]): T = {
      consume[T](key, throw FSCompileError(s"key not found: $key"))
    }

    def unused() = state.toMap

    def assertAllUsed() = {
      if (state.isEmpty == false) {
        throw FSCompileError(s"unused attributes: $state")
      }
    }
  }

  def compile(resource: ResourceVal): Res = {
    val attrs = new AttrExtractor(resource.attrs)
    val result = resource.typ match {
      case "file" => {
        val path = attrs.consume("path", resource.title)
        val content = attrs.consume("content", "")
        val force = attrs.consume("force", false)

        attrs.consume("seltype", "") // TODO(jcollard): Explicityl ignoring seltype.
        attrs.consume("alias", "") // TODO(arjun): Does this induce edges?
        attrs.consume("group", "root")
        attrs.consume("owner", "root")
        attrs.consume("mode", "0644")
        attrs.consume("recurse", false) // TODO(arjun): necessary to model?
        attrs.consume("purge", false) // TODO(arjun): necessary to model?
        attrs.consume("source", "") // TODO(arjun): I think this is meant to be mutually exclusive with "content"

        attrs.consume("ensure", "present") match {
          case "present" => File(path, content, force)
          case "absent" => AbsentPath(path, force)
          case "file" => EnsureFile(path, content)
          case "directory" => Directory(path)
          case "link" => File(attrs.consume[String]("target"), "", true) // TODO(arjun): contents?
          case _ => throw FSCompileError("unexpected ensure value")
        }
      }
      case "package" => {
        val name = attrs.consume("name", resource.title)
        val present = attrs.consume("ensure", "present") match {
          case "present" | "installed" | "latest" => true
          case "absent" | "purged" => false
          case x => throw FSCompileError(s"inexpected ensure for package: $x")
        }
        attrs.consume("source", "")
        attrs.consume("provider", "")
        Package(name, present)
      }
      case "user" => {
        val name = attrs.consume("name", resource.title)
        val present = attrs.consume("ensure", "present") match {
          case "present" => true
          case "absent" => false
          case x => throw FSCompileError(s"unexpected ensure value: $x")
        }
        val manageHome = attrs.consume("managehome", false)
        attrs.consume("comment", "")
        attrs.consume("shell", "")
        attrs.consume("groups", "")
        User(name, present, manageHome)
      }
      case "service" => {
        val name = attrs.consume("name", resource.title)
        // TODO(arjun): Ignored attributes
        attrs.consume("hasstatus", false)
        attrs.consume("hasrestart", false)
        attrs.consume("enable", false)
        attrs.consume("ensure", "running")
        attrs.consume("restart", "")
        Service(name)
      }
      case "ssh_authorized_key" => {
        val user = attrs.consume[String]("user")
        val present = attrs.consume[String]("ensure") match {
          case "present" => true
          case "absent" => false
          case x => throw FSCompileError(s"unexpected ensure value: $x")
        }
        val key = attrs.consume[String]("key")
        val name = attrs.consume("name", resource.title)
        attrs.consume("type", "rsa") // TODO(arjun): What is the actual default type?
        SshAuthorizedKey(user, present, name, key)
      }
      case _ => throw NotImplemented(resource.toString)
    }
    attrs.assertAllUsed()
    result
  }

}
