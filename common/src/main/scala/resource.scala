/* TODO : Check that everythings Needs to be transferrable over network using an actor, that is reconstructable as it is over network */
/* Generics across network!! */

/* resource can be installed natively or customly */
/* will follow graph like directory structure */
/* Need to specify custom install or native */
/* type of script lets say would be setup.sh */
/* import property map */
/* Export property map */
/* Props : trait map -> Prop [T] */
/* Dependency Type */

/* Can pass properties to shell script using command line parameters */
/* But how to link generic shell script execution with command line parameters that can be derived from properties */


/*
import shapeless._
import record._
import syntax.singleton._
import poly._
import HList._
import shapeless.ops.record._
*/
import scala.collection._


/* Prop ADT */
/* TODO : Maybe overriding toString is a better choice */
sealed trait Prop [+T] { def v () : T }
case class StaticProp [T] (private val _v: T) extends Prop [T] { def v () = _v }

// Accepts file or command using which it evaluates the property
case class DynamicProp [T] (private val eval_script: String,
                            private val fallback: T,
                            implicit val parse: (String => T)) extends Prop [T] {

  def v () : T = {

    (Cmd.exec (eval_script)) match {
      case (0, out, _) => parse (out)
      case (_, _, err) => fallback
    }
  }
}

case class MappedProp [T] (private val p: Prop[T]) extends Prop [T] { def v (): T = p.v () }



/////////////////////////////////////////////////////////////////////////
sealed trait InstallMethod
case object Native extends InstallMethod
case class Custom (val script: String) extends InstallMethod


// TODO : Encapsulate config in a config class

object InstallResource {

  // TODO : Define
  // def props_to_strlst[L <: HList, Prop[_]] (props: L) : Unit = {}

  def props_to_strlst (props : Map[String, Prop[_]]) : List[String] = 
    props.toList.map { case (k,p) => k + ":" + p.v ()}

  def apply (name: String, method: InstallMethod, props: Map[String, Prop[_]]): Int = {
    method match {
      case Native => Cmd.exec ("apt-get install -q -y" + " " + name)._1
      case Custom (script) => Cmd.exec (script + " " + 
                                        (props_to_strlst (props)).foldLeft (" ") (_ + _)
                                       )._1
    }
  }

  def apply (name: String, method: InstallMethod): Int =
    apply (name, method, Map.empty)
}


class Resource (val name: String, 
                private val install_type: InstallMethod,
                private val iconfig: /* HList */ Map[String, Prop[String]], 
                private val econfig: /* HList */ Map[String, Prop[String]], 
                private val deps: Resource*) {

  def install_deps (rs: Seq[Resource]) = {

    rs.foreach (x => x.install ())
  }

  def install () : Int = {

    install_deps (deps)
    InstallResource (name, install_type, iconfig)
  }

  // TODO : Get this out
  def get_prop (name: String) : Option[Prop[String]] = {
    (econfig get name)
  }
}
