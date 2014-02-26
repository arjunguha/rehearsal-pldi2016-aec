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


import shapeless._
import record._
import syntax.singleton._
import poly._
import HList._


/* Prop ADT */
sealed trait Prop [+T] { def v () : T }
case class StaticProp [T] (private val _v: T) extends Prop [T] { def v () = _v }

// Accepts file or command using which it evaluates the property
case class DynamicProp [T] (private val eval_script: String,
                            private val fallback: T,
                            implicit val parse: (String => T)) extends Prop [T] {

  def v () : T = {

    (Cmd.exec (eval_script)) match {
      case (0, out, _) => parse (out) /* TODO: implicit conversion to T, may restrict the kinds to T as any code cannot be translated over network */
      case (_, _, err) => fallback
    }
  }
}

case class MappedProp [T] (private val p: Prop[T]) extends Prop [T] { def v (): T = p.v () }



/////////////////////////////////////////////////////////////////////////
sealed trait InstallMethod
case object Native extends InstallMethod
case class Custom (val script: String) extends InstallMethod



object InstallResource {


  def props_to_strlst[L <: HList, Prop[_]] (props: L) : Unit = {}

  def apply[L <: HList, Prop[_]] (name: String, method: InstallMethod, props: L): Int = {
    method match {
      case Native => Cmd.exec ("apt-get install -q -y" + " " + name)._1
      case Custom (script) => Cmd.exec (script)._1 /* TODO : Convert props list to string list */
    }
  }

  def apply (name: String, method: InstallMethod): Int =
    apply (name, method, HNil)
}


  


/* TODO : Consruct a Global map out of deps, to answer certain queries */  


class Resource (val name: String, 
                val install_type: InstallMethod,
                val iconfig: HList, /* TODO : Change to maps */ /* of Prop */
                val econfig: HList, /* TODO : Change to maps */ /*of Prop */
                val deps: Resource*) {

  def install_deps (rs: Seq[Resource]) = {

    rs.foreach (x => x.install ())
  }

  def install () : Int = {

    install_deps (deps)
    InstallResource (name, install_type, iconfig)
  }

  /* TODO : Poly Type */
  def get_prop (name: String) : String = {
    "missing"
  }
}
