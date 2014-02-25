/* Needs to be transferrable over network using an actor */
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
import poly._


trait Prop [T] {

  def v () : T
}


class StaticProp [T] (private val _v: T) extends Prop [T] {

  def v () = _v
}


class DynamicProp [T] (private val eval_script: String,
                       private val fallback: T,
                       /* TODO : Accepting function for now to compile */
                       private val f: (String => T)) extends Prop [T] {

  def v () : T = {

    (Cmd.exec (eval_script)) match {
      case (0, out, _) => f (out) /* TODO: implicit conversion to T, may restrict the kinds to T as any code cannot be translated over network */
      case (_, _, err) => fallback
    }
  }
}


class Resource (val name: String, 
                val install_method: Int /* Native / Custom */,
                val ImportConfigs: HList /* of Prop */,
                val ExportConfigs: HList /* of Prop */,
                val deps: Resource*) {

  /* TODO : Consruct a map out of deps */  
  /* TODO : Construct a map of Configs both import and export */

  def install () : Int = 0

  /* TODO : Poly Type */
  def get_prop (name: String) : String = "missing"
}
