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


trait Prop [T] {

  def v () : T
}


class StaticProp [T] (private val v: T) extends Prop [T] {

  def v () = v
}


class DynamicProp [T] (private val eval_script: String,
                       private val fallback: T) extends Prop [T] {

  def v () : T = {
    
    // TODO : Implicit conversion
    Cmd.exec (eval_script)
  }
}


class Resource (name: String, 
                install_method: /*Native/Custom*/,
                deps: Resource*) {


}
