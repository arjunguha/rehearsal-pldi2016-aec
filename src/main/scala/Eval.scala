package fsmodel

import java.nio.file.Path

object Eval {


  type State = Map[Path, FileState]

  /*
  // Perhaps Set[State] (may be unnecessarily complex)
  def eval(p: Expr, s: State): List[State] = ...

  */


}