package fsmodel

import java.nio.file.Path

import Implicits._

object EvalR {

  type State = Map[Path, FileState]
  
  def evalR(expr: Expr, s0: State, s1: State): Boolean = expr match {
    case Error => false
    case Skip => s0 == s1
    case Mkdir(path) => !s0.contains(path) &&
                        s0.contains(path.getParent) &&
                        s0 - path == s1 - path &&
                        s1.get(path) == Some(IsDir)
    case _ => true
  }
}