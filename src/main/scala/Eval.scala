package fsmodel

import java.nio.file.Path

object Eval {


  type State = Map[Path, FileState]

  
  // Perhaps Set[State] (may be unnecessarily complex)
  def eval(p: Expr, s: State): List[State] = p match {
		case Error => List(s)
		case Skip => List(s)
		case _ => List(s)
		/*
		case Block(p, q) =>
		case Alt(p, q) =>
		case If(pred, p, q) =>
		case Mkdir(path) =>
		case CreateFile(path, hash) =>
		case Rm(path) =>
		case Cp(src, dst) =>
		case Mv(src, dst) =>
		*/
  }

  


}