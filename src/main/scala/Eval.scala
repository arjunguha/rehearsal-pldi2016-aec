package fsmodel

import java.nio.file.Path

import Implicits._

object Eval {

  type State = Map[Path, FileState]

  def eval(expr: Expr, s: State): List[State] = expr match {
    case Error => List()
    case Skip => List(s)
    case Mkdir(path) => path match {
      case _ if s.contains(path) => List()
      case _ if !s.contains(path.getParent) => List()
      case _ => List(s + (path -> IsDir))
    }
    // TODO(kgeffen) Use file contents
    case CreateFile(path, hash) => path match {
      case _ if s.contains(path) => List()
      case _ if !s.contains(path.getParent) => List()
      case _ => List(s + (path -> IsFile))
    }
    case Cp(src, dst) => s.get(src) match {
      // TODO(kgeffen) When contents are used, include contents here
      case Some(IsFile) => eval(CreateFile(dst), s)
      case _ => List()
    }
    case Mv(src, dst) => s.get(src) match {
      // TODO(kgeffen) When contents are used, include contents here
      case Some(IsFile) => eval(Block(CreateFile(dst), Rm(src)), s)
      case Some(IsDir) => {
        // NOTE(kgeffen) Creates dst first, moves all contents of src, then removes src.
        // Because move is called on all contents, any dirs contained in src will
        // move all of their children before src is removed. Move works recursively.
        val mvChildren: Seq[Expr] =
          s.keys.filter(k => k.getParent == src).map(
            k => Mv(k, dst + "/" + k.getFileName)
            ).toSeq
        val equivExprs: Seq[Expr] = Mkdir(dst) +: mvChildren :+ Rm(src)

        eval(Block(equivExprs: _*), s)
      }
      case _ => List()
    }
    case Rm(path) => path match {
      case _ if !s.contains(path) => List()
      // Fail if path is an occupied dir (Is the parent of any files)
      case _ if s.keys.exists(k => k.getParent == path) => List()
      case _ => List(s - path)
    }
    case Block(p, q) => {
      eval(p, s).flatMap(newState => eval(q, newState))
    }
    case Alt(p, q) => {
      eval(p, s) ++ eval(q, s)
    }
    case If(pred, p, q) => evalPred(pred, s) match {
      case true => eval(p, s)
      case false => eval(q, s)
    }
  }

  def evalPred(pred: Pred, s: State): Boolean = pred match {
    case True => true
    case False => false
    case And(a, b) => evalPred(a, s) && evalPred(b, s)
    case Or(a, b) =>  evalPred(a, s) || evalPred(b, s)
    case Not(a) => !evalPred(a, s)
    case TestFileState(path, expectedFileState) => s.get(path) match {
      case None => expectedFileState == DoesNotExist
      case Some(fileState) => expectedFileState == fileState
    }
  }

}
