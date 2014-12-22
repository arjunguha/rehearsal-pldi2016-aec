package fsmodel

import java.nio.file.Path

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
    case Cp(src, dst) => dst match {
      case _ if s.contains(dst) => List()
      case _ if !s.contains(dst.getParent) => List()
      case _ => s.get(src) match {
        case None => List()
        case Some(srcState) => srcState match {
          // TODO(kgeffen) This is akward, this line should not have to exist, consider refactoring
          case DoesNotExist => List()
          case IsDir => eval(Mkdir(dst), s)
          // TODO(kgeffen) When contents are used, include contents here
          case IsFile => eval(CreateFile(dst), s)
        }
      }
    }
    case Mv(src, dst) => eval(Block(Cp(src, dst), Rm(src)), s)
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
