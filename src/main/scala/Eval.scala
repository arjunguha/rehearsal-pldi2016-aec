package fsmodel

import java.nio.file.Path

object Eval {


  type State = Map[Path, FileState]

  
  // Perhaps Set[State] (may be unnecessarily complex)
  def eval(pred: Expr, s: State): List[State] = pred match {
		case Error => List()
		case Skip => List(s)
		case Mkdir(path) => path match {
			case _ if s.contains(path) => List()
			case _ if !s.contains(path.getParent) => List()
			case _ => List(s + (path -> IsDir))
		}
		// NOTE(kgeffen) File contents not yet used
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
			// If path is an occupied dir (Has any children)
			case _ if s.keys.exists(k => k.getParent == path) => List()
			case _ => List(s - path)
		}
		case Block(p1, p2) => {
			eval(p1, s).flatMap(newState => eval(p2, newState))
		}
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