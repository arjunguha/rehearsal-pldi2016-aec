package fsmodel.optExt

import fsmodel.core

private[optExt] object Pretty {

  sealed abstract trait Cxt
  case object SeqCxt extends Cxt
  case object ConcurCxt extends Cxt
  case object AltCxt extends Cxt

  def pretty(cxt: Cxt, expr: Expr): String = expr match {
    case Error => "error"
    case Skip => "skip"
    case Filter(a) => a.toString
    case Seq(list) => {
      list.map(p => pretty(SeqCxt, p)).mkString(" >> ")
    }
    case Concur(p, q) => {
      val str = pretty(ConcurCxt, p) + " * " + pretty(ConcurCxt, q)
      cxt match {
        case SeqCxt => s"($str)"
        case ConcurCxt | AltCxt => str
      }
    }
    case Alt(set) => {
      val str = set.map(p => pretty(AltCxt, p)).mkString(" + ")
      cxt match {
        case SeqCxt | ConcurCxt => s"($str)"
        case AltCxt => str
      }
    }
    case Atomic(p) => "atomic(" + pretty(AltCxt, p) + ")"
    case CreateFile(path, hash) => s"createFile($path)"
    case Rm(path) => s"rm($path)"
    case Mkdir(path) => s"mkdir($path)"
    case Cp(src, dst) => s"cp($src, $dst)"
  }

}
