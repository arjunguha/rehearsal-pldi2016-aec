package fsmodel.ext

import fsmodel.core

private[ext] object Pretty extends org.kiama.output.PrettyPrinter {

  sealed abstract trait Cxt
  case object SeqCxt extends Cxt
  case object ConcurCxt extends Cxt
  case object AltCxt extends Cxt

  def toDoc(cxt: Cxt, expr: Expr): Doc = expr match {
    case Error => "error"
    case Skip => "skip"
    case Filter(a) => a.toString
    case Seq(p, q) => toDoc(SeqCxt, p) <+> ">>" </> toDoc(SeqCxt, q)
    case Concur(p, q) => {
      val doc = toDoc(ConcurCxt, p) <+> "*" </> toDoc(ConcurCxt, q)
      cxt match {
        case SeqCxt => parens(group(doc))
        case ConcurCxt | AltCxt => doc
      }
    }
    case Alt(p, q) => {
      val doc = toDoc(AltCxt, p) <+> "+" </> toDoc(AltCxt, q)
      cxt match {
        case SeqCxt | ConcurCxt =>  parens(group(doc))
        case AltCxt => doc
      }
    }
    case Atomic(p) => "atomic" <> parens(group(toDoc(AltCxt, p)))
    case CreateFile(path, hash) => s"createFile($path)"
    case Rm(path) => s"rm($path)"
    case Mkdir(path) => s"mkdir($path)"
    case Cp(src, dst) => s"cp($src, $dst)"
  }

  def pretty(expr: Expr): String = pretty(toDoc(AltCxt, expr), 80)

}
