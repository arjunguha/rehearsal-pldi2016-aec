package eval

private[eval] object Pretty {

  sealed abstract trait Cxt
  case object SeqCxt extends Cxt
  case object ConcurCxt extends Cxt

  def pretty(cxt: Cxt, expr: Expr): String = expr match {
    case Error => "error"
    case Skip => "skip"
    case If(a, p, q) => s"If($a, ${pretty(cxt, p)}, ${pretty(cxt, q)})"
    case Seq(p, q) => pretty(SeqCxt, p) + " >> " + pretty(SeqCxt, q)
    case CreateFile(path, hash) => s"createFile($path)"
    case Rm(path) => s"rm($path)"
    case Mkdir(path) => s"mkdir($path)"
    case Cp(src, dst) => s"cp($src, $dst)"
  }

}
