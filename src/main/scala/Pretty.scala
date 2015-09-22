package rehearsal

private[rehearsal] object Pretty {

  import FSSyntax._

  sealed abstract trait PredCxt
  case object AndCxt extends PredCxt
  case object OrCxt extends PredCxt
  case object NotCxt extends PredCxt

  def prettyPred(cxt: PredCxt, pred: Pred): String = pred match {
    case True => "true"
    case False => "false"
    case TestFileState(p, s) => s"$s($p)"
    case Not(True) => "!true"
    case Not(False) => "!false"
    case Not(TestFileState(p, s)) => s"!$s($p)"
    case Not(a) => s"!(${prettyPred(NotCxt, a)})"
    case And(p, q) => {
      val pStr = prettyPred(AndCxt, p)
      val qStr = prettyPred(AndCxt, q)
      cxt match {
        case AndCxt | NotCxt => s"$pStr && $qStr"
        case OrCxt => s"($pStr && $qStr)"
      }
    }
    case Or(p, q) => {
      val pStr = prettyPred(OrCxt, p)
      val qStr = prettyPred(OrCxt, q)
      cxt match {
        case AndCxt => s"($pStr || $qStr)"
        case OrCxt | NotCxt => s"$pStr || $qStr"
      }
    }
    case ITE(a, b, c) => {
      val aStr = prettyPred(NotCxt, a)
      val bStr = prettyPred(NotCxt, b)
      val cStr = prettyPred(NotCxt, c)
      s"if ($aStr) { $bStr } else { $cStr }"
    }
  }

  def pretty(expr: Expr): String = expr match {
    case Error => "error"
    case Skip => "skip"
    case If(a, p, q) => s"If(${prettyPred(NotCxt, a)}, ${pretty(p)}, ${pretty(q)})"
    case Seq(p, q) => pretty(p) + " >> " + pretty(q)
    case CreateFile(path, hash) => s"createFile($path)"
    case Rm(path) => s"rm($path)"
    case Mkdir(path) => s"mkdir($path)"
    case Cp(src, dst) => s"cp($src, $dst)"
  }

}
