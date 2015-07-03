package rehearsal

object TranslationValidation {
  import FSSyntax._

  def validate(eval: SymbolicEvaluatorImpl, precond: Precond, e1: Expr, e2: Expr): Boolean = {
    eval.buildST(precond).map(eval.stEvalExprEquals(_, e1, e2)).getOrElse(false)
  }
}
