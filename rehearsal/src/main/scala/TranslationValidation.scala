package rehearsal

object TranslationValidation {
  import FSSyntax._

  def validate(eval: SymbolicEvaluatorImpl, precond: Precond, e1: Expr, e2: Expr): Boolean = {
    val state = eval.buildST(precond).map(eval.stateFromTerm)
    val st1 = state.flatMap(Eval.eval(_, e1))
    val st2 = state.flatMap(Eval.eval(_, e2))
    if (st1.isEmpty || st2.isEmpty) {
      throw Unexpected("Applying a manifest lead to an error state.")
    }
    st1.get == st2.get
  }
}
