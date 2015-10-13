package rehearsal

object TranslationValidation {
  import FSSyntax._
  import ResourceModel._

  def validate(eval: SymbolicEvaluatorImpl, precond: Precond, e1: Expr, e2: Expr): Boolean = {
    val state = eval.buildST(precond).map(st => eval.stateFromTerm(st).getOrElse(throw Unexpected("state is an error")))
    val st1 = state.flatMap(FSEvaluator.eval(_, e1))
    val st2 = state.flatMap(FSEvaluator.eval(_, e2))
    if (st1.isEmpty || st2.isEmpty) {
      throw Unexpected("Applying a manifest lead to an error state.")
    }
    st1.get == st2.get
  }

  def validate(eval: SymbolicEvaluatorImpl, precond: Precond,
               v1: List[Res], delta: List[Res], v2: List[Res]): Boolean = {
    val e1 = Seq(Block(v1.map(_.compile): _*), Block(v2.map(_.compile): _*))
    val e2 = Block(v2.map(_.compile): _*)
    validate(eval, precond, e1, e2)
  }
}
