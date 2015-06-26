package rehearsal.ppmodel

object GuessClasses {

  import puppet.syntax.{TopLevel, parse}
  import puppet.core._

  def nullaryClasses(stmt: StatementC): Seq[String] = stmt match {
    case BlockStmtC(stmts) => stmts.toSeq.flatMap(nullaryClasses _)
    case NodeC(_, stmts) => nullaryClasses(stmts)
    case VardefC(_, _, _) => Seq()
    case DefinitionC(_, _, _) => Seq()
    case HostclassC(name, args, _, _) => {
      if (args.forall(_._2.isDefined)) {
        Seq(name) // TODO(arjun): Nested classes?
      }
      else {
        Seq()
      }
    }
    case ResourceDeclC(_) => Seq()
    case ManyResourcesDeclC(_) => Seq() // TODO(arjun): Why can't this be flattened?
    case FuncAppC(_, _) => Seq()
    case FilterExprC(_, _, _) => Seq()
    case IfElseC(_, _, _) => Seq()
    case OrderResourceC(_, _, _) => Seq()
    case ResourceOverrideC(_, _, _) => Seq()
  }

  def loadableClasses(stmt: StatementC): Set[String] = nullaryClasses(stmt).toSet

  def guessLoad(topLevel: TopLevel): TopLevel = {
    val core = topLevel.desugar
    val loadable = nullaryClasses(core).toSet.toList
    val includes = loadable.flatMap(name => parse(s"include $name").items)
    TopLevel(topLevel.items ++ includes)
  }

}