package z3analysis

import eval._

import java.nio.file.Path

object Z3Evaluator {

  def ancestors(path: Path): Set[Path] = {
    if (path.getParent == null) {
      Set(path)
    }
    else {
      ancestors(path.getParent) + path
    }
  }

  def exprPaths(expr: Expr): Set[Path] = expr match {
    case Error => Set()
    case Skip => Set()
    case If(a, p, q) => predPaths(a) union exprPaths(p) union exprPaths(q)
    case Seq(p, q) => exprPaths(p) union exprPaths(q)
    case Mkdir(f) => ancestors(f)
    case CreateFile(f, _) => ancestors(f)
    case Rm(f) => ancestors(f)
    case Cp(src, dst) => ancestors(src) union ancestors(dst)
  }

  def predPaths(pred: Pred): Set[Path] = pred match {
    case True => Set()
    case False => Set()
    case Not(a) => predPaths(a)
    case And(a, b) => predPaths(a) union predPaths(b)
    case Or(a, b) => predPaths(a) union predPaths(b)
    case TestFileState(f, _) => ancestors(f)
  }

  def graphPaths(graph: FileScriptGraph): Set[Path] = {
    graph.nodes.map(p => exprPaths(p)).flatten.toSet
  }

  def isDeterministic(pre: Pred, graph: FileScriptGraph): Boolean = {
    (new Z3Evaluator(pre, graph)).isDeterministic
  }

}

class Z3Evaluator(pre: Pred, graph: FileScriptGraph) {

  import Z3Evaluator._
  import com.microsoft.z3

  val cxt = new com.microsoft.z3.Context()
  val solver = cxt.mkSolver()

  val pathSort = cxt.mkUninterpretedSort("Path")
  val pathMap: Map[Path, com.microsoft.z3.Expr] =
    graphPaths(graph).toList.map { path =>
      path -> cxt.mkConst(path.toString, pathSort)
    }.toMap

  solver.add(cxt.mkDistinct(pathMap.values.toList: _*))

  val statSort  = cxt.mkEnumSort("Stat", "IsDir", "IsFile", "DoesNotExist")
  val Array(isDir, isFile, doesNotExist) = statSort.getConsts()
  val fileStateMap = Map[FileState, z3.Expr](IsDir -> isDir, IsFile -> isFile,
                         DoesNotExist -> doesNotExist)

  val fsSort = cxt.mkArraySort(pathSort, statSort)

  def checkPred(fs: z3.ArrayExpr, pred: Pred): z3.BoolExpr = pred match {
    case True => cxt.mkTrue()
    case False => cxt.mkFalse()
    case Not(a) => cxt.mkNot(checkPred(fs, a))
    case And(a, b) => cxt.mkAnd(checkPred(fs, a), checkPred(fs, b))
    case Or(a, b) => cxt.mkOr(checkPred(fs, a), checkPred(fs, b))
    case TestFileState(f, fileState) => {
      cxt.mkEq(fileStateMap(fileState), cxt.mkSelect(fs, pathMap(f)))
    }
  }

  def evalR(fsIn: z3.ArrayExpr, fsOut: z3.ArrayExpr, expr: Expr): z3.BoolExpr = expr match {
    case Skip => cxt.mkEq(fsIn, fsOut)
    case Error => cxt.mkBool(true) // TODO(arjun): ?
    case Seq(p, q) => {
      val fsInter = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
      cxt.mkAnd(evalR(fsIn, fsInter, p), evalR(fsInter, fsOut, q))
    }
    case If(a, p, q) => {
      cxt.mkITE(checkPred(fsIn, a),
                evalR(fsIn, fsOut, p),
                evalR(fsIn, fsOut, q)).asInstanceOf[z3.BoolExpr]
    }
    case Cp(_, _) => throw new IllegalArgumentException("not implemented")
    case Mkdir(f) =>
      cxt.mkAnd(cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f.getParent)), isDir),
                cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f)), doesNotExist),
                cxt.mkEq(fsOut, cxt.mkStore(fsIn, pathMap(f), isDir)))
    case CreateFile(f, _) =>
      cxt.mkAnd(cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f)), doesNotExist),
                cxt.mkEq(fsOut, cxt.mkStore(fsIn, pathMap(f), isFile)))
    case Rm(f) => cxt.mkAnd(cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f)), isFile),
                            cxt.mkEq(fsOut, cxt.mkStore(fsIn, pathMap(f), doesNotExist)))
  }

  def graphR(fsIn: z3.ArrayExpr, fsOut: z3.ArrayExpr,
             graph: FileScriptGraph): z3.BoolExpr = {
    val fringe = graph.nodes.filter(_.outDegree == 0).toList
    if (fringe.length == 0) {
      cxt.mkEq(fsIn, fsOut)
    }
    else if (fringe.combinations(2).forall {
               case List(a, b) => a.commutesWith(b)
             }) {
      // Create a sequence of the programs in fringe. The ridiculous foldRight,
      // which is just the identity function, is a hack to coerce the
      // inner nodes to outer nodes in ScalaGraph.
      val p = Block(fringe.foldRight(List[Expr]()) { (n, lst) => n :: lst }: _*)
      val fsInter = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
      cxt.mkAnd(evalR(fsIn, fsInter, p),
               graphR(fsInter, fsOut, graph -- fringe))
    }
    else {
      val fsInter = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
      val exprs = for (p <- fringe) yield {
        cxt.mkAnd(evalR(fsIn, fsInter, p),
                 graphR(fsInter, fsOut, graph - p))
      }
      cxt.mkOr(exprs: _*)
    }
  }

  lazy val isDeterministic: Boolean = {
    val fsIn = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
    solver.add(checkPred(fsIn, pre))
    val fsOut1 = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
    val fsOut2 = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
    println("Building first formula")
    solver.add(graphR(fsIn, fsOut1, graph))
    println("Building second formula")
    solver.add(graphR(fsIn, fsOut2, graph))
    println("Checking formula")
    solver.add(cxt.mkNot(cxt.mkEq(fsOut1, fsOut2)))
    solver.check() == z3.Status.UNSATISFIABLE
  }

}