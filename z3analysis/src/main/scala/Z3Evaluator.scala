package z3analysis

import java.nio.file.Paths
import com.microsoft.z3.{ArrayExpr, Sort}
import eval._
import bdd.Bdd

import java.nio.file.Path

object Z3Evaluator {

  def ancestors(path: Path): Set[Path] = {
    if (path.getParent == null) {
      Set(path)
    }
    else {
      Set(path, path.getParent)
      // ancestors(path.getParent) + path
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
    case ITE(a, b, c) => predPaths(a) union predPaths(b) union predPaths(c)
  }

  def graphPaths(graph: FileScriptGraph): Set[Path] = {
    graph.nodes.map(p => exprPaths(p)).flatten.toSet
  }

  def isDeterministic(bdd: Bdd[TestFileState])
    (pre: bdd.Node, graph: FileScriptGraph): Boolean = {
    (new Z3Evaluator(graph)).isDeterministic(bdd)(pre)
  }

}

class Z3Evaluator(graph: FileScriptGraph) {

  import Z3Evaluator._
  import com.microsoft.z3

  val cxt = new com.microsoft.z3.Context()
  val solver = cxt.mkSolver()

  // Z3 will segfault if the size of an array's domain is zero.
  val allPaths = (graphPaths(graph) + Paths.get("/")).toList
  val pathSort = cxt.mkUninterpretedSort("Path")

  val pathMap: Map[Path, com.microsoft.z3.Expr] =
    allPaths.map { case path =>
      path -> cxt.mkConst(path.toString, pathSort)
    }.toMap

  solver.add(cxt.mkDistinct(pathMap.values.toList: _*))

  val statSort  = cxt.mkEnumSort("Stat", "IsDir", "IsFile", "DoesNotExist")
  val Array(isDir, isFile, doesNotExist) = statSort.getConsts()
  val fileStateMap = Map[FileState, z3.Expr](IsDir -> isDir, IsFile -> isFile,
                         DoesNotExist -> doesNotExist)

  val fsSort = cxt.mkArraySort(pathSort, statSort)

  val error_ctor = cxt.mkConstructor("error", "is_error", null, null, null)
  val ok_ctor = cxt.mkConstructor("ok", "is_ok", Array[String]("ok_state"),
                                  Array[Sort](fsSort), Array(0))
  val stateSort = cxt.mkDatatypeSort("State", Array(error_ctor, ok_ctor))

  val error = cxt.mkConst(error_ctor.ConstructorDecl())
  val okDecl = ok_ctor.ConstructorDecl()

  def checkPred(fs: z3.ArrayExpr, pred: Pred): z3.BoolExpr = pred match {
    case True => cxt.mkTrue()
    case False => cxt.mkFalse()
    case Not(a) => cxt.mkNot(checkPred(fs, a))
    case And(a, b) => cxt.mkAnd(checkPred(fs, a), checkPred(fs, b))
    case Or(a, b) => cxt.mkOr(checkPred(fs, a), checkPred(fs, b))
    case TestFileState(f, fileState) => {
      cxt.mkEq(fileStateMap(fileState), cxt.mkSelect(fs, pathMap(f)))
    }
    case ITE(a, b, c) => cxt.mkITE(checkPred(fs, a),
                                   checkPred(fs, b),
                                   checkPred(fs, c)).asInstanceOf[z3.BoolExpr]

  }

  var n = 0
  def ifOK(inState: z3.Expr, outState: z3.Expr)
          (f: z3.ArrayExpr => z3.BoolExpr): z3.BoolExpr = {
    val fsIn = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
    n = n + 1
    cxt.mkITE(cxt.mkEq(inState, error),
              cxt.mkEq(outState, error),
              cxt.mkAnd(cxt.mkEq(inState, cxt.mkApp(okDecl, fsIn)),
                        f(fsIn))).asInstanceOf[z3.BoolExpr]
  }
  
  def evalR(inState: z3.Expr, outState: z3.Expr, expr: Expr): z3.BoolExpr = expr match {
    case Skip => cxt.mkEq(inState, outState)
    case Error => cxt.mkEq(outState, error)
    case Seq(p, q) => {
      val interState = cxt.mkFreshConst("fs", stateSort)
      n = n + 1
      cxt.mkAnd(evalR(inState, interState, p), evalR(interState, outState, q))
    }
    case If(a, p, q) => {
      ifOK(inState, outState) { fsIn =>
        cxt.mkITE(checkPred(fsIn, a),
                  evalR(inState, outState, p),
                  evalR(inState, outState, q)).asInstanceOf[z3.BoolExpr]
      }
    }
    case Cp(_, _) => throw new IllegalArgumentException("not implemented")
    case Mkdir(f) =>
      ifOK(inState, outState) { fsIn =>
        cxt.mkITE(cxt.mkAnd(cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f.getParent)), isDir),
                            cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f)), doesNotExist)),
                  cxt.mkEq(outState, cxt.mkApp(okDecl, cxt.mkStore(fsIn, pathMap(f), isDir))),
                  cxt.mkEq(outState, error)).asInstanceOf[z3.BoolExpr]
      }
    case CreateFile(f, _) =>
      ifOK(inState, outState) { fsIn =>
        cxt.mkITE(cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f)), doesNotExist),
                  cxt.mkEq(outState, cxt.mkApp(okDecl, cxt.mkStore(fsIn, pathMap(f), isFile))),
                  cxt.mkEq(outState, error)).asInstanceOf[z3.BoolExpr]
      }
    case Rm(f) =>
      ifOK(inState, outState) { fsIn =>
        cxt.mkITE(cxt.mkEq(cxt.mkSelect(fsIn, pathMap(f)), isFile),
                  cxt.mkEq(outState, cxt.mkApp(okDecl, cxt.mkStore(fsIn, pathMap(f), doesNotExist))),
                  cxt.mkEq(outState, error)).asInstanceOf[z3.BoolExpr]
      }
  }

  def graphR(inState: z3.Expr, outState: z3.Expr,
             graph: FileScriptGraph): z3.BoolExpr = {
    val fringe = graph.nodes.filter(_.outDegree == 0).toList
    if (fringe.length == 0) {
      cxt.mkEq(inState, outState)
    }
    else if (fringe.combinations(2).forall {
               case List(a, b) => a.commutesWith(b)
             }) {
      // Create a sequence of the programs in fringe. The ridiculous foldRight,
      // which is just the identity function, is a hack to coerce the
      // inner nodes to outer nodes in ScalaGraph.
      val p = Block(fringe.foldRight(List[Expr]()) { (n, lst) => n :: lst }: _*)
      val interState = cxt.mkFreshConst("fs", stateSort)
      cxt.mkAnd(evalR(inState, interState, p),
               graphR(interState, outState, graph -- fringe))
    }
    else {
      val interState = cxt.mkFreshConst("fs", stateSort)
      val exprs = for (p <- fringe) yield {
        cxt.mkAnd(evalR(inState, interState, p),
                 graphR(interState, outState, graph - p))
      }
      cxt.mkOr(exprs: _*)
    }
  }

  def bddToZ3Pred(myBdd: Bdd[TestFileState])(node: myBdd.Node, fs: z3.ArrayExpr): Unit = {
    import myBdd._
    val nodeToExpr = collection.mutable.Map[Node, z3.BoolExpr]()
    def helper(node: Node): z3.BoolExpr = nodeToExpr.get(node) match {
      case Some(z3Expr) => z3Expr
      case None => {
        val z3Expr = toRep(node) match {
          case Leaf(true) => cxt.mkTrue()
          case Leaf(false) => cxt.mkFalse()
          case Branch(TestFileState(f, fileState), lo, hi) => {
            cxt.mkITE(cxt.mkEq(fileStateMap(fileState), cxt.mkSelect(fs, pathMap(f))),
                      helper(hi), helper(lo))
          }
        }
        val x = cxt.mkFreshConst("fs", cxt.getBoolSort).asInstanceOf[z3.BoolExpr]
        solver.add(cxt.mkEq(x, z3Expr))
        nodeToExpr += (node -> x)
        x
      }
    }
    helper(node)
    solver.add(nodeToExpr(node))
    println(s"Precondition has size ${nodeToExpr.size}")
  }

  def isDeterministic(myBdd: Bdd[TestFileState])(pre: myBdd.Node): Boolean = {
    val fsIn = cxt.mkFreshConst("fs", fsSort).asInstanceOf[z3.ArrayExpr]
    bddToZ3Pred(myBdd)(pre, fsIn)
    assert(solver.check() == z3.Status.SATISFIABLE,
           s"precondition unsatisfiable: $pre")
    val inState = cxt.mkApp(okDecl, fsIn)
    val fsOut1 = cxt.mkFreshConst("fs", stateSort)
    val fsOut2 = cxt.mkFreshConst("fs", stateSort)
    solver.add(graphR(inState, fsOut1, graph))
    solver.add(graphR(inState, fsOut2, graph))

    solver.add(cxt.mkNot(cxt.mkEq(fsOut1, fsOut2)))
    println(s"Checking formula ($n states and ${pathMap.size} paths)...")


    val r = solver.check()
    // if (r == z3.Status.SATISFIABLE) {
    //   println(solver.getModel)
    // }
    r == z3.Status.UNSATISFIABLE
  }

}