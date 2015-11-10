package rehearsal

object IdempotenceOptimizer {

  import FSSyntax._
  import java.nio.file.Path
  import Implicits._

  def addPath(p: Path, paths: Map[Path, Int]): Map[Path, Int] = {
    paths.get(p) match {
      case None => paths + (p -> 1)
      case Some(n) => paths + (p -> (n + 1))
    }
  }

  def countPathsPred(pred: Pred, paths: Map[Path, Int]): Map[Path, Int] = {
    pred match {
      case Not(a) => countPathsPred(pred, paths)
      case And(a, b) => countPathsPred(a, countPathsPred(b, paths))
      case Or(a, b) => countPathsPred(a, countPathsPred(b, paths))
      case TestFileState(p, _) => addPath(p, paths)
      case True => paths
      case False => paths
    }
  }

  def countPathsExpr(expr: Expr, paths: Map[Path, Int]): Map[Path, Int] = {
    expr match {
      case Error => paths
      case Skip => paths
      case If(a, e1, e2) =>
        countPathsExpr(e2, countPathsExpr(e1, countPathsPred(a, paths)))
      case Seq(e1, e2) => countPathsExpr(e2, countPathsExpr(e1, paths))
      case Mkdir(p) => addPath(p, paths)
      case CreateFile(p, _) => addPath(p, paths)
      case Rm(p) => addPath(p, paths)
      case Cp(src, dst) => addPath(dst, addPath(src, paths))
    }
  }

  def countPaths(expr: Expr) = countPathsExpr(expr, Map()).withDefaultValue(0)

  object CannotPrune extends RuntimeException("cannot prune")

  def findPackageLike(paths: Map[Path, Int], expr: Expr): Expr = expr match {
    case If(TestFileState(p, DoesNotExist), Seq(CreateFile(p_, ""), body), Skip)
      if p == p_ && paths(p) == 2 => {
      try {
        If(TestFileState(p, DoesNotExist),
          Seq(CreateFile(p_, ""), pruneFiles(paths, body)),
          Skip)
      }
      catch {
        case CannotPrune => expr
      }
    }
    case Seq(e1, e2) => findPackageLike(paths, e1) >> findPackageLike(paths, e2)
    case _ => expr
  }

  def pruneFiles(paths: Map[Path, Int], expr: Expr): Expr = expr match {
    case CreateFile(p, _) => if (paths(p) == 1) Skip else expr
    case If(TestFileState(p, IsDir), Skip, Mkdir(p_)) if (p == p_) => if (paths(p) == 2) Skip else expr
    case Seq(e1, e2) => pruneFiles(paths, e1) >> pruneFiles(paths, e2)
    case _ => throw CannotPrune
  }

  def prune(expr: Expr): Expr = findPackageLike(countPaths(expr), expr)

}