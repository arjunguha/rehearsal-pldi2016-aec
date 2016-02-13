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
      case PNot(a) => countPathsPred(pred, paths)
      case PAnd(a, b) => countPathsPred(a, countPathsPred(b, paths))
      case POr(a, b) => countPathsPred(a, countPathsPred(b, paths))
      case PTestFileState(p, _) => addPath(p, paths)
      case PTrue => paths
      case PFalse => paths
    }
  }

  def countPathsExpr(expr: Expr, paths: Map[Path, Int]): Map[Path, Int] = {
    expr match {
      case EError => paths
      case ESkip => paths
      case EIf(a, e1, e2) =>
        countPathsExpr(e2, countPathsExpr(e1, countPathsPred(a, paths)))
      case ESeq(e1, e2) => countPathsExpr(e2, countPathsExpr(e1, paths))
      case EMkdir(p) => addPath(p, paths)
      case ECreateFile(p, _) => addPath(p, paths)
      case ERm(p) => addPath(p, paths)
      case ECp(src, dst) => addPath(dst, addPath(src, paths))
    }
  }

  def countPaths(expr: Expr) = countPathsExpr(expr, Map()).withDefaultValue(0)

  object CannotPrune extends RuntimeException("cannot prune")

  def findPackageLike(paths: Map[Path, Int], expr: Expr): Expr = expr match {
    case EIf(PTestFileState(p, DoesNotExist), ESeq(ECreateFile(p_, ""), body), ESkip)
      if p == p_ && paths(p) == 2 => {
      try {
        ite(testFileState(p, DoesNotExist),
          createFile(p_, "") >> pruneFiles(paths, body),
          ESkip)
      }
      catch {
        case CannotPrune => expr
      }
    }
    case ESeq(e1, e2) => findPackageLike(paths, e1) >> findPackageLike(paths, e2)
    case _ => expr
  }

  def pruneFiles(paths: Map[Path, Int], expr: Expr): Expr = expr match {
    case ECreateFile(p, _) => if (paths(p) == 1) ESkip else expr
    case EIf(PTestFileState(p, IsDir), ESkip, EMkdir(p_)) if (p == p_) => if (paths(p) == 2) ESkip else expr
    case ESeq(e1, e2) => pruneFiles(paths, e1) >> pruneFiles(paths, e2)
    case _ => throw CannotPrune
  }

  def prune(expr: Expr): Expr = findPackageLike(countPaths(expr), expr)

}
