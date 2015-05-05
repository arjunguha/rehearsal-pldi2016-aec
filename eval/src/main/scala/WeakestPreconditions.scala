package eval

import java.nio.file.Path
import Implicits._

import bdd._

object WeakestPreconditions {

  def withFileState(pred: Pred, f: Path, s: FileState): Pred = s match {
    case IsFile => pred.replace(TestFileState(f, IsFile), True)
                       .replace(TestFileState(f, IsDir), False)
                       .replace(TestFileState(f, DoesNotExist), False)
    case IsDir => pred.replace(TestFileState(f, IsDir), True)
                      .replace(TestFileState(f, IsFile), False)
                      .replace(TestFileState(f, DoesNotExist), False)
    case DoesNotExist => pred.replace(TestFileState(f, DoesNotExist), True)
                             .replace(TestFileState(f, IsDir), False)
                             .replace(TestFileState(f, IsFile), False)
  }

  def bddWithFileState(bdd: Bdd[TestFileState])(pred: bdd.Node, f: Path, s: FileState): bdd.Node = {
    import bdd._
    s match {
      case IsFile => bddRestrictAll(pred, List((TestFileState(f, IsFile), true),
                                               (TestFileState(f, IsDir), false),
                                               (TestFileState(f, DoesNotExist), false)))
      case IsDir => bddRestrictAll(pred, List((TestFileState(f, IsDir), true),
                                              (TestFileState(f, IsFile), false),
                                              (TestFileState(f, DoesNotExist), false)))
      case DoesNotExist => bddRestrictAll(pred, List((TestFileState(f, DoesNotExist), true),
                                                     (TestFileState(f, IsDir), false),
                                                     (TestFileState(f, IsFile), false)))
    }
  }

  def predToBdd(bdd: Bdd[TestFileState])(pred: Pred): bdd.Node = {
    import bdd._
    import Implicits._
    pred match {
      case True => bddTrue
      case False => bddFalse
      case TestFileState(f, s) => bddVar(TestFileState(f, s))
      case And(a, b) => predToBdd(bdd)(a) && predToBdd(bdd)(b)
      case Or(a, b) => predToBdd(bdd)(a) || predToBdd(bdd)(b)
      case Not(a) => !predToBdd(bdd)(a)
      case ITE(a, b, c) => (predToBdd(bdd)(a) && predToBdd(bdd)(b)) || (!predToBdd(bdd)(a) && predToBdd(bdd)(c))
    }
  }

  def ite(a: Pred, b: Pred, c: Pred): Pred = (a, b, c) match {
    case (a, True, False) => a
    case (a, False, True) => Not(a)
    case (a, b, False) => a && b
    case _ => ITE(a, b, c)
  }

  def bddToPred(bdd: Bdd[TestFileState])(node: bdd.Node): Pred = {
    bdd.bddFold[Pred](True, False)(node, { (l, x, r) => ite(x, l, r) })
  }

  def wpBdd(bdd: Bdd[TestFileState])(expr: Expr, post: bdd.Node): bdd.Node = {
    import bdd._
    import Implicits._
    expr match {
      case Error => bddFalse
      case Skip => post
      case If(a, p, q) => {
        val bddA = predToBdd(bdd)(a)
        (!bddA || wpBdd(bdd)(p, post)) && (bddA || wpBdd(bdd)(q, post))
      }
      case Seq(p, q) => wpBdd(bdd)(p, wpBdd(bdd)(q, post))
      case Mkdir(f) => bddWithFileState(bdd)(post, f, IsDir) &&
                       bddVar(TestFileState(f, DoesNotExist)) &&
                       bddVar(TestFileState(f.getParent(), IsDir))
      case CreateFile(f, _) => bddWithFileState(bdd)(post, f, IsFile) &&
                               bddVar(TestFileState(f, DoesNotExist)) &&
                               bddVar(TestFileState(f.getParent(), IsDir))
      case Rm(f) => bddWithFileState(bdd)(post, f, DoesNotExist) && bddVar(TestFileState(f, IsFile))
      case Cp(f, g) => bddWithFileState(bdd)(post, g, IsFile) &&
                       bddVar(TestFileState(g, DoesNotExist)) && bddVar(TestFileState(f, IsFile))
      case _ => bddFalse
    }
  }

  // Calculates the weakest-precondition for an expression yielding the desired postcondition.
  def wp(expr: Expr, post: Pred): Pred = expr match {
    case Error => False
    case Skip => post
    case If(a, p, q) => (!a || wp(p, post)) && (a || wp(q, post))
    case Seq(p, q) => wp(p, wp(q, post))
    case Mkdir(f) => withFileState(post, f, IsDir) && (TestFileState(f, DoesNotExist) &&
                                                       TestFileState(f.getParent(), IsDir))
    case CreateFile(f, _) => withFileState(post, f, IsFile) && (TestFileState(f, DoesNotExist) &&
                                                                TestFileState(f.getParent(), IsDir))
    case Rm(f) => withFileState(post, f, DoesNotExist) && TestFileState(f, IsFile)
    case Cp(f, g) => withFileState(post, g, IsFile) && (TestFileState(g, DoesNotExist) &&
                                                        TestFileState(f, IsFile))
    case _ => False
  }

  def wpGraphBdd(bdd: Bdd[TestFileState])(g: FileScriptGraph, post: bdd.Node): bdd.Node = {
    import bdd.Implicits._
    val finalNodes = g.nodes.filter(_.outDegree == 0).toList
    if (finalNodes.length == 0) {
      post
    } else if (finalNodes.combinations(2).forall { case List(a, b) => a.commutesWith(b) }) {
      val pred = finalNodes.foldRight(post){ (node, pred) => wpBdd(bdd)(node, pred) }
      wpGraphBdd(bdd)(g -- finalNodes, pred)
    } else {
      val preds = for (node <- finalNodes) yield {
        wpGraphBdd(bdd)(g - node, wpBdd(bdd)(node, post))
      }
      preds.foldRight[bdd.Node](bdd.bddTrue) { (x, y) => x && y }
    }
  }

  def wpGraph(g: FileScriptGraph, post: Pred): Pred = {
    val myBdd = bdd.Bdd[TestFileState]((x, y) => (x, y) match {
      case (TestFileState(f, _), TestFileState(g, _)) => f.toString < g.toString
    })
    bddToPred(myBdd)(wpGraphBdd(myBdd)(g, predToBdd(myBdd)(post)))
  }

}
