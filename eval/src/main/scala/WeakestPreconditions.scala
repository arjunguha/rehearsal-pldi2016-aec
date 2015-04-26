package eval

import java.nio.file.Path
import Implicits._

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
    case Cp(f, g) => post.replace(TestFileState(g, DoesNotExist), False)
      .replace(TestFileState(g, IsFile), TestFileState(f, IsFile))
      .replace(TestFileState(g, IsDir), TestFileState(f, IsDir)) &&
      (TestFileState(g, DoesNotExist) && !TestFileState(f, DoesNotExist))
    case _ => False
  }

  def wpGraph(g: FileScriptGraph, post: Pred): Pred = {
    val finalNodes = g.nodes.filter(_.outDegree == 0).toList
    if (finalNodes.length == 0) {
      post
    }
    else {
      val pres = for (node <- finalNodes) yield {
        wpGraph(g - node, wp(node, Helpers.simplify(post)))
      }
      Helpers.simplify(And(pres: _*))
    }
  }
}
