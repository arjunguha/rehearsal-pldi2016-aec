package equiv.ast

import java.nio.file.Path

trait TypedModel {
  // When using ScalaZ3, all these types will be Z3AST. But, the type
  // distinctions in this trait will help us keep our types straight.
  type S // The type used to represent states
  type B // The type used to represent boolean expressions
  type P // The type used to represent paths

  def trueB: B
  def falseB: B
  def andB(e1: B, e2: B): B
  def orB(e1: B, e2: B): B
  def notB(e: B): B

  def exists(path: P, state: S): B
  def isDir(path: P, state: S): B
  def isFile(path: P, state: S): B
  def isLink(path: P, state: S): B
}

trait PredModel extends TypedModel {

  def eval(pred: Predicate, state: S, paths: Map[Path, P]): B = pred match {
    case True => trueB
    case False => falseB
    case Exists(p) => exists(paths(p), state)
    case IsDir(p) => isDir(paths(p), state)
    case IsRegularFile(p) => isFile(paths(p), state)
    case IsLink(p) => isLink(paths(p), state)
    case And(lhs, rhs) => andB(eval(lhs, state, paths), eval(rhs, state, paths))
    case Or(lhs, rhs) => orB(eval(lhs, state, paths), eval(rhs, state, paths))
    case Not(p) => notB(eval(p, state, paths))
  }

}
