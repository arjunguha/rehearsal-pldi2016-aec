package pipeline.main

import puppet.common._
import puppet.common.toposortperm._
import equiv.sat._
import equiv.ast._
import equiv.semantics._

import scala.collection.immutable.Stream

case class Benchmark(mainFile: String, modulePath: Option[String] = None)

object Pipeline {

  def func[T](trees: Stream[LazyTree[T]]): Stream[List[T]] = trees match {
    case x #:: xs =>  {
      val ch = func(x.children)
      (x.root :: ch.head) #:: ((ch.tail map {ls=> x.root :: ls}) ++ func(xs))
    }

    case _ => Stream(List())
  }

  def apply(mainFile: String, modulePath: Option[String] = None) {

    import puppet.driver.{PuppetDriver => driver}

    val graph = driver.toSerializable(driver.compile(driver.prepareContent(mainFile, modulePath)))

    // println("Generate toposort")
    val permtree = TopoSortPermutationLazyTree(graph)

    // println("generate list of perms")
    val perms = func(permtree)

    val z3 = new Z3Puppet

    val x = perms(0)
    val y = perms(1)

    val x_expr = Block((x.map((r) => Provider(r).toFSOps())).toSeq:_*)
    val y_expr = Block((y.map((r) => Provider(r).toFSOps())).toSeq:_*)

    println(z3.isEquiv(x_expr, y_expr))
  }
}
