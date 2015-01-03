package fsmodel

trait TypedZ3 {

  type Z3Bool
  type Z3Path
  type Z3FileState
  type Z3FileSystemState

  def z3true: Z3Bool
  def z3false: Z3Bool

  def isFile: Z3FileState
  def isDir: Z3FileState
  def doesNotExist: Z3FileState

  def path(p: java.nio.file.Path): Z3Path

  def newState(): Z3FileSystemState

  def testFileState(path: Z3Path, fileState: Z3FileState,
                    fileSystemState: Z3FileSystemState): Z3Bool
  def and(a: Z3Bool, b: Z3Bool): Z3Bool
  def or(a: Z3Bool, b: Z3Bool): Z3Bool
  def implies(a: Z3Bool, b: Z3Bool): Z3Bool
  def not(a: Z3Bool): Z3Bool

  // TODO(arjun): In the implementation, remember to assert that all paths
  // are distinct before calling (check-sat)
  def checkSAT(formula: Z3Bool): Option[Boolean]

  object Implicits {

    import scala.language.implicitConversions

    implicit def boolToZ3Bool(b: Boolean): Z3Bool = {
      if (b) z3true else z3false
    }

    implicit class RichZ3Bool(bool: Z3Bool) {
      def &&(other: Z3Bool) = and(bool, other)
      def ||(other: Z3Bool) = or(bool, other)
      def -->(other: Z3Bool) = implies(bool, other)
      //def unary_!() = not(bool)
    }

  }

}

trait Z3Eval extends TypedZ3 {

  import Implicits._

  val tmp: Z3Bool = !true && false

  def eval(expr: Expr, s1: Z3FileSystemState): Z3FileSystemState

}

class Z3Impl() extends TypedZ3 {

  import z3.scala._
  import z3.scala.dsl._
  import z3.scala.dsl.Operands._


  private val cxt = new Z3Context(new Z3Config("MODEL" -> true,
                                               "TIMEOUT" -> 3000))

  private val solver = cxt.mkSolver

  private val pathSort = cxt.mkUninterpretedSort("Path")
  // (declare-sort FileState)
  private val fileStateSort = cxt.mkUninterpretedSort("FileState")

  private val fileSystemStateSort = cxt.mkUninterpretedSort("FileSystemState")

  type Z3Bool = Z3AST
  type Z3Path = Z3AST
  type Z3FileState = Z3AST
  type Z3FileSystemState = Z3AST

  val z3true = true.ast(cxt)
  val z3false = false.ast(cxt)

  // (declare-const IsFile FileState)
  val isFile = cxt.mkConst("IsFile", fileStateSort)
  val isDir = cxt.mkConst("IsDir", fileStateSort)
  val doesNotExist = cxt.mkConst("DoesNotExist", fileStateSort)

  // (distinct ...)
  solver.assertCnstr(cxt.mkDistinct(isFile, isDir, doesNotExist))

  private val seenPaths = collection.mutable.Map[java.nio.file.Path, Z3Path]()

  def path(p: java.nio.file.Path): Z3Path = {
    seenPaths.get(p) match {
      case Some(z3Path) => z3Path
      case None => {
        val z3Path = cxt.mkConst(s"Path($p)", pathSort)
        seenPaths += (p -> z3Path)
        // Note that (distinct ...) for paths is added by checkSAT()
        z3Path
      }
    }
  }

  // TODO(kgeffen) Implement
  def testFileState(path: Z3Path, fileState: Z3FileState): Z3Bool = {
    z3true
  }


  import Implicits._

  def and(a: Z3Bool, b: Z3Bool): Z3Bool = {
    a == z3true && b == z3true
  }
  def or(a: Z3Bool, b: Z3Bool): Z3Bool = {
    a == z3true || b == z3true
  }

  def implies(a: Z3Bool, b: Z3Bool): Z3Bool = {
    not(a) || b
  }
  
  def not(a: Z3Bool): Z3Bool = {
    a == z3false
  }
  
  def checkSAT(formula: Z3Bool): Option[Boolean] = {
    None
  }
  def newState(): Z3FileSystemState = {
    cxt.mkConst("FileSystemState", fileSystemStateSort)
  }

  def testFileState(path: Z3Path, fileState: Z3FileState,
                    fileSystemState: Z3FileSystemState): Z3Bool = {
    z3true
  }


}
