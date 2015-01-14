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
  def eq(a: Z3FileState, b: Z3FileState): Z3Bool

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
      def unary_!() = not(bool)
    }

  }

}

trait Z3Eval extends TypedZ3 {

  import Implicits._

  val z = new Z3Impl
  import z._

  def eval(expr: Expr, s1: Z3FileSystemState): Z3FileSystemState
  // = expr match {
  //   // TODO(kgeffen) scratch, untested 
  //   case Error => s1 // Should fail, maybe return a (fss which is unsat)
  //   case Skip => s1
  //   case Mkdir(path) => 
  //     // Will look something like
  //     //some z3 context . mkStore(s1, dst, isFile)
  //   case CreateFile(path, hash) => 
  //   case Cp(src, dst) => 
  //   // It would be nice to be able to do this:
  //     // testFileState(src, isFile, s1) --> testFileState(dst, isFile, s1)
  //   // But with current signatures, above is impossible, could do this
  //     // testFileState(src, isFile, s1) match
  //       // case Some(true) => eval(CreateFile(dst), s1)
  //       // case _ => eval(Error, s1)
  //     // Is almost same as regular eval
  //   case Mv(src, dst) => 
  //     // testFileState(src, isFile, s1) --> eval(Block(CreateFile(dst), Rm(src)), s1)
  //   case Rm(path) =>
  //   case Block(p, q) => 
  //   case Alt(p, q) => 
  //   case If(pred, p, q) => 
  // }

}

class Z3Impl() extends TypedZ3 {

  import z3.scala._
  import z3.scala.dsl._
  import z3.scala.dsl.Operands._

  import Implicits._

  private val cxt = new Z3Context(new Z3Config("MODEL" -> true,
                                               "TIMEOUT" -> 3000))
  private val solver = cxt.mkSolver

  private val pathSort = cxt.mkUninterpretedSort("Path")
  private val fileStateSort = cxt.mkUninterpretedSort("FileState")
  private val fileSystemStateSort = cxt.mkArraySort(pathSort, fileStateSort)

  type Z3Bool = Z3AST
  type Z3Path = Z3AST
  type Z3FileState = Z3AST
  type Z3FileSystemState = Z3AST

  val z3true = true.ast(cxt)
  val z3false = false.ast(cxt)

  val isFile = cxt.mkConst("IsFile", fileStateSort)
  val isDir = cxt.mkConst("IsDir", fileStateSort)
  val doesNotExist = cxt.mkConst("DoesNotExist", fileStateSort)

  solver.assertCnstr(cxt.mkDistinct(isFile, isDir, doesNotExist))

  private val seenPaths = collection.mutable.Map[java.nio.file.Path, Z3Path]()

  // NOTE(kgeffen) Paths made distinct in checkSAT, not here
  def path(p: java.nio.file.Path): Z3Path = {
    seenPaths.get(p) match {
      case Some(z3Path) => z3Path
      case None => {
        val z3Path = cxt.mkConst(s"Path($p)", pathSort)
        seenPaths += (p -> z3Path)
        z3Path
      }
    }
  }

  def and(a: Z3Bool, b: Z3Bool): Z3Bool = cxt.mkAnd(a, b)
  def or(a: Z3Bool, b: Z3Bool): Z3Bool = cxt.mkOr(a, b)
  def implies(a: Z3Bool, b: Z3Bool): Z3Bool = cxt.mkImplies(a, b)
  def not(a: Z3Bool): Z3Bool = cxt.mkNot(a)
  def eq(a: Z3FileState, b: Z3FileState) = cxt.mkEq(a, b)

  def checkSAT(formula: Z3Bool): Option[Boolean] = {
    solver.push
    
    // Ensure paths are distinct
    if(!seenPaths.isEmpty) {
      solver.assertCnstr(cxt.mkDistinct(seenPaths.values.toSeq: _*))
    }

    solver.assertCnstr(formula)

    val res = solver.check()
    solver.pop(1)
    res
  }

  def newState(): Z3FileSystemState = {
    cxt.mkFreshConst("FileSystemState", fileSystemStateSort)
  }

  def testFileState(path: Z3Path, fileState: Z3FileState,
                    fileSystemState: Z3FileSystemState): Z3Bool = {
    eq(fileState,
      cxt.mkSelect(fileSystemState, path)
      )
  }

}
