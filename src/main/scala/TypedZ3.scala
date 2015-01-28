package fsmodel

trait TypedZ3 {

  // NOTE(kgeffen) Used to define equals method which will take any
  // of the types specified below
  type Z3Data

  type Z3Bool <: Z3Data
  type Z3Path <: Z3Data
  type Z3FileState <: Z3Data
  type Z3FileSystemState <: Z3Data

  def z3true: Z3Bool
  def z3false: Z3Bool

  def isFile: Z3FileState
  def isDir: Z3FileState
  def doesNotExist: Z3FileState

  def path(p: java.nio.file.Path): Z3Path

  def newState(): Z3FileSystemState
  def newBool(): Z3Bool

  def testFileState(path: Z3Path, fileState: Z3FileState,
                    fileSystemState: Z3FileSystemState): Z3Bool
  def and(a: Z3Bool, b: Z3Bool): Z3Bool
  def or(a: Z3Bool, b: Z3Bool): Z3Bool
  def implies(a: Z3Bool, b: Z3Bool): Z3Bool
  def not(a: Z3Bool): Z3Bool

  def eq(a: Z3Data, b: Z3Data): Z3Bool

  def checkSAT(formula: Z3Bool): Option[Boolean]

  def setFileState(path: Z3Path, fileState: Z3FileState,
                   fileSystemState: Z3FileSystemState): Z3FileSystemState

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

object Z3Eval {

  val z = new Z3Impl
  import z._
  import Implicits._ 

  val tmp: Z3Bool = !z3true && false

  def evalR(expr: Expr, s0: Z3FileSystemState, s1: Z3FileSystemState): Z3Bool = expr match {
    case Error => z3false
    case Skip => z.eq(s0, s1)
    // case Mkdir(dst) => {
    //   val foo = path(dst)
    //   checkSAT(testFileState(foo, newState, doesNotExist))
    //   //the above does not error, but also doesnt do what's wanted

    //   // z.checkSAT(
    //   //   z.testFileState(foo, s0, z.doesNotExist)
    //   //   )
    //   // //testFileState(path(dst), isDir, s1) // test nothing else has changed
    //   // )
    // }
    
    //checkSAT(eq(s0, s1)) // This might be wrong, maybe eq(s0, s1) and different sig
    // case Mkdir(dst) => Some(true)
    // {
    //   testFileState(path(dst), doesNotExist, s0) &&
    //   testFileState(path(dst.getParent), isDir, s0) &&
    //   cxt.mkStore(s0, path(dst), doesNotExist) == cxt.mkStore(s1, path(dst), doesNotExist) &&
    //   cxt.mkSelect(s1, isDir)
    // } // Maybe should all use checksat
    case _ => z3false
  }

}

class Z3Impl() extends TypedZ3 {

  import z3.scala._
  import z3.scala.dsl._
  import z3.scala.dsl.Operands._

  import Implicits._

  private val cxt = new Z3Context(new Z3Config("MODEL" -> true,
                                               "TIMEOUT" -> 3000))
  private val solver = cxt.mkSolver

  private val boolSort = cxt.mkBoolSort
  private val pathSort = cxt.mkUninterpretedSort("Path")
  private val fileStateSort = cxt.mkUninterpretedSort("FileState")
  private val fileSystemStateSort = cxt.mkArraySort(pathSort, fileStateSort)

  type Z3Data = Z3AST
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

  def eq(a: Z3Data, b: Z3Data) = cxt.mkEq(a, b)

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

  def newBool(): Z3Bool = {
    cxt.mkFreshConst("Bool", boolSort)
  }

  def testFileState(path: Z3Path, fileState: Z3FileState,
                    fileSystemState: Z3FileSystemState): Z3Bool = {
    eq(fileState,
      cxt.mkSelect(fileSystemState, path)
      )
  }

  def setFileState(path: Z3Path, fileState: Z3FileState,
                   fileSystemState: Z3FileSystemState): Z3FileSystemState = {
    cxt.mkStore(fileSystemState, path, fileState)
  }

}
