
class SynthTests extends org.scalatest.FunSuite {

  import java.nio.file._
  import rehearsal.Eval._
  import rehearsal.ResourceModel._
  import rehearsal.UpdateSynth._
  import rehearsal.unions
  import rehearsal.FSSyntax
  import rehearsal.FSSyntax.{Skip, Expr}


  object Directory {
    def apply(path: String): Res =
      rehearsal.ResourceModel.Directory(Paths.get(path))
  }

  object EnsureFile {
    def apply(path: String, contents: String): Res =
      rehearsal.ResourceModel.EnsureFile(Paths.get(path), contents)
  }

  val initState: Map[Path, FState] = Map(Paths.get("/") -> FDir)

  def toExpr(rs: List[Res]): Expr =
    rs.map(_.compile).foldRight[Expr](Skip)({ 
      case (ex, acc) => FSSyntax.Seq(acc, ex) 
    })

  def testCase(name: String, e1: List[Res], e2: List[Res]) = {
    test(name) {
 
      val all = e1 ++ e2

      val bounds = DomainBounds(unions(all.map(allPaths)).toList,
        unions(all.map(allContents)).toList,
        unions(all.map(allPackages)).toList,
        unions(all.map(allUsers)).toList,
        unions(all.map(allGroups)).toList) 

      val update = new UpdateSynth2(bounds)
      

      val (_, result) = update.synth(Set(), Seq(Some(initState)), e1, e2)

      val e1Expr = toExpr(e1)
      val e2Expr = toExpr(e2)
      val deltaExpr = toExpr(result)
      val finalExpr = FSSyntax.Seq(e1Expr, deltaExpr)

      //TODO(jcollard): This should really be over all states that satisfy
      // the preconditions
      val st: State = initState
     
      assert(eval(st, e2Expr) == eval(st, finalExpr))

    }
  }


  testCase("Add single file",
    List(),
    List(EnsureFile("/arjun", "chipmunk")))

  testCase("Two files",
    List(),
    List(EnsureFile("/arjun", "chipmunk"), 
      EnsureFile("/aaron", "strawberry")))

  testCase("Move to home directory",
    List(EnsureFile("/arjun", "chipmunk")),
    List(EnsureFile("/home/arjun", "chipmunk")))
 
  testCase("No change",
    List(EnsureFile("/arjun", "chipmunk")),
    List(EnsureFile("/arjun", "chipmunk")))

  testCase("Add file in sub directory",
    List(),
    List(EnsureFile("/home/jcollard", "darn")))
 

  testCase("Make several changes",

    List(Directory("/home"),
      Directory("/home/jcollard"),
      Directory("/usr"),
      Directory("/usr/bin"),
      Directory("/home/aaron"),
      EnsureFile("/home/aaron/.bashrc", "some bash"),
      EnsureFile("/usr/bin/fortune", "theworst")),

    List(EnsureFile("/home/jcollard/.bashrc", "amazing bash!"),
      EnsureFile("/usr/bin/emacs", "really vim"),
      EnsureFile("/usr/bin/vim", "vim"),
      Directory("/home/arjun/bin"),
      EnsureFile("/home/arjun/bin/doom", "classic binary")
        
    ))


}
