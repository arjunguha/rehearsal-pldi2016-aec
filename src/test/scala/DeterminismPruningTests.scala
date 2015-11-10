import java.nio.file.Path

import rehearsal.PuppetSyntax.FSGraph

class DeterminismPruningTests extends org.scalatest.FunSuite {
  import rehearsal._
  import Implicits._
  import FSSyntax._
  import DeterminismPruning._
  import ResourceModel._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge

  import scalax.collection.GraphPredef._


  val mydir = Directory("/mydir").compile("")
  val myfile = File("/mydir/myfile", CInline("hi"), false).compile("")

  val mydir2 = Directory("/mydir2").compile("")
  val myfile2 = File("/mydir2/myfile2", CInline("hi2"), false).compile("")

  test("directory resource ensures directory") {
    val absSt = absEval(mydir)
    assert(absSt("/mydir") == ADir)
    assert(absSt("/") == ARead)
  }

  test("file resource writes file and reads directory") {
    val absSt = absEval(myfile)
    assert(absSt("/mydir") == ARead)
    assert(absSt("/mydir/myfile") == AWrite)
    assert(absSt("/") == ARead)
  }

  test("pruning a lone file resource ") {
    val g = PuppetParser.parse(
      """
        file{"/foo": ensure => present }
      """).eval().resourceGraph().fsGraph("")
    val pruned = Slicing.sliceGraph(g)
    assert(pruned.exprs.values.head.fileSets.writes.isEmpty)
  }

  test("pruning a file resource that may commute with a directory ") {
    val absSt = join(absEval(myfile), absEval(mydir))
    val e_ = pruneExpr(Set("/mydir/myfile"), absSt, Map.empty, myfile)._2
    assert(e_ != Skip)
  }

  test("pruning a directory that may commute with a file") {
    val absSt = join(absEval(myfile), absEval(mydir))
    val e_ = pruneExpr(Set("/mydir/myfile"), absSt, Map.empty, mydir)._2
    info(mydir.toString)
    info(absEval(mydir).toString)
    assert(e_ != Skip)

  }

  test("missing dependency between file and directory") {
    val m = PuppetParser.parse("""
      file{"/dir": ensure => directory }

      file{"/dir/file": ensure => present}
                               """).eval().resourceGraph().fsGraph("")
    val pruned = Slicing.sliceGraph(m)

    info(m.toString)
    info(pruned.toString)
    info(summarizeGraph(Map(), m).toString)
    assert(SymbolicEvaluator.isDeterministic(pruned) == false)
  }

  test("2: missing deps") {
    val mydir = Directory("/mydir").compile("")
    val myfile = File("/mydir/myfile", CInline("hi"), false).compile("")

    import DeterminismPruning2._
    val g = FSGraph(Map(1 -> mydir, 2 -> myfile),
      Graph[Int, DiEdge](1, 2))
    val st = absGraph(g).map.get
    info(st.toString)
    val g_ = pruneGraph(g)
    info(g_.toString)
    assert(pruneablePaths(g) == Set("/mydir/myfile"))
  }

  test("2: slicing limitation") {
    import DeterminismPruning2._
    val g = FSGraph(Map(1 -> mydir, 2 -> myfile, 3 -> mydir2, 4 -> myfile2),
                    Graph[Int, DiEdge](1 ~> 2, 3 ~> 4))
    val st = absGraph(g).map.get
    val g_ = pruneGraph(g)
    info(g_.exprs.toString)
    assert(st("/mydir/myfile") == Known(Set(AIsFile)))
    assert(st("/mydir2/myfile2") == Known(Set(AIsFile)))
  }

  test("2: pruning packages") {
    import DeterminismPruning2._
    val e = Package("vim", true).compile("ubuntu-trusty")
    val st = absEval(e).map.get
    // /packages/vim could be file or dir
    assert(st.values.toList.filter(x => x != Known(Set(AIsDir)) && x != Known(Set(AIsFile))).length == 1)
  }

  test("2: single file") {
    import DeterminismPruning2._
    val st = absEval(File("/mydir/myfile", CInline("hi"), false).compile("")).map.get
    assert(st("/mydir/myfile") == Known(Set(AIsFile)))
  }

  test("2: file resource reduced") {
    import DeterminismPruning2._
    val p = "/mydir/myfile".toPath
    val c = "hi"
    val e = If(TestFileState(p, IsFile),
      Rm(p) >> CreateFile(p, c),
      If(TestFileState(p, DoesNotExist),
        CreateFile(p, c),
        Error))
    val st = absEval(e).map.get
    assert(st(p) == Known(Set(AIsFile)))
  }


  test("2: create file or error") {
    import DeterminismPruning2._
    val p = "/mydir/myfile".toPath
    val c = "hi"
    val e = If(TestFileState(p, DoesNotExist),
               CreateFile(p, c),
               Error)
    val st = absEval(e).map.get
    assert(st("/mydir/myfile") == Known(Set(AIsFile)))
  }

  test("2: rm(p) >> create(p)") {
    import DeterminismPruning2._
    val p = "/mydir/myfile".toPath
    val c = "hi"
    val e = Rm(p) >> CreateFile(p, c)
    val st = absEval(e).map.get
    assert(st == Map("/mydir".toPath -> Known(Set(AIsDir)),
                     "/mydir/myfile".toPath -> Known(Set(AIsFile))))
  }

}
