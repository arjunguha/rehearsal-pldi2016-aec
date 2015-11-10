class FSTableTests extends org.scalatest.FunSuite with org.scalatest.Matchers {

  import rehearsal._
  import FSSyntax._
  import Implicits._
  import java.nio.file.{Paths, Path}
  import PuppetParser.parseFile

  val root = "parser-tests/good"

  test("mkdir(x) >> mkdir(y)") {
    val tbl = new FSTable()
    import tbl.dd._
    tbl.mkddExpr(Mkdir("/foo") >> Mkdir("/bar")) match {
      case Leaf(Some(map)) => {
        assert(map ==  Map[Path, FileState](Paths.get("/foo") -> IsDir, Paths.get("/bar") -> IsDir))
      }
      case other => assert(false, "got $other")
    }
  }

  test("mkdir(x) >> mkdir(x) == mkdir(x)") {
    val tbl = new FSTable()
    import tbl.dd._
    val n1 = tbl.mkddExpr(Mkdir("/foo") >> Mkdir("/foo"))
    val n2 = tbl.mkddExpr(Mkdir("/foo"))
    assert(n1 == n2)
  }

  test("disjoint predicates") {
    val tbl = new FSTable()
    import tbl.dd._
    val a = tbl.mkddPred(TestFileState("/x", IsDir))
    val e1 = tbl.mkddExpr(Mkdir("/y"))
    val n = tbl.seq(a, e1)
    println(a)
    println(e1)
    println(tbl.dd)
    println(n)
  }

  test("two resources") {
    val tbl = new FSTable()

    val e = PuppetParser.parse("""
      file {'/0': ensure => directory }
      file {'/1': ensure => directory }
      """).eval.resourceGraph.fsGraph("ubuntu-trusty").expr()
    val n = tbl.mkddExpr(e)
    info(s"cache size: ${tbl.dd.cacheSize}")
    info(tbl.dd.toString)
    info(n.toString)
  }


  test("three resources") {
    val tbl = new FSTable()

    val e = PuppetParser.parse("""
      file {'/0': ensure => directory }
      file {'/1': ensure => directory }
      file {'/2': ensure => directory }
     """).eval.resourceGraph.fsGraph("ubuntu-trusty").expr()
    tbl.mkddExpr(e)
    info(s"cache size: ${tbl.dd.cacheSize}")
  }

  ignore("large number of directories") {
    val tbl = new FSTable()

    val n = 12
    val rs = (for (x <- 0.to(n)) yield { ResourceModel.Directory(Paths.get(s"/$x")) })
    val e = Block(rs.map(_.compile("ubuntu-trusty")): _*)
    val node = tbl.mkddExpr(e)
    info(s"cache size: ${tbl.dd.cacheSize}, reachable: ${tbl.dd.gc(List(node))}")
  }


  ignore("dhoppe-monit.pp") {
    val dd = new FSTable()
    val e = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph("ubuntu-trusty").expr()
    dd.mkddExpr(e)
  }

}