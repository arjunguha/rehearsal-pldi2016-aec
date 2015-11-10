class IdempotenceEvaluationSuite extends org.scalatest.FunSuite {

  import rehearsal._
  import PuppetParser.parseFile

  import FSSyntax._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import rehearsal.Implicits._
  import java.nio.file.Paths
  import SymbolicEvaluator.{predEquals, exprEquals, isIdempotent}
  import PuppetSyntax._

  val root = "parser-tests/good"

  test("dhoppe-monit.pp") {
    val g = parseFile(s"$root/dhoppe-monit.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isIdempotent(g) == true)
  }

  test("dhoppe-monit_BUG.pp") {
    val g = parseFile(s"$root/dhoppe-monit_BUG.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isIdempotent(g) == true)
  }

  test("thias-bind.pp") {
    assert(parseFile(s"$root/thias-bind.pp").eval.resourceGraph
            .fsGraph("ubuntu-trusty").expr().isIdempotent() == true)
  }

  test("thias-bind.pp pruned") {
    assert(parseFile(s"$root/thias-bind.pp").eval.resourceGraph
      .fsGraph("ubuntu-trusty").expr().pruneIdem().isIdempotent() == true)
  }

  test("ssh_authorized_keys should be idempotent (regression)") {
    val manifest =
      """
      user { 'deployer':
        ensure     => present,
        managehome => true,
      }

      ssh_authorized_key { 'deployer_key':
        ensure  => present,
        key     => 'X',
        user    => 'deployer',
        require => User['deployer'],
      }
      """
    val g = PuppetParser.parse(manifest).eval.resourceGraph().fsGraph("centos-6")
    val e = g.expr()

    assert(SymbolicEvaluator.isDeterministic(g.pruneWrites()), "not deterministic")
    assert(e.pruneIdem().isIdempotent() == true, "not idempotent")
  }

  test("pdurbin-java-jpa-tutorial.pp") {
    val g = parseFile(s"$root/pdurbin-java-jpa-tutorial.pp").eval.resourceGraph.fsGraph("centos-6")
    assert(SymbolicEvaluator.isIdempotent(g) == true)
  }

  test("BenoitCattie-puppet-nginx.pp") {
    val g = parseFile(s"$root/BenoitCattie-puppet-nginx.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(SymbolicEvaluator.isIdempotent(g) == true)
  }

  test("small non-idempotent example (in FS)") {
   import FSSyntax._
    val dst = "/dst.txt"
    val src = "/src.txt"
    val e1 = If(TestFileState(dst, IsFile),
      Rm(dst) >> Cp(src, dst),
      If(TestFileState(dst, DoesNotExist),
        Cp(src, dst),
        Error))
    val e2 = If(TestFileState(src, IsFile), Rm(src), Skip)
    val e = e1 >> e2

    assert(e.isIdempotent() == false)
    assert(e.pruneIdem().isIdempotent() == false)
  }

  test("small non-idempotent example (in Puppet)"){
    val g = PuppetParser.parseFile(s"$root/non-idempotent.pp").eval.resourceGraph.fsGraph("ubuntu-trusty")
    isIdempotent(g)
    assert(isIdempotent(g) == false)

  }

}
