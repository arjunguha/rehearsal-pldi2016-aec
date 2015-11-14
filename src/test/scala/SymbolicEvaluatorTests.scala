import rehearsal.PuppetSyntax.Node

class SymbolicEvaluator2Tests extends org.scalatest.FunSuite {

  import rehearsal._
  import FSSyntax._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import rehearsal.Implicits._
  import java.nio.file.Paths
  import SymbolicEvaluator.{predEquals, exprEquals, isDeterministic, isDeterministicError, isIdempotent}

  test("simple equality") {
    val x = TestFileState(Paths.get("/usr"), IsFile)
    assert(predEquals(x, x))
  }

  test("basic predicates") {
    val x = TestFileState(Paths.get("/usr"), IsFile)
    val y = TestFileState(Paths.get("/usr"), IsDir)
    assert(predEquals(x, y) == false)
  }

  test("program equivalence") {
    val x = CreateFile(Paths.get("/usr"), "astring")
    assert(exprEquals(x, x) == None)
  }


  test("program equivalence 2") {
    val x = CreateFile(Paths.get("/usr"), "astring")
    val y = CreateFile(Paths.get("/lib"), "astring")
    assert(exprEquals(Seq(x, y), Seq(y, x)) == None)
  }

  test("program equivalence 3") {
    val x = CreateFile(Paths.get("/usr/bin"), "astring")
    val y = CreateFile(Paths.get("/usr"), "astring")
    assert(exprEquals(x, y) != None)
  }

  test("program equivalence 4 - Mkdir"){
    val x = Mkdir(Paths.get("/usr"))
    assert(exprEquals(x, x) == None)
  }

  test("program equivalence 5 - Mkdir") {
    val x = Mkdir(Paths.get("/usr"))
    val y = CreateFile(Paths.get("/usr/bin"), "astring")
    assert(exprEquals(Seq(x, y), Seq(y, x)) != None)
  }

  test("program equivalence 6 - Mkdir"){
    val x = Mkdir(Paths.get("/usr"))
    val y = Mkdir(Paths.get("/lib"))
    assert(exprEquals(Seq(x, y), Seq(y, x)) == None)
  }

  test("program equivalence 7 - Rm"){
    val y = CreateFile(Paths.get("/usr"), "astring")
    val x = Rm(Paths.get("/usr"))
    assert(exprEquals(Seq(y, x), Seq(x, y)) != None)
  }

  test("program equivalence 8 - Rm"){
    val x = CreateFile(Paths.get("/usr"), "astring")
    val y = CreateFile(Paths.get("/lib"), "astring")
    val x1 = Rm(Paths.get("/usr"))
    val y1 = Rm(Paths.get("/lib"))
    assert(exprEquals(Seq(Seq(x, y), Seq(x1, y1)),
                      Seq(Seq(x, y), Seq(y1, x1))) == None)
  }

  test("program equivalence 9 - Cp"){
    val x = CreateFile(Paths.get("/usr"), "a")
    val y = Cp(Paths.get("/usr"), Paths.get("/lib"))
    val z = CreateFile(Paths.get("/lib"), "a")
    assert(exprEquals(Seq(x, y), Seq(x, z)) == None)
  }

  test("trivial program with non-deterministic output") {
    val g = Graph[Expr, DiEdge](If(TestFileState(Paths.get("/foo"), IsDir), Mkdir(Paths.get("/bar")), Skip),
                                Mkdir(Paths.get("/foo")))

    assert(isDeterministic(g) == false)
  }

  test("trivial program with non-deterministic error"){
    val g = Graph[Expr, DiEdge](Mkdir("/foo"), Mkdir("/foo/bar"))
    assert(isDeterministic(g) == false)
  }

  test("Is a singleton graph deterministic") {
    val g = Graph[Expr, DiEdge](If(TestFileState(Paths.get("/foo"), IsDir), Skip,
                                            Mkdir(Paths.get("/foo"))))
    assert(true == isDeterministic(g))
    assert(false == isDeterministicError(g))
  }

  test("Two-node non-deterministic graph") {
    assert(false == isDeterministic(Graph[Expr, DiEdge](Mkdir(Paths.get("/foo")),
      If(TestFileState(Paths.get("/foo"), IsDir), Skip, Mkdir(Paths.get("/bar"))))))
  }

  test("a bug") {
    val p = Paths.get("/usr/games/sl")
    val c = ""
    val n1 = CreateFile(p, c)
    val n2 = If(TestFileState(p, IsFile),
      Rm(p) >> CreateFile(p, c),
      If(TestFileState(p, DoesNotExist), CreateFile(p, c), Skip))
    assert(false == isDeterministic(Graph[Expr, DiEdge](n1, n2)))
  }

  test("should be deterministic") {
    val p = Paths.get("/usr/foo")
    val c = "c"
    val n = CreateFile(p, c)
    assert(true == isDeterministic(Graph[Expr, DiEdge](n, n)))
  }

  test("file removal and creation should be non-deterministic") {
    val p = Paths.get("/usr/foo")
    assert(false == isDeterministic(Graph[Expr, DiEdge](Rm(p), CreateFile(p, ""))))
  }

  test("package with config file non-deterministic graph") {
    val program = """
      file {'/usr/games/sl': ensure => present, content => "something"}
      package {'sl': ensure => present }
                  """
    val g = PuppetParser.parse(program).eval().resourceGraph().fsGraph("ubuntu-trusty")
    assert(false == isDeterministic(g))
  }

  test("should be non-deterministic") {
    info("Should work")
    val p = Paths.get("/usr/foo")
    val c1 = "contents 1"
    val c2 = "contents 2"
    val stmt1 = If(TestFileState(p, DoesNotExist), CreateFile(p, c1), Rm(p) >> CreateFile(p, c1))
    val stmt2 = If(TestFileState(p, DoesNotExist), CreateFile(p, c2), Rm(p) >> CreateFile(p, c2))
    assert(false == isDeterministic(Graph[Expr, DiEdge](stmt1, stmt2)))
  }

  test("service") {
    val program = """
      file {'/foo': ensure => directory}
      file {'/foo/bar': ensure => file, before => Service['foo'] }
      service {'foo':}
                  """
    val g = PuppetParser.parse(program).eval().resourceGraph().fsGraph("ubuntu-trusty")
    val exprs = g.exprs.values.toArray
    println(s"${exprs(0)}")
    println(s"${exprs(1)}")
    println(s"${exprs(2)}")
    println(exprs(0).fileSets)
    println(exprs(2).fileSets)
    assert(false == isDeterministic(g))
  }

  test("blah") {
    val program = """
      file {'/foo': ensure => directory}
      file {'/foo/bar': ensure => file, before => File['/etc/foo'] }
      file {'/etc/foo': ensure => file}
                  """
    val g = PuppetParser.parse(program).eval().resourceGraph().fsGraph("ubuntu-trusty")
    assert(false == isDeterministic(g))
  }

  // TODO(arjun): not a test case
  ignore("createFile should check that parent is a directory") {
    val p1 = If(TestFileState("/packages/monit", DoesNotExist),
      If(TestFileState("/etc", DoesNotExist),
        Mkdir("/etc"), Skip) >> If(TestFileState("/etc/monit", DoesNotExist),
        Mkdir("/etc/monit"), Skip) >> CreateFile("/etc/monit/monitrc", "") >> CreateFile("/packages/monit", ""), Skip)

    val p2 = If(TestFileState("/etc/monit/conf.d", IsFile),
              Rm("/etc/monit/conf.d") >> CreateFile("/etc/monit/conf.d", ""),
              If(TestFileState("/etc/monit/conf.d", DoesNotExist),
                CreateFile("/etc/monit/conf.d", ""), Error))

    val p3 = If(TestFileState("/etc/monit/conf.d/myservice", IsFile),
             Rm("/etc/monit/conf.d/myservice") >> CreateFile("/etc/monit/conf.d/myservice", ""),
             If(TestFileState("/etc/monit/conf.d/myservice", DoesNotExist), CreateFile("/etc/monit/conf.d/myservice", ""), Error))


    val p = p1 >> p2 >> p3
    val s = new SymbolicEvaluatorImpl(p.paths.toList, p.hashes, Set(), None)
    println(s.exprEquals(p, Error))

  }

//    val example1 = {
//    import rehearsal.fsmodel._
//    (And(TestFileState(Paths.get("/usr"), IsFile),
//      TestFileState(Paths.get("/lib"), IsDir)))
//  }
//
//  val example2 = {
//    import rehearsal.fsmodel._
//    TestFileState(Paths.get("/usr"), IsFile)
//
//  }

  test("slicing regression: thias-bind-buggy") {
    val m = PuppetParser.parse(
      """
        package { 'bind': ensure => installed }

        service { 'named':
            require   => Package['bind'],
            hasstatus => true,
            enable    => true,
            ensure    => running,
            restart   => '/sbin/service named reload',
        }

        file { "/var/named":
            require => Package['bind'],
            ensure  => directory,
            owner   => 'root',
            group   => 'named',
            mode    => '0770',
            seltype => 'named_log_t',
        }

          file { "/var/named/example.com":
              content => "lol",
              notify  => Service['named'],
          }
      """).eval().resourceGraph().fsGraph("centos-6")

    assert(isDeterministic(m.pruneWrites()) == false, "slicing changed the result of determinism")
  }

  test("openssh class from SpikyIRC benchmark") {
    val m = PuppetParser.parse("""
      package {'openssh':
        ensure => latest,
      }

      service {'sshd':
        ensure     => running,
        enable     => true,
      }

      file {'sshd_config':
        ensure => present,
        path   => '/etc/ssh/sshd_config',
        mode   => '0600',
        owner  => 'root',
        group  => 'root',
        source => 'puppet:///modules/ssh/sshd_config',
        notify => Service['sshd'],
      }
    """).eval().resourceGraph().fsGraph("centos-6")

    val r1 = isDeterministic(m)
    val r2 = isDeterministic(m.pruneWrites())
    assert(r1 == r2)
    assert(r2 == false)
  }

  test("missing dependency between file and directory") {
    val m = PuppetParser.parse("""
      file{"/dir": ensure => directory }

      file{"/dir/file": ensure => present}
      """).eval().resourceGraph().fsGraph("centos-6")

    assert(isDeterministic(m) == false, "should be non-deterministic")
    assert(isDeterministic(m.pruneWrites()) == false,
           "slicing removed nondeterminism")
  }

  test("pdurbin-java-jpa reduced") {
    // This test illustrates a subtle issue with the way we model package vs. file resources. We have packages
    // create their entire directory tree, but files do not (and should not). In this example, the vim-enhanced
    // package creates a file in /etc. So, if it runs first, it creates the /etc directory. But, if the file
    // /etc/inittab runs first, it will signal an error if /etc does not exist.
    val m = PuppetParser.parse(
      """
         file {"/etc/inittab":
            content => "my contents"
          }
        package{"vim-enhanced": }
      """).eval.resourceGraph.fsGraph("centos-6")
    assert(isDeterministic(m) == true)
  }

  test("slicing limitation") {
    val g = PuppetParser.parse(
      """
        file{"/alpha": ensure => directory}
        file{"/alpha/gamma": content => "dummy", require => File["/alpha"]}
        file{"/beta": ensure => directory}
        file{"/beta/delta": content => "dummy", require => File["/beta"]}
      """).eval().resourceGraph().fsGraph("ubuntu-trusty")
    val g_ = g.pruneWrites()

    val sets = Block(g_.exprs.values.toSeq: _*).fileSets
    val writes = sets.writes ++ sets.dirs
    assert(writes.contains("/alpha/gamma") == false)
    assert(writes.contains("/beta/delta") == false)
    assert(SymbolicEvaluator.isDeterministic(g_))
  }

  test("two independent packages") {
    val m = PuppetParser.parse(
      """
          $packages_to_install = [
            'unzip',
            'vim-enhanced',
          ]

          package { $packages_to_install:
            ensure => installed,
          }

            """).eval.resourceGraph.fsGraph("centos-6")
    val pruned = m.pruneWrites()
    assert(SymbolicEvaluator.isDeterministic(pruned) == true)
  }

  test("java-reduced-less") {
    val m = PuppetParser.parse(
      """
  $packages_to_install = [
    'unzip',
    'ant',
  ]

  package { $packages_to_install:
    ensure => installed,
  }

  file { '/otherb':
    content => "foobar"
  }

      """.stripMargin).eval.resourceGraph.fsGraph("centos-6")
    val pruned = m.pruneWrites()
    assert(SymbolicEvaluator.isDeterministic(pruned) == true)
  }
}
