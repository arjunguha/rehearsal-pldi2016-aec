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
    val x = testFileState(Paths.get("/usr"), IsFile)
    assert(predEquals(x, x))
  }

  test("basic predicates") {
    val x = testFileState(Paths.get("/usr"), IsFile)
    val y = testFileState(Paths.get("/usr"), IsDir)
    assert(predEquals(x, y) == false)
  }

  test("program equivalence") {
    val x = createFile(Paths.get("/usr"), "astring")
    assert(exprEquals(x, x) == None)
  }


  test("program equivalence 2") {
    val x = createFile(Paths.get("/usr"), "astring")
    val y = createFile(Paths.get("/lib"), "astring")
    assert(exprEquals(seq(x, y), seq(y, x)) == None)
  }

  test("program equivalence 3") {
    val x = createFile(Paths.get("/usr/bin"), "astring")
    val y = createFile(Paths.get("/usr"), "astring")
    assert(exprEquals(x, y) != None)
  }

  test("program equivalence 4 - Mkdir"){
    val x = mkdir(Paths.get("/usr"))
    assert(exprEquals(x, x) == None)
  }

  test("program equivalence 5 - Mkdir") {
    val x = mkdir(Paths.get("/usr"))
    val y = createFile(Paths.get("/usr/bin"), "astring")
    assert(exprEquals(seq(x, y), seq(y, x)) != None)
  }

  test("program equivalence 6 - Mkdir"){
    val x = mkdir(Paths.get("/usr"))
    val y = mkdir(Paths.get("/lib"))
    assert(exprEquals(seq(x, y), seq(y, x)) == None)
  }

  test("program equivalence 7 - Rm"){
    val y = createFile(Paths.get("/usr"), "astring")
    val x = rm(Paths.get("/usr"))
    assert(exprEquals(seq(y, x), seq(x, y)) != None)
  }

  test("program equivalence 8 - Rm"){
    val x = createFile(Paths.get("/usr"), "astring")
    val y = createFile(Paths.get("/lib"), "astring")
    val x1 = rm(Paths.get("/usr"))
    val y1 = rm(Paths.get("/lib"))
    assert(exprEquals(seq(seq(x, y), seq(x1, y1)),
                      seq(seq(x, y), seq(y1, x1))) == None)
  }

  test("program equivalence 9 - Cp"){
    val x = createFile(Paths.get("/usr"), "a")
    val y = cp(Paths.get("/usr"), Paths.get("/lib"))
    val z = createFile(Paths.get("/lib"), "a")
    assert(exprEquals(seq(x, y), seq(x, z)) == None)
  }

  test("trivial program with non-deterministic output") {
    val g = Graph[Expr, DiEdge](ite(testFileState(Paths.get("/foo"), IsDir), mkdir(Paths.get("/bar")), Skip),
                                mkdir(Paths.get("/foo")))

    assert(isDeterministic(g) == false)
  }

  test("trivial program with non-deterministic error"){
    val g = Graph[Expr, DiEdge](mkdir("/foo"), mkdir("/foo/bar"))
    assert(isDeterministic(g) == false)
  }

  test("Is a singleton graph deterministic") {
    val g = Graph[Expr, DiEdge](ite(testFileState(Paths.get("/foo"), IsDir), Skip,
                                            mkdir(Paths.get("/foo"))))
    assert(true == isDeterministic(g))
    assert(false == isDeterministicError(g))
  }

  test("Two-node non-deterministic graph") {
    assert(false == isDeterministic(Graph[Expr, DiEdge](mkdir(Paths.get("/foo")),
      ite(testFileState(Paths.get("/foo"), IsDir), Skip, mkdir(Paths.get("/bar"))))))
  }

  test("a bug") {
    val p = Paths.get("/usr/games/sl")
    val c = ""
    val n1 = createFile(p, c)
    val n2 = ite(testFileState(p, IsFile),
      rm(p) >> createFile(p, c),
      ite(testFileState(p, DoesNotExist), createFile(p, c), Skip))
    assert(false == isDeterministic(Graph[Expr, DiEdge](n1, n2)))
  }

  test("should be deterministic") {
    val p = Paths.get("/usr/foo")
    val c = "c"
    val n = createFile(p, c)
    assert(true == isDeterministic(Graph[Expr, DiEdge](n, n)))
  }

  test("file removal and creation should be non-deterministic") {
    val p = Paths.get("/usr/foo")
    assert(false == isDeterministic(Graph[Expr, DiEdge](rm(p), createFile(p, ""))))
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
    val stmt1 = ite(testFileState(p, DoesNotExist), createFile(p, c1), rm(p) >> createFile(p, c1))
    val stmt2 = ite(testFileState(p, DoesNotExist), createFile(p, c2), rm(p) >> createFile(p, c2))
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
    val p1 = ite(testFileState("/packages/monit", DoesNotExist),
      ite(testFileState("/etc", DoesNotExist),
        mkdir("/etc"), Skip) >> ite(testFileState("/etc/monit", DoesNotExist),
        mkdir("/etc/monit"), Skip) >> createFile("/etc/monit/monitrc", "") >> createFile("/packages/monit", ""), Skip)

    val p2 = ite(testFileState("/etc/monit/conf.d", IsFile),
              rm("/etc/monit/conf.d") >> createFile("/etc/monit/conf.d", ""),
              ite(testFileState("/etc/monit/conf.d", DoesNotExist),
                createFile("/etc/monit/conf.d", ""), Error))

    val p3 = ite(testFileState("/etc/monit/conf.d/myservice", IsFile),
             rm("/etc/monit/conf.d/myservice") >> createFile("/etc/monit/conf.d/myservice", ""),
             ite(testFileState("/etc/monit/conf.d/myservice", DoesNotExist), createFile("/etc/monit/conf.d/myservice", ""), Error))


    val p = p1 >> p2 >> p3
    val s = new SymbolicEvaluatorImpl(p.paths.toList, p.hashes, Set(), None)
    println(s.exprEquals(p, Error))

  }

//    val example1 = {
//    import rehearsal.fsmodel._
//    (And(testFileState(Paths.get("/usr"), IsFile),
//      testFileState(Paths.get("/lib"), IsDir)))
//  }
//
//  val example2 = {
//    import rehearsal.fsmodel._
//    testFileState(Paths.get("/usr"), IsFile)
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
    val alpha = g.exprs(Node("file", "/alpha"))
    val beta = g.exprs(Node("file", "/beta"))
    val gamma = g.exprs(Node("file", "/alpha/gamma"))
    val delta = g.exprs(Node("file", "/beta/delta"))

    assert(alpha.commutesWith(beta))
    assert(gamma.commutesWith(delta))

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

  test("FOO") {
    val g = PuppetParser.parseFile(s"parser-tests/good/spiky-reduced.pp").eval.resourceGraph.fsGraph("centos-6").pruneWrites()
    val m = g.exprs.values.map(e => e.paths.toList.map(p => p -> 1).toMap).foldLeft(Map[java.nio.file.Path, Int]())((x, y) =>
      x.combine(y) {
        case (None, None) => None
        case (None, y) => y
        case (x, None) => x
        case (Some(x), Some(y)) => Some(x+y)
      }
    )

  }

}
