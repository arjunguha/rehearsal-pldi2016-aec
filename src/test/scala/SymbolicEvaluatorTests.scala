import rehearsal.PuppetSyntax.Node

class SymbolicEvaluator2Tests extends FunSuitePlus {

  import rehearsal._
  import FSSyntax._
  import scalax.collection.Graph
  import scalax.collection.GraphEdge.DiEdge
  import rehearsal.Implicits._
  import java.nio.file.Paths
  import SymbolicEvaluator.{predEquals, exprEquals, isDeterministic, isDeterministicError, isIdempotent}

  def comprehensiveIsDet(original: FSGraph[Node]): Boolean = {
    val contracted = original.addRoot(Node("root", "root")).contractEdges()
    val pruned = original.pruneWrites()
    val contractedAndPruned = contracted.pruneWrites()
    val expected = SymbolicEvaluator.isDeterministic(original)
    assert (SymbolicEvaluator.isDeterministic(contracted) == expected, "contracting changed result of determinism")
    assert (SymbolicEvaluator.isDeterministic(pruned) == expected, "pruning changed result of determinism")
    assert (SymbolicEvaluator.isDeterministic(contractedAndPruned) == expected, "contract; prune changed result of determinism")
    expected
  }

  def comprehensiveIdem(original: FSGraph[Node]): Boolean = {
    val expr = original.expr()
    val expected =  expr.isIdempotent()
    assert(expr.pruneIdem().isIdempotent() == expected, "pruning changed the result of idempotence")
    expected
  }

  test("Manifest that creates a user account and file in her home directory (non-deterministic)") {
    val m =
      """
        package{'vim':
          ensure => present
        }

        file{'/home/carol/.vimrc':
          content => "syntax on"
        }

        user{'carol':
          ensure => present,
          managehome => true
        }
        """

    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(comprehensiveIsDet(g) == false)
  }

  test("Manifest that creates a user account and file in her home directory (deterministic)") {
    val m =
      """
        package{'vim':
          ensure => present
        }

        file{'/home/carol/.vimrc':
          content => "syntax on"
        }

        user{'carol':
          ensure => present,
          managehome => true
        }

        User['carol'] -> File['/home/carol/.vimrc']
      """

    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(comprehensiveIsDet(g) == true)
  }

  test("Manifest that configures Apache web server (non-deterministic)") {
    val m =
      """
        file {"/etc/apache2/sites-available/000-default.conf":
          content => "dummy config",
        }
        package{"apache2": ensure => present }
      """

    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(comprehensiveIsDet(g) == false)
  }

  test("Manifest that configures Apache web server (deterministic)") {
    val m =
      """
        file {"/etc/apache2/sites-available/000-default.conf":
          content => "dummy config",
          require => Package["apache2"]
        }
        package{"apache2": ensure => present }
      """

    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(comprehensiveIsDet(g) == true)
  }

  test("Manifest with a user-account abstraction (non-deterministic)") {
    // Since we already test the body of myuser, this test only shows
    // that defined-types work correctly.
    val m =
      """
        define myuser($title) {
          user {"$title":
            ensure => present,
            managehome => true
          }
          file {"/home/${title}/.vimrc":
            content => "syntax on"
          }
        }
        myuser {"alice": }
        myuser {"carol": }
      """

    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert (comprehensiveIsDet(g) == false)
  }

  test("Manifest with a user-account abstraction (deterministic)") {
    // Since we already test the body of myuser, this test only shows
    // that defined-types work correctly.
    val m =
      """
        define myuser($title) {
          user {"$title":
            ensure => present,
            managehome => true
          }
          file {"/home/${title}/.vimrc":
            content => "syntax on"
          }
          User["$title"] -> File["/home/${title}/.vimrc"]
        }
        myuser {"alice": }
        myuser {"carol": }
      """
    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert (comprehensiveIsDet(g) == true)
  }

  test("Manifest with two modules that cannot be composed together") {
    val m =
      """
      define cpp() {
        if !defined(Package['m4']) {
          package {'m4': ensure => present }
        }
        if !defined(Package['make']) {
          package {'make': ensure => present }
        }
        package {'gcc': ensure => present }
        Package['m4'] -> Package['make']
        Package['make'] -> Package['gcc']
      }

      define ocaml() {
        if !defined(Package['m4']) {
          package {'m4': ensure => present }
        }
        if !defined(Package['make']) {
          package {'make': ensure => present }
        }
        package {'ocaml': ensure => present }
        Package['make'] -> Package['m4']
        Package['m4'] -> Package['ocaml']
      }

      cpp{"mycpp": }
      ocaml{"myocaml": }
      """
    intercept[EvalError] {
      PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    }
  }

  test("Non-idempotence with just two files") {
    val m =
      """
        file {"/dst": source => "/src" }
        file {"/src": ensure => absent }
        File["/dst"] -> File["/src"]
      """
    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(comprehensiveIsDet(g) == true)
    assert(comprehensiveIdem(g) == false)
  }

  test("User manages /etc/hosts manually and with Puppet (non-deterministic)") {
    val m =
      """
        host {"umass.edu": ip => "localhost"}
        file{"/etc/hosts": content => "my hosts"}
      """
    val g = PuppetParser.parse(m).eval.resourceGraph.fsGraph("ubuntu-trusty")
    assert(comprehensiveIsDet(g) == false)
  }

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
    val g = Graph[Expr, DiEdge](ite(testFileState(Paths.get("/foo"), IsDir), mkdir(Paths.get("/bar")), ESkip),
                                mkdir(Paths.get("/foo")))

    assert(isDeterministic(g) == false)
  }

  test("trivial program with non-deterministic error"){
    val g = Graph[Expr, DiEdge](mkdir("/foo"), mkdir("/foo/bar"))
    assert(isDeterministic(g) == false)
  }

  test("Is a singleton graph deterministic") {
    val g = Graph[Expr, DiEdge](ite(testFileState(Paths.get("/foo"), IsDir), ESkip,
                                            mkdir(Paths.get("/foo"))))
    assert(true == isDeterministic(g))
    assert(false == isDeterministicError(g))
  }

  test("Two-node non-deterministic graph") {
    assert(false == isDeterministic(Graph[Expr, DiEdge](mkdir(Paths.get("/foo")),
      ite(testFileState(Paths.get("/foo"), IsDir), ESkip, mkdir(Paths.get("/bar"))))))
  }

  test("a bug") {
    val p = Paths.get("/usr/games/sl")
    val c = ""
    val n1 = createFile(p, c)
    val n2 = ite(testFileState(p, IsFile),
      rm(p) >> createFile(p, c),
      ite(testFileState(p, DoesNotExist), createFile(p, c), ESkip))
    assert(false == isDeterministic(Graph[Expr, DiEdge](n1, n2)))
  }

  test("should be deterministic") {
    val p = Paths.get("/usr/foo")
    val c = "c"
    val n = createFile(p, c)
    assert(true == isDeterministic(Graph[Expr, DiEdge](n, n)))
  }

  test("independent rm and createFile") {
    val p = Paths.get("/usr/foo")
    val e1 = rm(p)
    val e2 = createFile(p, "")
    val g = Graph[Expr, DiEdge](e1, e2)
    assert(e1.commutesWith(e2) == false, "commutativity check is buggy")
    assert(false == isDeterministic(g))
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

  test("openssh file-set checking") {
    val g = PuppetParser.parse("""
      package {'openssh':
        ensure => latest,
      }
      """).eval.resourceGraph.fsGraph("centos-6")

    val e = g.expr()
    println(e)
    println(e.fileSets)
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

    val g2 = m.pruneWrites()

    for (x <- m.exprs) {
      println(x._2)

      println("Reads: " + x._2.fileSets.reads)
      println("Writes: " + x._2.fileSets.writes)
      println("Dirs: " + x._2.fileSets.dirs)
    }



    assert(isDeterministic(g2) == false, "pruning changed result")
    assert(isDeterministic(m) == false, "wrong result without pruning")
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

    val sets = ESeq(g_.exprs.values.toSeq: _*).fileSets
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

  test("single user") {
    val m = PuppetParser.parse(
      """
        user{"alice": managehome => true}
      """).eval.resourceGraph.fsGraph("ubuntu").pruneWrites()

    println(m.expr())
  }

  test("packages ircd-hybrid and httpd") {
    // Both packages create files in /var. When we don't force /var to be
    // a directory, this test checks that we do force / to be a directory.
    val m = PuppetParser.parse("""
      package{'ircd-hybrid': }
      package{'httpd': }
      """).eval.resourceGraph.fsGraph("centos-6").pruneWrites()

    val List(e1, e2) = m.exprs.values.toList
    assert (e1.commutesWith(e2))
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
    val List(e1, e2) = pruned.exprs.values.toList
    assert (e1.commutesWith(e2))
    assert(SymbolicEvaluator.isDeterministic(pruned) == true,
      ".commutesWith passed, but not deterministic! Very bad.")
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

//  test("In Spiky, irssi configuration files should be trivially files") {
//    import DeterminismPruning2._
//    val g = PuppetParser.parseFile(s"parser-tests/good/spiky-reduced.pp")
//      .eval.resourceGraph.fsGraph("centos-6")
//
//    val candidates = pruningCandidates2(g.exprs)
//    val collectd = Node("package", "collectd")
//    println(candidates(Node("package", "collectd")))
//  }

}
