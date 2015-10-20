class UpdateSynth2Tests extends org.scalatest.FunSuite {

  import java.nio.file.Paths
  import rehearsal._
  import ResourceModel._
  import UpdateSynth._
  import TranslationValidation._
  import FSEvaluator._

  val bounds = DomainBounds.empty.withPaths(Paths.get("/a"), Paths.get("/b")).withContents("hello", "bye")

  ignore("trivial guess") {
    val upd = new UpdateSynth(bounds)

    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir))),
                  List(EnsureFile("/a", "hello")),
                  List(EnsureFile("/b", "bye")))
    info(r.toString)
    assert(r.isDefined)

  }

  ignore("trivial guess with a state that leads to error") {
    val upd = new UpdateSynth(bounds)
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir)),
                       Some(Map())),
                  List(EnsureFile("/a", "hello")),
                  List(EnsureFile("/b", "bye")))
    info(r.toString)
    assert(r.isDefined)
  }

  ignore("trivial guess with error as input") {
    val upd = new UpdateSynth(bounds)
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir)),
                       None),
                  List(EnsureFile("/a", "hello")),
                  List(EnsureFile("/b", "bye")))
    info(r.toString)
    assert(r.isDefined)
  }

  ignore("synthesizing file with common prefix") {
    val m1 =
    """
      file { '/common':
        ensure => file,
        content => "things",
      }

      file { '/not':
        ensure => file,
        content => "a",
      }
    """

    val m2 =
    """
      file { '/common':
        ensure => file,
        content => "things",
      }

      file { '/not':
        ensure => file,
        content => "b",
      }
    """
    assert(exec(m1, m2) == ((PrecondTrue, List(EnsureFile("/not", "b")))))
  }

  ignore("synthesizing differences in users") {
    val m1 =
    """
      file{'/home': ensure => directory, before => User['aaron'] }

      user {'aaron':
        name => 'aaron',
        ensure => present,
        managehome => true,
      }
    """
    val m2 =
    """
      file{'/home': ensure => directory, before => User['aaron'] }

      user {'aaron':
        name => 'aaron',
        ensure => present,
        managehome => false,
      }
    """
    assert(exec(m1, m2)._2 == List(AbsentPath("/home/aaron", true)))
  }

  ignore("m1 and m2 are equivalent only when /foo and /foo/bar are directories") {
    val m1 = """
      file{'/foo': ensure => directory }
      file{'/foo/bar': ensure => directory }
      File['/foo'] -> File['/foo/bar']
    """

    val m2 = """
      file{'/foo': ensure => directory }
      file{'/foo/bar': ensure => directory }
      File['/foo/bar'] -> File['/foo']
    """

    // The precondition should be non-empty
    println(exec(m1, m2))
  }

  def testCase(name: String, r1: List[Res], r2: List[Res]) = {
    ignore(name) {
      val (eval, precond, delta) = execLists(r1, r2)
      assert(validate(eval, precond, r1, delta, r2))
    }
  }

  object AbsentPath {
    def apply(path: String, force: Boolean): Res =
      rehearsal.ResourceModel.AbsentPath(Paths.get(path), force)
  }

  object Directory {
    def apply(path: String): Res =
      rehearsal.ResourceModel.Directory(Paths.get(path))
  }

  object EnsureFile {
    def apply(path: String, contents: String): Res =
      rehearsal.ResourceModel.EnsureFile(Paths.get(path), contents)
  }


  testCase("translation validation",
           List(User("aaron", true, true)),
           List(User("aaron", true, false)))

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
           List(EnsureFile("/home/aaron/.bashrc", "some bash"),
                EnsureFile("/usr/bin/fortune", "theworst")),

           List(EnsureFile("/home/jcollard/.bashrc", "amazing bash!"),
                EnsureFile("/usr/bin/emacs", "really vim"),
                EnsureFile("/usr/bin/vim", "vim"),
                EnsureFile("/home/arjun/bin/doom", "classic binary")
    ))
}
