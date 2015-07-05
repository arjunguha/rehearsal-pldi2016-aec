class UpdateSynth2Tests extends org.scalatest.FunSuite {

  import java.nio.file.Paths
  import rehearsal._
  import ResourceModel._
  import UpdateSynth._
  import TranslationValidation._
  import Eval._

  val bounds = DomainBounds.empty.withPaths(Paths.get("/a"), Paths.get("/b")).withContents("hello", "bye")

  test("trivial guess") {
    val upd = new UpdateSynth(bounds)

    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir))),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    info(r.toString)
    assert(r.isDefined)

  }

  test("trivial guess with a state that leads to error") {
    val upd = new UpdateSynth(bounds)
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir)),
                       Some(Map())),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    info(r.toString)
    assert(r.isDefined)
  }

  test("trivial guess with error as input") {
    val upd = new UpdateSynth(bounds)
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir)),
                       None),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    info(r.toString)
    assert(r.isDefined)
  }

  test("synthesizing file with common prefix") {
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
    assert(exec(m1, m2) == ((PrecondTrue, List(EnsureFile(Paths.get("/not"), "b")))))
  }

  test("synthesizing differences in users") {
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
    assert(exec(m1, m2)._2 == List(AbsentPath(Paths.get("/home/aaron"), true)))
  }

  test("m1 and m2 are equivalent only when /foo and /foo/bar are directories") {
    val m1 = """
      file{'/foo': ensure => directory }
      file{'/foo/bar': ensure => directory }
      File['/foo'] ~> File['/foo/bar']
    """

    val m2 = """
      file{'/foo': ensure => directory }
      file{'/foo/bar': ensure => directory }
      File['/foo/bar'] ~> File['/foo']
    """

    // The precondition should be non-empty
    println(exec(m1, m2))
  }

  test("translation validation") {
    val r1 = List(User("aaron", true, true))
    val r2 = List(User("aaron", true, false))
    val (eval, precond, delta) = execLists(r1, r2)
    assert(validate(eval, precond, r1, delta, r2))
  }
}
