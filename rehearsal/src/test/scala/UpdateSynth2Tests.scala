
class UpdateSynth2Tests extends org.scalatest.FunSuite {

  import java.nio.file.Paths
  import rehearsal.ppmodel._
  import ResourceModel._
  import rehearsal.fsmodel.Eval._

  test("trivial guess") {
    val upd = new UpdateSynth2(List(Paths.get("/a"), Paths.get("/b")),
                               List("hello", "bye"),
                               List(),
                               List(),
                               List())
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir))),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    info(r.toString)
    assert(r.isDefined)

  }

  test("trivial guess with a state that leads to error") {
    val upd = new UpdateSynth2(List(Paths.get("/a"), Paths.get("/b")),
                               List("hello", "bye"),
                               List(),
                               List(),
                               List())
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir)),
                       Some(Map())),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    info(r.toString)
    assert(r.isDefined)
  }

  test("trivial guess with error as input") {
    val upd = new UpdateSynth2(List(Paths.get("/a"), Paths.get("/b")),
                               List("hello", "bye"),
                               List(),
                               List(),
                               List())
    import upd._
    val r = guess(Seq(Some(Map(Paths.get("/") -> FDir)),
                       None),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    info(r.toString)
    assert(r.isDefined)
  }


}