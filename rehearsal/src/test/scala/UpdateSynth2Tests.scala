
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
    val r = guess(Map(Paths.get("/") -> FDir),
                  List(EnsureFile(Paths.get("/a"), "hello")),
                  List(EnsureFile(Paths.get("/b"), "bye")))
    println(r)

  }

}