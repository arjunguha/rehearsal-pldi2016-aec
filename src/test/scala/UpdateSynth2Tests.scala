class UpdateSynth3Tests extends org.scalatest.FunSuite {

  import rehearsal._
  import Implicits._

  test("equivPrefix produces None on equivalent resource graphs") {
    val p1 = PuppetParser.parse("""
      file{"/foo": ensure => directory}
      file{"/foo/bar": ensure => file, require => File["/foo"]}
      """).eval().resourceGraph()

    assert(UpdateSynth2.equivPrefix(p1, p1) == None)
  }

  test("equivPrefix finds a trivial prefix that is equivalent") {
    val p1 = PuppetParser.parse("""
      file{"/foo": ensure => directory}
      file{"/foo/bar": ensure => file, require => File["/foo"]}
                                """).eval().resourceGraph()
    val p2 = PuppetParser.parse("""
      file{"/foo": ensure => directory}
      file{"/foo/bar": ensure => directory, require => File["/foo"]}
      file{"/foo/bar/baz": ensure => file, require => File["/foo/bar"]}
                                """).eval().resourceGraph()


    UpdateSynth2.equivPrefix(p2, p1) match {
      case None => assert(false)
      case Some((cex, ress)) => {
        assert(ress.map(n => p1.ress(n)) ==  p1.deps.topologicalSort().map(n => p1.ress(n)))
      }
    }
  }

  test("equivPrefix finds a trivial prefix that is equivalent (2)") {
    val p1 = PuppetParser.parse("""
      file{"/foo": ensure => directory}
      file{"/foo/bar": ensure => file, content => "Y", require => File["/foo"]}
                                """).eval().resourceGraph()
    val p2 = PuppetParser.parse("""
      file{"/foo": ensure => directory}
      file{"/foo/bar": ensure => file, content => "X", require => File["/foo"]}
                                """).eval().resourceGraph()


    UpdateSynth2.equivPrefix(p2, p1) match {
      case None => assert(false)
      case Some((cex, ress)) => {
        assert(ress.map(n => p1.ress(n)) ==  p1.deps.topologicalSort().map(n => p1.ress(n)))
      }
    }
  }






}
