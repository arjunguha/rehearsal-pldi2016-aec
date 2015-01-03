package fsmodel

import java.nio.file.Path

class TypedZ3Tests extends org.scalatest.FunSuite {

  test("sanity") {
    val z = new Z3Impl
    //assert(z.z3true != z.z3false)
  }
}
