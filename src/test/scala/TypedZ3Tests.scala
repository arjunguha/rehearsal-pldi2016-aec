package fsmodel

import java.nio.file.Path

import Implicits._

class TypedZ3Tests extends org.scalatest.FunSuite {

	val z = new Z3Impl

  test("Z3Bools are distinct") {
    assert(z.z3true != z.z3false)
  }

  test("Z3FileStates are distinct") {
    assert(z.isFile != z.isDir)
    assert(z.isFile != z.doesNotExist)
  }

  // TODO(kgeffen) Get implicit conversion working outside of TypedZ3 file
	test("And functions correctly for Z3Bools") {
		assert(z.z3true == z.and(z.z3true, z.z3true))
		assert(z.z3false == z.and(z.z3true, z.z3false))
		assert(z.z3false == z.and(z.z3false, z.z3true))
		assert(z.z3false == z.and(z.z3false, z.z3false))
  }

  test("Or functions correctly for Z3Bools") {
		assert(z.z3false == z.or(z.z3false, z.z3false))
		assert(z.z3true == z.or(z.z3true, z.z3false))
		assert(z.z3true == z.or(z.z3false, z.z3true))
		assert(z.z3true == z.or(z.z3true, z.z3true))
  }

  test("Implies functions correctly for Z3Bools") {
		assert(z.z3false == z.implies(z.z3true, z.z3false))
		assert(z.z3true == z.implies(z.z3true, z.z3true))
		assert(z.z3true == z.implies(z.z3false, z.z3true))
		assert(z.z3true == z.implies(z.z3false, z.z3false))
  }

  test("Not works for Z3Bools") {
  	assert(z.not(z.z3true) == z.z3false)
  	assert(z.not(z.z3false) == z.z3true)
  }



}
