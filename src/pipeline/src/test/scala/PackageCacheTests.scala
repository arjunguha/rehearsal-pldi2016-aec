package pipeline

import org.scalatest.FunSuite
import org.scalatest.BeforeAndAfterAll

import java.nio.file.{Files, Path}
import scala.util.Try

class PackageCacheTestSuite extends FunSuite with BeforeAndAfterAll {

  var cacheroot: Path = _
  val dir_prefix = "pkgcache_test"

  override def beforeAll() {
    cacheroot = Files.createTempDirectory(dir_prefix)
  }

  override def afterAll() {
    val cache = new PackageCache(cacheroot)
    cache.clear()
    Try(Files.delete(cacheroot))
  }

  test("Valid package name should return set of paths") {
    val cache = new PackageCache(cacheroot)
    val pkg = "sl"
    val files = cache.files(pkg)
    cache.clear()
    assert(files.isDefined && !files.isEmpty)
  }

  test("Invalid package name should return None") {
    val cache = new PackageCache(cacheroot)
    val pkg = "fortune"
    val files = cache.files(pkg)
    assert(!files.isDefined)
    assert(!cache.entryExists(pkg))
    cache.clear()
  }

  test("cold cache should work") {
    val cache = new PackageCache(cacheroot)
    val pkg = "sl"
    assert(!cache.entryExists(pkg))
    cache.files(pkg)
    assert(cache.entryExists(pkg))
    cache.clear()
  }

  test("warm cache should work") {
    val cache = new PackageCache(cacheroot)
    val pkg = "sl"
    assert(!cache.entryExists(pkg))
    val files_cold = cache.files(pkg)
    assert(cache.entryExists(pkg))
    val files_warm = cache.read(pkg)
    assert(files_cold == files_warm)
    cache.clear()
  }
}
