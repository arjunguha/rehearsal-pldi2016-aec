package cook.fingerprint

import scala.concurrent._
import scala.concurrent.duration._
import scala.async.Async.await
import ExecutionContext.Implicits.global
import org.scalatest.FunSuite

class FingerPrintSuite extends FunSuite {

  val docker_url = "http://localhost:4243"

  test("Installing a package should not fail") {
    val fp = Await.result(FingerPrint(docker_url, "apt-get install -y sl"), Duration.Inf)
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }

  test("Installing a service should not fail") {
    val fp = Await.result(FingerPrint(docker_url, "apt-get install -y apache2"), Duration.Inf)
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }

  test("Creating a file should not fail") {
    val fp = Await.result(FingerPrint(docker_url, "touch /myfile"), Duration.Inf)
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }

  test("Creating a user should not fail") {
    val fp = Await.result(FingerPrint(docker_url, "useradd foo"), Duration.Inf)
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }
}
