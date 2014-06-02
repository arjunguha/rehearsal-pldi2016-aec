package cook.fingerprint

import org.scalatest.FunSuite

class FingerPrintSuite extends FunSuite {

  val docker_url = "http://localhost:4243"

  test("Installing a package should not fail") {
    val fp = FingerPrint(docker_url, "apt-get install -y sl")
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }

  test("Installing a service should not fail") {
    val fp = FingerPrint(docker_url, "apt-get install -y apache2")
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }

  test("Creating a file should not fail") {
    val fp = FingerPrint(docker_url, "touch /myfile");
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }

  test("Creating a user should not fail") {
    val fp = FingerPrint(docker_url, "useradd foo");
    fp.foreach({case (k,v) => println("File: %s, MD5: %s".format(k,v))})
    println("----")
  }
}
