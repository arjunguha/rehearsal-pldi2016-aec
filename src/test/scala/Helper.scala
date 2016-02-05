trait FunSuitePlus extends org.scalatest.FunSuite
  with com.typesafe.scalalogging.LazyLogging {

  import org.scalatest.Outcome

  override def withFixture(test: NoArgTest): Outcome = {
    logger.info(s"Starting test case ${test.name}")
    try {
      test()
    }
    finally {
      logger.info(s"Finished test case ${test.name}")
    }
  }

}
