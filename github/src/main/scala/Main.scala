import dispatch.github._
import scala.concurrent._
import scala.concurrent.duration._
import scala.async.Async.{async, await}
import com.typesafe.scalalogging.slf4j.LazyLogging

import ExecutionContext.Implicits.global

object Main extends App with LazyLogging {

  def puppetFiles(client : Client) : Future[Stream[GhCode]] = async {
    val repos = await(client.searchRepos("language:puppet").search())
    println(s"Got ${repos.length} repos written in Puppet")
    var i = 0
    val files = await(Future.sequence(repos.map { repo => async {
      val files = await(client.searchCode(s"repo:${repo.full_name} language:puppet").search())
      for (file <- files) {
        val url = file.html_url
                    .replace("https://github.com", "https://raw.githubusercontent.com")
                    .replace("/blob", "")
        logger.debug(url)
        println(url)
      }
      files
    } }))
    files.flatten

  }

  args match {
    case Array() => {
      println("No OAuth token provided on the command line.")
      println("Search will be faster if you authenticate.")
      Await.result(puppetFiles(BasicClient), Duration.Inf)
    }
    case Array(token) =>
      Await.result(puppetFiles(new OAuthClient(token)), Duration.Inf)
  }

}

