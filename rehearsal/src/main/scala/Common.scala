package rehearsal

case class NotImplemented(message: String) extends RuntimeException(message)
case class Unsupported(message: String) extends RuntimeException(message)
case class Unexpected(message: String) extends RuntimeException(message)