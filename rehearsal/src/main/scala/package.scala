package rehearsal

case class NotImplemented(message: String) extends RuntimeException(message)

// Ill-formed input
case class Unexpected(message: String) extends RuntimeException(message)

case class CannotUpdate(msg: String) extends RuntimeException(msg)
