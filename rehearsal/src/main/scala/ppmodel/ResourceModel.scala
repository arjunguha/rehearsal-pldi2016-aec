package rehearsal.ppmodel

import java.nio.file.Path

sealed trait Res
case class File(path: Path, content: String, force: Boolean) extends Res
case class AbsentPath(path: Path, force: Boolean) extends Res
case class Directory(path: Path, force: Boolean, present: Boolean) extends Res
case class Package(name: String, present: Boolean) extends Res
case class Group(name: String, present: Boolean) extends Res
case class User(name: String, present: Boolean, manageHome: Boolean) extends Res
case class Notify(message: String) extends Res