package puppet.common

case class Tree[T](val root: T, val children: List[Tree[T]])
