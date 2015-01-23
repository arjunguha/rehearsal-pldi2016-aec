package fsmodel

import java.nio.file.Path

import Implicits._

object EvalR {

  type State = Map[Path, FileState]

  // TODO(kgeffen) When file contents used, include throughout
  def evalR(expr: Expr, s0: State, s1: State): Boolean = expr match {
    case Error => false
    case Skip => s0 == s1
    case Mkdir(path) => !s0.contains(path) &&
                        s0.contains(path.getParent) &&
                        s0 - path == s1 - path &&
                        s1.get(path) == Some(IsDir)
    case CreateFile(path, hash) => !s0.contains(path) &&
                                   s0.contains(path.getParent) &&
                                   s0 - path == s1 - path &&
                                   s1.get(path) == Some(IsFile)
    case Cp(src, dst) => s0.get(src) == Some(IsFile) &&
                         evalR(CreateFile(dst), s0, s1)
    case Mv(src, dst) => s0.get(src) match {
      case Some(IsFile) => evalR(Block(CreateFile(dst), Rm(src)), s0, s1)
      // Fail if dst is within src; cannot move dir inside itself
      case Some(IsDir) if dst.startsWith(src) => false
      case Some(IsDir) => {
        // NOTE(kgeffen) Creates dst first, moves all contents of src, then removes src.
        // Because move is called on all contents, any dirs contained in src will
        // move all of their children before src is removed. Move works recursively.
        // NOTE(kgeffen) Code is nearly identical to corresponding case in Eval.scala
        val mvChildren: Seq[Expr] =
          s0.keys.filter(k => k.getParent == src).map(
            k => Mv(k, dst + "/" + k.getFileName)
            ).toSeq
        val equivExprs: Seq[Expr] = Mkdir(dst) +: mvChildren :+ Rm(src)

        evalR(Block(equivExprs: _*), s0, s1)
      } 
      case _ => false
    }
    case _ => true
  }
}