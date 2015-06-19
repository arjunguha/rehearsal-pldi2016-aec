package rehearsal.ppmodel

import exp.synthesis.Synthesizer


case class CannotUpdate(msg: String) extends RuntimeException(msg)

object UpdateSynth  extends com.typesafe.scalalogging.LazyLogging {

  import exp._
  import exp.{External => E, CommonSyntax => C}

  import java.nio.file.{Files, Path, Paths}
  import scalax.collection.GraphEdge.DiEdge
  import rehearsal.fsmodel._

  def calculate(manifest1: Path, manifest2: Path): Unit = {
    calculate(new String(Files.readAllBytes(manifest1)),
              new String(Files.readAllBytes(manifest2)))
  }

  def topologicalSort[V](graph: scalax.collection.Graph[V, DiEdge]): List[V] = {
    if (graph.isEmpty) {
      List()
    }
    else {
      graph.nodes.find(_.inDegree == 0) match {
        case None => throw CannotUpdate("cyclic graph")
        case Some(node) => {
          node :: topologicalSort(graph - node)
        }
      }
    }
  }

  def genEnum(typeDef: E.TypeDef): E.Expr = {
    assert (typeDef.isEnumerated)
    val n = typeDef.cons.length
    val pats = (0.until(n - 1).map(i => E.PConst(E.CNum(i)))) :+ E.PElse
    val arms = typeDef.cons.map({ case (cname, _) => E.EConstr(cname, Nil) })
    E.TypedFun(C.Id("_"), E.TNum, E.EMatch(E.EOp2(C.Mod, E.EMkHole(), E.EConst(E.CNum(n))), pats.zip(arms).toList))
  }

  def replaceBody(expr: E.Expr, body: E.Expr): E.Expr = expr match {
    case E.ELet(x, e1, e2) => E.ELet(x, e1, replaceBody(e2, body))
    case E.ELetRec(x, t, e1, e2) => E.ELetRec(x, t, e1, replaceBody(e2, body))
    case _ => body
  }

  def mkLet(x: String, e1: E.Expr, e2: E.Expr) = E.ELet(C.Id(x), e1, e2)

  def okHack(e: E.Expr) = {
    E.EApp(E.EApp(E.EId(C.Id("unwrapstate")), e),
          E.EArray(Map(), E.EConstr("SDoesNotExist", Nil), E.TConstructor("path"), E.TConstructor("filestate")))
  }

  def enumEqDef(t: E.TypeDef): E.Expr = {
    import E._
    import C._
    val x = EId(Id("x"))
    val y = EId(Id("y"))
    println(t)
    val cases = t.cons.map(_._1).map(cname => PConstr(cname, Nil) -> EMatch(y, List(PConstr(cname, Nil) -> EConst(CBool(true)), PElse -> EConst(CBool(false)))))
    TypedFun(Id("x"), TConstructor(t.id),
      TypedFun(Id("y"), TConstructor(t.id),
        if (cases.length == 1) { EConst(CBool(true)) } else { EMatch(x, cases) }))
  }

  def fileArrayEq(paths: E.TypeDef): E.Expr = {
    import E._
    import C._
    val x = EId(Id("x"))
    val y = EId(Id("y"))

    val lst: List[Expr] = paths.cons.map(_._1).map(pname => EApp(EApp(EId(Id("filestateeq")), ESelect(x, EConstr(pname, Nil))), ESelect(y, EConstr(pname, Nil))))
    val body = lst.reduce((e1, e2) => EOp2(And, e1, e2))
    val tarray = E.TArray(E.TConstructor("path"), E.TConstructor("filestate"))
    TypedFun(Id("x"), tarray,
      TypedFun(Id("y"), tarray,
      body))
  }

  def stateEqDef = {
    import E._
    import C._
    val x = EId(Id("x"))
    val y = EId(Id("y"))
    val fs0 = Id("fs0")
    val fs1 =  Id("fs1")
    TypedFun(Id("x"), TConstructor("state"),
      TypedFun(Id("y"), TConstructor("state"),
      EMatch(x, List(PConstr("Ok", List(fs0)) -> EMatch(y, List(PConstr("Ok", List(fs1)) -> EApp(EApp(EId(Id("filearrayeq")), EId(fs1)), EId(fs0)),
                                                              PElse -> EConst(CBool(false)))),
                    PConstr("Error", Nil) -> EMatch (y, List(PConstr("Error", Nil) -> EConst(CBool(true)),
                                                            PElse -> EConst(CBool(false))))))))
  }



  def calculate(manifest1: String, manifest2: String): Unit = {
    val depth = 2 // TODO(Arjun): don't hardcode

    val graph1 = puppet.syntax.parse(manifest1).desugar().toGraph(Map()).head._2
    val graph2 = puppet.syntax.parse(manifest2).desugar().toGraph(Map()).head._2

    assert(SymbolicEvaluator2.isDeterministic(toFileScriptGraph(graph1)), "V1 is not deterministic")
    assert(SymbolicEvaluator2.isDeterministic(toFileScriptGraph(graph2)), "V2 is not deterministic")

    val resList1 = topologicalSort(graph1).map(r => ResourceToExpr.convert(r))
    val resList2 = topologicalSort(graph2).map(r => ResourceToExpr.convert(r))
    val (pathTypeDef, hashTypeDef) = ResourceModel.buildTypes(resList1 ++ resList2)

    val (staticTypeDefs, staticCommonExprs) = Parser.parseFromFile(Paths.get("update.syn"))

    val tenv = External.buildEnv(pathTypeDef :: hashTypeDef :: staticTypeDefs)
    val env = Map(C.Id("inSt") -> E.TArray(E.TConstructor("path"), E.TConstructor("filestate")))

    val commonExprs = mkLet("parent", ResourceModel.genGetParent(pathTypeDef),
                        mkLet("genpath", genEnum(pathTypeDef),
                          mkLet("genhash",  genEnum(hashTypeDef),
                          mkLet("hasheq", enumEqDef(hashTypeDef),
                            staticCommonExprs))))

    val spec = E.EApp(E.EApp(E.EId(C.Id("evalresources")), E.EId(C.Id("inSt"))),
                                        ResourceModel.coerceAll(resList2))

    val sketch = E.EApp(E.EApp(E.EId(C.Id("evalunwrap")),
                     E.EApp(E.EApp(E.EId(C.Id("evalresources")), E.EId(C.Id("inSt"))), ResourceModel.coerceAll(resList1))),
                   E.EApp(E.EId(C.Id("genresourcelist")), E.EConst(E.CNum(depth))))


    val expr = replaceBody(commonExprs,
      mkLet("filearrayeq", fileArrayEq(pathTypeDef),
        mkLet("stateeq", stateEqDef,
          E.EApp(E.EApp(E.EId(C.Id("stateeq")), sketch), spec))))


    val (t, exprTyped) = E.typeCheck(tenv, env, expr)
    assert (t == E.TBool)


    val genFSArrayDef = E.EArray(
      pathTypeDef.cons.map(_._1).map {
        pathName => (E.EConstr(pathName, Nil), E.EApp(E.EId(C.Id("genfilestate")), E.EConst(E.CNum(0))))
      }.toMap,
      E.EConstr("SDoesNotExist", Nil),
      E.TConstructor("path"),
      E.TConstructor("filestate"))


    val gen = replaceBody(commonExprs, genFSArrayDef)
    val (_, genTyped) = E.typeCheck(tenv, env, gen)

    logger.info("Starting synthesizer")

    val result = Synthesizer.genTypedCompletionGen(
      Map(C.Id("inSt") -> genTyped),
      exprTyped)
    println(result)






  }

}