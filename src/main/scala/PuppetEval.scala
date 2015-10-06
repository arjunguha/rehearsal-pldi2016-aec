package rehearsal

object Evaluator {
  //pipeline: toGraph(Graph(), eval(expandAll(parse(m))))
  import Syntax._
  import scalax.collection.mutable.Graph
  import scalax.collection.mutable.Graph._
  import scalax.collection.GraphEdge._
  import Implicits._

  case class EvalError(msg: String) extends RuntimeException(msg)
  case class GraphError(msg: String) extends RuntimeException(msg)
  type ResourceGraph = Graph[Resource, DiEdge]

  sealed trait EdgeDir
  case object Left extends EdgeDir
  case object Right extends EdgeDir

  def isValue(m: Manifest): Boolean = m match {
    case Empty => true
    case Block(m1, m2) => isValue(m1) && isValue(m2)
    case Resource(title, typ, attrs) => {
      isValueExpr(title) && isPrimitiveType(typ) && attrs.forall {
        case Attribute(name, value) => isValueExpr(name) && isValueExpr(value)
      }
    }
    case Edge(m1, m2) => isValue(m1) && isValue(m2)
    case Define(_, _, _) => false
    case Class(_, _, _, _) => false
    case Let(_, _, _) => false
    case MCase(_, _) => false
    case E(e) => isValueExpr(e)
    case Include(_) => false
    case Require(_) => false
  }

  def isValueExpr(e: Expr): Boolean = e match {
    case Undef => true
    case Str(_) => true
    case Bool(_) => true
    case Res(typ, e, attrs) => isPrimitiveType(typ) && isValueExpr(e) && attrs.forall {
      case Attribute(name, value) => isValueExpr(name) && isValueExpr(value)
    }
    case Var(_) => false
    case Not(_) => false
    case And(_, _) => false
    case Or(_, _) => false
    case Eq(_, _) => false
    case Match(_, _) => false
    case In(_, _) => false
    case Array(es) => es.forall(isValueExpr)
    case App(_, _) => false
    case ITE(pred, m1, m2) => isValueExpr(pred) && isValue(m1) && isValue(m2)
    case RegExp(_,_) => false
  }

  val primitiveTypes = Set("file", "File", "package", "Package", "user", "User", "group", "Group",
                           "service", "Service", "ssh_authorized_key", "Ssh_authorized_key")

  def isPrimitiveType(typ: String): Boolean = primitiveTypes.contains(typ)

  def subExpr(varName: String, e: Expr, body: Expr): Expr = body match {
    case Str(_) => body
    case Res(typ, expr, attrs) => Res(typ, subExpr(varName, e, expr), attrs.map(subAttr(varName, e, _)))
    case Var(id) if varName == id => e
    case Var(_) => body
    case Bool(_) => body
    case Not(expr) => Not(subExpr(varName, e, expr))
    case And(expr1, expr2) => And(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
    case Or(expr1, expr2) => Or(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
    case Eq(expr1, expr2) => Eq(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
    case Match(expr1, expr2) => Match(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
    case In(expr1, expr2) => In(subExpr(varName, e, expr1), subExpr(varName, e, expr2))
                case ITE(pred, m1, m2) => ITE(subExpr(varName, e, pred), sub(varName, e, m1), sub(varName, e, m2))
  }

  def subAttr(varName: String, e: Expr, attr: Attribute): Attribute = attr match {
    case Attribute(name, value) => Attribute(subExpr(varName, e, name), subExpr(varName, e, value))
  }

  def paramsContainVar(varName: String, params: Seq[Argument]) =
    params.foldRight[Boolean](false){case (Argument(id, _), res) => ((id == varName) || res)}

  def sub(varName: String, e: Expr, body: Manifest): Manifest = body match {
    case Empty => body
    case Block(m1, m2) => Block(sub(varName, e, m1), sub(varName, e, m2))
    case Resource(title, typ, attrs) =>
      Resource(subExpr(varName, e, title), typ, attrs.map(attr => subAttr(varName, e, attr)))
    case Edge(m1, m2) => Edge(sub(varName, e, m1), sub(varName, e, m2))
    case Define(name, params, m) if name != varName && !paramsContainVar(varName, params) =>
      Define(name, params, sub(varName, e, m))
    case Define(_, _, _) => body
    case Let(v, expr, b) if v != varName => Let(v, subExpr(varName, e, expr), sub(varName, e, b))
    case Let(v, expr, b) => Let(v, subExpr(varName, e, expr), b)
    case E(expr) => E(subExpr(varName, e, expr))
  }

  def evalAttr(a: Attribute): Attribute = a match {
    case Attribute(name, value) => Attribute(evalExpr(name), evalExpr(value))
  }

  def evalExpr(e: Expr): Expr = e match {
    case Undef => e
    case Res(typ, e, attrs) => Res(typ, evalExpr(e), attrs.map(evalAttr))
    case Var(_) => e
    case Str(_) => e
    case Bool(_) => e
    case Array(_) => e
    case Not(e) => evalExpr(e) match {
      case Bool(b) => Bool(!b)
      case _ => throw EvalError(s"Cannot evaluate: Invalid argument for Not: $e")
    }
    case And(e1, e2) => (evalExpr(e1), evalExpr(e2)) match {
      case (Bool(b1), Bool(b2)) => Bool(b1 && b2)
      case _ => throw EvalError(s"Cannot evaluate: Invalid argument(s) for And: $e1, $e2")
    }
    case Or(e1, e2) => (evalExpr(e1), evalExpr(e2)) match {
      case (Bool(b1), Bool(b2)) => Bool(b1 || b2)
      case _ => throw EvalError(s"Cannot evaluate: Invalid argument(s) for Or: $e1, $e2")
    }
    case Eq(e1, e2) => if(evalExpr(e1) == evalExpr(e2)) Bool(true) else Bool(false)
    case Match(Str(e1), Str(e2)) => {
      val pat = e2.r
      e1 match {
        case pat(_) => Bool(true)
        case _ => Bool(false)
      }
    }
    case Match(e1, e2) => throw EvalError(s"Cannot evaluate: Invalid argument(s) for Match: $e1, $e2")
    case In(Str(e1), Str(e2)) => if(e2.contains(e1)) Bool(true) else Bool(false)
    case In(e1, e2) => throw EvalError(s"Cannot evaluate: Invalid argument(s) for In: $e1, $e2")
    case App(_, _) => throw new Exception("NYI")
    case ITE(pred, m1, m2) => evalExpr(pred) match {
      case Bool(true) => eval(m1) match {
        case E(e) => e
        case _ => throw EvalError(s"Cannot evaluate ITE as an expression with non-expressions in the branch: $m1")
      }
      case Bool(false) => eval(m2) match {
        case E(e) => e
        case _ => throw EvalError(s"Cannot evaluate ITE as an expression with non-expressions in the branch: $m2")
      }
      case Undef => eval(m2) match {
        case E(e) => e
        case _ => throw EvalError(s"Cannot evaluate ITE as an expression with non-expressions in the branch: $m2")
      }
      case _ => throw EvalError(s"Cannot evaluate: invalid predicate for if: $pred")
    }
    case RegExp(_, _) => e
  }

  def edgesFromArr(es: Seq[Expr], m: Manifest, d: EdgeDir): Manifest = es match {
    case Seq() => throw EvalError("edgesFromArr: cannot create edge with empty array")
    case h :: Seq() => if(d == Right) Edge(E(h), m) else Edge(m, E(h))
    case h :: t => {
      if(d == Right) Block(Edge(E(h), m), edgesFromArr(t, m, d))
      else           Block(Edge(m, E(h)), edgesFromArr(t, m, d))
    }
  }

  /* Note: it is not possible to have an edge between 2 arrays, because an edge containing an
     array only arises through the before and require attributes and such edges always have a
     Res as one of the nodes [-Rian]
   */

  def eval(m: Manifest): Manifest = m match {
    case Empty => Empty
    case Block(m1, m2) => eval(m1) >> eval(m2)
    case Resource(title, typ, attrs) => Resource(evalExpr(title), typ, attrs.map(evalAttr))
    case Edge(E(Array(es)), m2) => edgesFromArr(es, eval(m2), Right)
    case Edge(m1, E(Array(es))) => edgesFromArr(es, eval(m1), Left)
    case Edge(m1, m2) => Edge(eval(m1), eval(m2))
    case Define(_, _, _) => m
    case Let(varName, e, body) => eval(sub(varName, evalExpr(e), body))
    case Class(_, _, _, _) => throw EvalError("class should have been eliminated by desugaring")
    case MCase(_, _) => throw EvalError("case should have been eliminated by desugaring")
    case E(ITE(pred, m1, m2)) => {
      val v = evalExpr(pred)
      if (v == Bool(true))        eval(m1)
      else if (v == Bool(false))  eval(m2)
      else if (v == Undef)        eval(m2)
      else throw EvalError(s"Cannot evaluate: Invalid Predicate for if: $pred")
    }
    case E(e) => E(evalExpr(e))
    case Include(_) => throw EvalError("include should have been eliminated during class expansion.")
    case Require(_) => throw EvalError("require should have been eliminated during class expansion.")

  }

  /*what to do if instance contains an attribute that doesn't have corresponding parameter in define? :
        ignoring for now */
  def subArgs(params: Seq[Argument], args: Seq[Attribute], body: Manifest): Manifest =
    (params, args) match {
      case (Seq(), _) => body
      case (Argument(paramName, _) :: paramsT, Attribute(Str(attrName), value) :: argsT) => {
        if(paramName == attrName) subArgs(paramsT, argsT, sub(paramName, value, body))
        else                      subArgs(params, argsT, body)
      }
      case (Argument(paramName, _) :: paramsT, Attribute(Var(attrName), value) :: argsT) => {
        if(paramName == attrName) subArgs(paramsT, argsT, sub(paramName, value, body))
        else                      subArgs(params, argsT, body)
      }
      case (Argument(paramName, Some(default)) :: paramsT, Seq()) =>
        subArgs(paramsT, args, sub(paramName, default, body))
      case (Argument(_, None) :: _, Seq()) => throw EvalError(s"""Not enough attributes for
        defined type instantiation: params = $params; body = $body""")
      case _ => throw EvalError(s"Unexpected attribute pattern: attrs = $args")
    }

  def expandDefine(m: Manifest, d: Define): Manifest = (m, d) match {
    case (Empty, _) => Empty
    case (Block(m1, m2), _) => Block(expandDefine(m1, d), expandDefine(m2, d))
    case (Resource(_, typ, attrs), Define(name, params, body)) if name == typ =>
      subArgs(params, attrs, body)
    case (Resource(_, _, _), _) => m //do nothing
    case (E(ITE(pred, thn, els)), _) => E(ITE(pred, expandDefine(thn, d), expandDefine(els, d)))
    case (Edge(m1, m2), _) => Edge(expandDefine(m1, d), expandDefine(m2, d))
    case (Define(name1, _, _), Define(name2, _, _)) if name1 == name2 => Empty //remove define declaration
    case (Define(name, params, body), _) => Define(name, params, expandDefine(body, d))
    case (Let(x, e, body), _) => Let(x, e, expandDefine(body, d))
    case (E(Res(typ, e, attrs)), _) => m //do something?
    case (E(_), _) => m

    case (Class(_,_,_,_), _) => throw EvalError("classes should have been removed during class expansion.")
    case (Include(_), _) => throw EvalError("include should have been removed during class expansion.")
    case (Require(_), _) => throw EvalError("require should have been removed during class expansion.")

  }

  def findDefine(m: Manifest): Option[Define] = m match {
    case d@Define(_, _, _) => Some(d)
    case Block(m1, m2) => {
      val m1res = findDefine(m1)
      if(m1res == None) findDefine(m2) else m1res
    }
    case Edge(m1, m2) => {
      val m1res = findDefine(m1)
      if(m1res == None) findDefine(m2) else m1res
    }
    case E(ITE(_, m1, m2)) => {
      val m1res = findDefine(m1)
      if(m1res == None) findDefine(m2) else m1res
    }
    case Let(_, _, body) => findDefine(body)
    case Class(_, _, _, body) => findDefine(body)
    case Empty |E(_) | Resource(_, _, _) | Include(_) | Require(_) => None

    case MCase(_, _) => throw new Exception("not implemented")
  }


  def expandAllDefines(m: Manifest): Manifest = {
    var d: Option[Define] = findDefine(m)
    var m2: Manifest = m
    while(d != None){
      m2 = expandDefine(m2, d.get)
      d = findDefine(m2)
    }
    m2
  }

  //TODO(jcollard)
  def findClass(m: Manifest): Option[Class] = m match {
    case c@Class(_, _, _, _) => Some(c)
    case Block(m1, m2) => {
      val m1res = findClass(m1)
      if(m1res == None) findClass(m2) else m1res
    }
    case Edge(m1, m2) => {
      val m1res = findClass(m1)
      if(m1res == None) findClass(m2) else m1res
    }
    case E(ITE(_, m1, m2)) => {
      val m1res = findClass(m1)
      if(m1res == None) findClass(m2) else m1res
    }
    case Let(_, _, body) => findClass(body)
    case Define(_,_,body) => findClass(body)
    case Empty |E(_) | Resource(_, _, _) | Include(_) | Require(_) => None
    case MCase(_, _) => throw  new Exception("not implemented")
  }

  //TODO(jcollard)
  def expandClass(m: Manifest, c: Class, expanded: Boolean): (Manifest, Boolean) =
    c match {
      case Class(name,params,inherits,body) => {
        m match {
          // Turn the class into a Define
          case Class(name1,_,_,_)
              if name1 == name => (Define(name, params, body), expanded)
          case c2@Class(_,_,_,_) => (c2, expanded)

          case Empty => (Empty, expanded)
          case Block(m1, m2) => {
            val (m1Prime, expandedPrime) = expandClass(m1, c, expanded)
            val (m2Prime, expandedPrime2) = expandClass(m2, c, expandedPrime)
            (Block(m1Prime, m2Prime), expandedPrime2)
          }
          // TODO(jcollard): Check if this is a Class resource?
          case Resource(_, _, _) => (m, expanded) //do nothing
          case E(ITE(pred, thn, els)) => {
            //TODO(jcollard): This is almost certainly wrong. This should
            //be something that would normally be handled at runtime. If
            //the include is on both the left and right hand side, this
            //will likely be incorrect
            val (left, e0) = expandClass(thn, c, expanded)
            val (right, e1) = expandClass(els, c, e0)
            (E(ITE(pred, left, right)), e1)
          }
          case Edge(m1, m2) => {
            val (left, e0) = expandClass(m1, c, expanded)
            val (right, e1) = expandClass(m2, c, e0)
            (Edge(left, right), e1)
          }
          case Define(name, params, body) => {
            val (bod, e0) = expandClass(body, c, expanded)
            (Define(name, params, bod), e0)
          }
          case Let(x, e, body) => {
            val (bod, e0) = expandClass(body, c, expanded)
            (Let(x, e, bod), e0)
          } 
          case E(_) => (m, expanded)

          //Replace include / require with a resource that will be filled
          //during expansion.
          case Include(_) => (Resource(Str(name), name, params.map(argToAttr(name))), true)
          case Require(_) => (Resource(Str(name), name, params.map(argToAttr(name))), true)
        }
      }
    }

  def argToAttr(className: String)(arg: Argument) : Attribute =
    arg match {
      case Argument(id, None) => Attribute(Str(id), Var(s"$className::$id"))
      case Argument(id, Some(e)) => Attribute(Str(id), e)
    }



  def expandAllClasses(m: Manifest): Manifest = {
    var d: Option[Class] = findClass(m)
    var m2: Manifest = m
    while(d != None){
      val (newMan, _) = expandClass(m2, d.get, false)
      m2 = newMan
      d = findClass(m2)
    }
    m2
  }


  def expandAll(m: Manifest): Manifest = {
    expandAllDefines(expandAllClasses(m))
  }

  /* Note: it is not possible to have an edge between 2 arrays, because an edge containing an
     array only arises through the before and require attributes and such edges always have a
     Res as one of the nodes [-Rian]
   */
   def expandRes(r: Res, m: Manifest): Option[Resource] = m match {
    case Block(m1, m2) => {
      val resDef = expandRes(r, m1)
      if(resDef == None) expandRes(r, m2)
      else               resDef
    }
    case resDef@Resource(title, typ, attrs) => r match {
      //TODO(Rian)
      case Res(refTyp, refTitle, refAttrs) => {
        if (refTyp.equalsIgnoreCase(typ) && title == refTitle) Some(Resource(title, typ, attrs ++ refAttrs))
        else None
      }
    }
    case E(ITE(_, m1, m2)) => {
      val resDef = expandRes(r, m1)
      if(resDef == None) expandRes(r, m2)
      else               resDef
    }
    case Edge(m1, m2) => {
      val resDef = expandRes(r, m1)
      if(resDef == None) expandRes(r, m2)
      else               resDef
    }
    case Define(_, _, body) => expandRes(r, body)
    case Class(_, _, _, body) => expandRes(r, body)
    case Let(varName, e, body) => expandRes(r, body)
    case Empty | E(_) => None
    case MCase(_, _) => throw EvalError(s"$m should have been desugared")
    case Include(_) | Require(_) => throw EvalError(s"NYI (expandRes): $m")
  }

  def addEdges(g: ResourceGraph, e: Edge): ResourceGraph = e match {
    case Edge(r1@Resource(_, _, _), r2@Resource(_, _, _)) => g += DiEdge(r1, r2)
    case Edge(Block(r11, r12), r2) => addEdges(g, Edge(r11, r2)) ++ addEdges(g, Edge(r12, r2))
    case Edge(r1, Block(r21, r22)) => addEdges(g, Edge(r1, r21)) ++ addEdges(g, Edge(r1, r22))
    case Edge(_, _) => throw GraphError(s"edge is not fully evaluated $e")
  }

  def toGraph(m: Manifest): ResourceGraph = toGraphRec(Graph(), m, m)

  def toGraphRec(g: ResourceGraph, m: Manifest, wholeM: Manifest): ResourceGraph = m match {
    case Empty => g
    case Block(m1, m2) => toGraphRec(g, m1, wholeM) ++ toGraphRec(g, m2, wholeM)
    case Edge(E(r1@Res(_, _, _)), E(r2@Res(_, _, _))) => {
      val r1Def = expandRes(r1, wholeM)
      val r2Def = expandRes(r2, wholeM)
      if(r1Def == None) throw GraphError(s"can't find resource def that corresponds to $r1")
      else if (r2Def == None) throw GraphError(s"can't find resource def that corresponds to $r2")
      else g + DiEdge(r1Def.get, r2Def.get)
    }
    case Edge(E(r@Res(_, _, _)), m2) => {
      val rDef = expandRes(r, wholeM)
      if(rDef == None) throw GraphError(s"can't find resource def that corresponds to $r")
      addEdges(g, Edge(rDef.get, m2))
    }
    case Edge(m1, E(r@Res(_, _, _))) => {
      val rDef = expandRes(r, wholeM)
      if(rDef == None) throw GraphError(s"can't find resource def that corresponds to $r")
      addEdges(g, Edge(m1, rDef.get))
    }
    case e@Edge(_, _) => addEdges(g, e)
    case r@Resource(_, _, _) => g + r
    case E(r@Res(_, _, _)) => {
      val resDef = expandRes(r, m)
      if(resDef == None) throw GraphError(s"can't find resource def that corresponds to $r")
      g + resDef.get
    }
    case Let(_, _, _) | E(_) | Define(_, _, _) | Class(_, _, _, _) |
         MCase(_, _) => throw GraphError(s"m is not fully evaluated $m")
    case Include(_) | Require(_) => throw GraphError(s"NYI (toGraph): $m")
  }
}
