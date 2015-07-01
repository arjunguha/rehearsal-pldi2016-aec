package rehearsal

object CatalogImpl {

  import java.nio.file._
  import spray.json._
  import scalax.collection.mutable.Graph, scalax.collection.GraphEdge.DiEdge, scalax.collection.GraphPredef._
  import puppet.graph.Value

  case class Ref(title: String, typ: String)
  case class Res(typ: String, title: String,
                      require: Seq[Ref],
                      before: Seq[Ref],
                      attrs: Map[String, Value]) {

    val ref = Ref(title, typ)
  }

  case class Data(resources: Seq[Res])
  case class Top(data: Data)

  trait WithoutWriter[T] {

    def write(x: T): JsValue = throw new SerializationException("Cannot serialize values of type " + x.getClass.toString)
  }

  object MyJsonProtocol extends DefaultJsonProtocol {

    def optJsArray[T](v: JsValue): JsValue = v match {
      case JsArray(_) => v
      case _ => JsArray(Vector(v))
    }

    implicit object valueFormat extends JsonFormat[Value] with WithoutWriter[Value] {
      import puppet.graph._
      def read (value: JsValue): Value = value match {
        case JsString(str) => StringV(str)
        case JsBoolean(b) => BoolV(b)
        case JsArray(arr) => ASTArrayV(arr.map(x => read(x)).toArray)
        case _ => throw new DeserializationException(s"unexpected value $value")
      }
    }

    implicit object resourceRefFormat extends JsonFormat[Ref] with WithoutWriter[Ref] {

      val r = """^(.*)\[(.*)\]$""".r

      def read(value: JsValue): Ref = value match {
        case JsString(str) =>  {
          val m = r.findFirstMatchIn(str).get
          Ref(m.group(2).toLowerCase, m.group(1).toLowerCase)
        }
        case _ => throw new DeserializationException("expected string")
      }

    }

    implicit object resourceFormat extends JsonFormat[Res] with WithoutWriter[Res] {

      def read(value: JsValue) = value.asJsObject.getFields("type", "title", "parameters") match {
        case Seq(JsString(typ), JsString(title), JsObject(params)) => {
          val require = optJsArray(params.getOrElse("require", JsArray())).convertTo[Seq[Ref]]
          val before = optJsArray(params.getOrElse("before", JsArray())).convertTo[Seq[Ref]]
          val notify = optJsArray(params.getOrElse("notify", JsArray())).convertTo[Seq[Ref]]
          val attrs = (params - "require" - "before" - "notify").mapValues(x => x.convertTo[Value])
          Res(typ.toLowerCase, title.toLowerCase, require, before ++ notify, attrs)
        }
        case _ => throw new DeserializationException("Could not deserialize resource")
      }

    }
    implicit val dataFormat = jsonFormat1(Data.apply)
    implicit val topFormat = jsonFormat1(Top.apply)
  }

  import MyJsonProtocol._

  def mkGraph(resources: Seq[Res]): Graph[Ref, DiEdge] = {
    val g = Graph[Ref, DiEdge]()
    for (r <- resources) {
      g.add(r.ref)
    }
    for (r <- resources; before <- r.before) {
      g.add(DiEdge(from = r.ref, to = before))
    }
    for (r <- resources; require <- r.require) {
      g.add(DiEdge(from = require, to = r.ref))
    }
    g

  }

  val toElim = Set("Stage", "Class")

  def elimCompoundResources(g: Graph[Ref, DiEdge]): Unit = {
    for (ref <- g.nodes.toList; if (toElim.contains(ref.typ))) {
      for (pre <- ref.inNeighbors; post <- ref.outNeighbors) {
        g.add(DiEdge(from = pre.value, to = post.value))
      }
    }
    for (ref <- g.nodes.toList; if (toElim.contains(ref.typ))) {
      assert(g.remove(ref))
    }
  }

  def mkResource(resources: Seq[Res])(ref: Ref): puppet.graph.Resource = {
    import puppet.graph._
    resources.find(r => r.ref == ref) match { // map would be faster
      case Some(r) => {
        // The Attribute case class is public, but its companion object is private. Therefore we have to use "new".
        // Evidently I don't understand visibility in Scala.
        val attrs = r.attrs.toList.map({ case (k, v) => new Attribute(k, v) })
        Resource(new Attribute("type", StringV(r.typ)) :: new Attribute("name",  StringV(r.title)) :: attrs)
      }
      case None => throw Unexpected(s"should have found ${ref.title} : ${ref.typ} in resources")
    }
  }

  def parseFile(path: String) = {
    val top = (new String(Files.readAllBytes(Paths.get(path)))).parseJson.convertTo[Top]
    val graph = mkGraph(top.data.resources)
    elimCompoundResources(graph)
    nodeMap(mkResource(top.data.resources), graph)
  }

}

object Catalog {

  val parseFile = CatalogImpl.parseFile _

}