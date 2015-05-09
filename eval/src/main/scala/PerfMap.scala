package eval

import scala.collection.mutable.{ Builder, MapBuilder }

class PerfMap[A, +B](map: Map[A, B], hash: Int) extends scala.collection.MapLike[A, B, PerfMap[A, B]]
                                                with Map[A, B] {
  def get(key: A) = map.get(key)
  def iterator = map.iterator
  
  def +[B1 >: B](kv: (A, B1)) = {
    val newMap = map + kv
    new PerfMap(newMap, hashCode + kv.hashCode)
  }

  def -(key: A) = {
    val kv = (key, map(key))
    val newMap = map - key
    new PerfMap(newMap, hashCode - kv.hashCode)
  }

  override val size = map.size
  override val hashCode = hash

  override def empty = new PerfMap(Map.empty, PerfMap.seed)
  override protected[this] def newBuilder = new MapBuilder[A, B, PerfMap[A, B]](empty)
}

object PerfMap {
  val seed = 0

  def apply[A, B](map: Map[A, B]) = {
    val hash = map.foldLeft(seed)((acc, kv) => acc + kv.hashCode)
    new PerfMap(map, hash)
  }

  def apply[A, B](xs: (A,B)*) = {
    val hash = xs.foldLeft(seed)((acc, kv) => acc + kv.hashCode)
    new PerfMap(Map(xs:_*), hash)
  }

  def empty[A, B] = {
    new PerfMap[A, B](Map.empty, seed)
  }
}
