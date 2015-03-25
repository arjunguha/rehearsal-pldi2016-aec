package fsmodel.core

import scala.collection.mutable.{ Builder, MapBuilder }

class PerfMap[A, +B](map: Map[A, B], hash: Int) extends scala.collection.MapLike[A, B, PerfMap[A, B]]
                                                with Map[A, B] {


  def get(key: A) = map.get(key)
  def iterator = map.iterator
  def +[B1 >: B](kv: (A, B1)) = {
    /*
    val (key, value) = kv
    if (map.contains(key)) {
      val old_kv = (key, map(key))
      val newMap = map + kv
      new PerfMap(newMap, hashCode - old_kv.hashCode + kv.hashCode)
    }
    else {
    */
//      val (key, value) = kv
//      assert(!map.contains(key))
      val newMap = map + kv
      new PerfMap(newMap, hashCode + kv.hashCode)
    // }
  }

  def -(key: A) = {
//    if (map.contains(key)) {
//      assert(map.contains(key))
      val kv = (key, map(key))
      val newMap = map - key
      new PerfMap(newMap, hashCode - kv.hashCode)
//    }
//    else {
//      this
//    }
  }

  override val size = map.size
//  override def foreach[U](f: ((A, B)) => U): Unit  = map.foreach(f)

  override def empty = new PerfMap(Map.empty, PerfMap.seed)
  override protected[this] def newBuilder = new MapBuilder[A, B, PerfMap[A, B]](empty)

  override val hashCode = hash

/*
  override def canEqual(other: Any): Boolean =
    other.isInstanceOf[PerfMap[_, _]]

  override def equals(other: Any): Boolean = other match {
    case that: PerfMap[_, _] => {
      val hashEqual = that.hashCode == this.hashCode
      val mapEqual = that.getMap == this.map
      if (hashEqual && !mapEqual) {
        println("Collision detected")
      }
      else if (!hashEqual && mapEqual) {
        println(s"Error detected, hashes are not equal even though maps are equal: ${that.hashCode} ${this.hashCode}")
        that.getMap.foreach({ case (k, v) => println(s"""("${k}", $v),""") })
        println()
        println()
        println()
        println()
        println()
        this.map.foreach(println(_))
        throw new Exception("Aborting..")
      }
      
      (that canEqual this) &&
      (that.size == this.size) &&
      hashEqual &&
      // super.equals(that)
       mapEqual
    }
                                
    case _ => false
  }

  def getMap = map
*/
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
