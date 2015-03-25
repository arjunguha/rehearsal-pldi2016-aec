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
      val old_kv = map(key)
      val newMap = map + kv
      new PerfMap(newMap, hashCode - old_kv.hashCode + kv.hashCode) // TODO(nimish): Check
    }
    else {
    */
//      val (key, value) = kv
//      assert(!map.contains(key))
      val newMap = map + kv
      new PerfMap(newMap, hashCode + (kv.hashCode % PerfMap.modbase))
    // }
  }

  def -(key: A) = {
//    if (map.contains(key)) {
//      assert(map.contains(key))
      val kv = (key, map(key))
      val newMap = map - key
      new PerfMap(newMap, hashCode - (kv.hashCode % PerfMap.modbase))
//    }
//    else {
//      this
//    }
  }

  override val size = map.size
//  override def foreach[U](f: ((A, B)) => U): Unit  = map.foreach(f)

  override def empty = new PerfMap(Map.empty, PerfMap.seed)
  override protected[this] def newBuilder = new MapBuilder[A, B, PerfMap[A, B]](empty)

  override val hashCode = hash % PerfMap.modbase
}

object PerfMap {

//  val modbase = Int.MaxValue

  /*
   * http://www.wolframalpha.com/input/?i=prime+number+near+2%5E30
   *
   * modbase is chosen to be a prime number less than 2^30-2,
   * Upper bound is 2^30-2 so that sum of two number module modbase does
   * not overflow (i.e sum is always <= Int.MaxValue)
   */
  val modbase = 1073741789
  val seed = 0

  def apply[A, B](map: Map[A, B]) = {
    val hash = map.foldLeft(seed)((acc, kv) => (acc + (kv.hashCode % modbase)) % modbase)
    new PerfMap(map, hash)
  }

  def apply[A, B](xs: (A,B)*) = {
    val hash = xs.foldLeft(seed)((acc, kv) => (acc + (kv.hashCode % modbase)) % modbase)
    new PerfMap(Map(xs:_*), hash)
  }

  def empty[A, B] = {
    new PerfMap[A, B](Map.empty, seed)
  }
}
