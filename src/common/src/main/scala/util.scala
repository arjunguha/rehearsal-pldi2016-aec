package puppet.common.util

object stripQuote {

  def apply(str: String): String = {
    var newstr = str

    if(str.length > 0 && (str(0) == '\'' || str(0) == '\"'))
      newstr = newstr.stripPrefix(str(0).toString)

    if(str.length > 1 && (str(str.length-1) == '\'' || str(str.length-1) == '\"'))
      newstr = newstr.stripSuffix(str(str.length-1).toString)

    newstr
  }
}
