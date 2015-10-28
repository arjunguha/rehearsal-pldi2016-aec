class myclass($x) {

  notify{"baz": message => $x}

}

class{"myclass":
   x => "/a"
}

notify{"bar":
  message => "it worked",
  require => Notify["baz"]
}