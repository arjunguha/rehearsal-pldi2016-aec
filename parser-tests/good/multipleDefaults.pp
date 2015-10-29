class hi {
  Notify { message => "HELLO" }

  notify{"hello": }

}

class hiiii {
  Notify { message => "greetings"}

}
include hiiii

include hi