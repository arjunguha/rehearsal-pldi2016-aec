class hi {
  Notify { message => "HELLO" }

  notify{"hello": }

}

class hiiii {
  Notify { message => "greetings"}
  notify{"notification2": }

}
include hiiii

include hi