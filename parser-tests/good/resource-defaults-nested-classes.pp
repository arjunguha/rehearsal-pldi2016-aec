define  myType {
  Notify {  message => "second message" }

  notify{"R2": }
}

class a {
  Notify { message => "first message (should only print once)" }


  notify{"R1": } -> myType{"R2": }
}
include a
