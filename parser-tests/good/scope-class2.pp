# Check that default expressions are statically scoped
$x = true

class myClass($arg = $x) {

  if $arg {
    notify{"r": message => "static scope" }
  }
  else {
    fail("dynamic scope :(")
  }

}

class otherClass {
  $x = false
  include myClass
}

include otherClass