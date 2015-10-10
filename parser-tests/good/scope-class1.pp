# Check that identifiers within classes are statically scoped
$x = true

class myClass {

  if $x {
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
