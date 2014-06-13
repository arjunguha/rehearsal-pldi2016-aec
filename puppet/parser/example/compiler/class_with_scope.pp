$toplevelvar = "toplevel"
$somevar = "some toplevel var"

class parent { 
  $parentvar = "parent class"
  $somevar = "some parent var"
}

class child inherits parent {
  $childvar = "child class"
  $somevar = "some child var"

  notice($toplevelvar)
  notice($parentvar)
  notice($childvar)
  notice($::somevar)
  notice($parent::somevar)
  notice($somevar)
}

include child
