define mytype($x) {

  file{'/myfile':
    $x => "hello"
  }

}