node default {
  Exec {
    path => $::path,
  }

  include packages

  include base

  #include nginx

  #include mysql
  #include mongodb

  #include php
  #class { "ruby":
  #version => "2.0.0-p353"
  #}
}
