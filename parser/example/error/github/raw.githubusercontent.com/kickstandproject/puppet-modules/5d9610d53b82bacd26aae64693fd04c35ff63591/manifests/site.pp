import 'nodes/*/*.pp'

stage { 'bootstrap':
  before => Stage['main'],
}

Exec {
  path => '/bin:/sbin:/usr/bin:/usr/sbin',
}
