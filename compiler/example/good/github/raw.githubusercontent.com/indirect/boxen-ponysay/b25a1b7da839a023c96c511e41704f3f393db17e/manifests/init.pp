class ponysay {
  homebrew::formula { 'ponysay': }
  package { 'boxen/brews/ponysay': }
}

class fortune {
  package { 'fortune': }
}

class fortune::horse_ebooks {
  include fortune

  $fortunes = "/opt/boxen/homebrew/share/games/fortunes"

  exec { 'horse_ebooks':
    cwd     => $fortunes,
    command => "curl -o horse_ebooks http://horsefortun.es/fortune",
    unless  => "test -e $fortunes/horse_ebooks"
  }

  exec { 'horse_ebooks.dat':
    refreshonly => true,
    cwd         => $fortunes,
    command     => "strfile horse_ebooks",
    subscribe   => Exec['horse_ebooks']
  }
}
