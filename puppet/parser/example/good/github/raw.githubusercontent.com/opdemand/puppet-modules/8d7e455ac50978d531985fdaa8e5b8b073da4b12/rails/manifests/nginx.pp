class rails::nginx (){
  
  require rails::params
  
  nginx::resource::vhost { "rails":
    ensure   => present,
    proxy => "http://thin",
  }

  nginx::resource::upstream { "thin":
    ensure  => present,
    members => [
      "127.0.0.1:3000",
      "127.0.0.1:3001",
      "127.0.0.1:3002",
    ],
  }
  
}
