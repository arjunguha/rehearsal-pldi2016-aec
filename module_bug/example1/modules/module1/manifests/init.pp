class module1 {

  package {'apache2':
    ensure => installed
  }

  service {'apache2':
    ensure => running
  }

  Package <| |> -> Service <| |>
}
