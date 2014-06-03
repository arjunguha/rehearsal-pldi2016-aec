class gsettings::setup{
  $schemas_path = '/usr/share/glib-2.0/schemas'
  @exec{"glib-compile-schemas":
    path        => ["/bin","/usr/bin"],
    provider    => shell,
    command     => "glib-compile-schemas $schemas_path",
    refreshonly => true,
  }
}
