define ezpublish::install::fetch::local ($www, $ezpublish_src, $ezpublish_folder, $ezpublish) {
  exec { "download-tar":
    command => "/bin/cp /local/$ezpublish_src $www/$ezpublish",
  } ~>
  exec { "create_folder_tar":
    command => "/bin/mkdir $www/$ezpublish_folder",
    refreshonly => true,
    returns => [ 0, 1, 2, '', ' ']
  } ~>
  exec { "extract_tar":
    command => "/bin/tar --strip-components=1 -xzf $www/$ezpublish -C $www/$ezpublish_folder",
    refreshonly => true,
    returns => [ 0, 1, 2, '', ' ']
  }
}