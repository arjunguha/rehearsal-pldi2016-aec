# output to outputs.json 
define opdemand::output($key, $value) {
  exec {"/usr/local/bin/opdemand-output $key $value":
    path        => "/var/cache/opdemand",
    user        => "root",
    require =>  Class[Opdemand::Common],
  }
}