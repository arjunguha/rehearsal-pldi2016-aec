class kbp_mcollective::server {
  include gen_mcollective::server
  include kbp_icinga::mcollective

  kbp_rabbitmq::client { "mcollective":; }

  file { "/etc/mcollective/facts.yaml":
    content => template("kbp_mcollective/facts"),
    require => Package["mcollective-common"];
  }
}

class kbp_mcollective::client($pass_client, $pass_server) {
  include gen_mcollective::client
  class { "kbp_rabbitmq":
    rabbitmq_name => "mcollective",
    port          => 6163,
    stomp         => true;
  }

  $user_client = "mcollective_client"
  $user_server = "mcollective_server"

  gen_rabbitmq::add_user {
    $user_client:
      password => $pass_client;
    $user_server:
      password => $pass_server;
  }

  gen_rabbitmq::set_permissions {
    "permissions for ${user_client}":
      username => $user_client;
    "permissions for ${user_server}":
      username => $user_server;
  }

  @@concat::add_content {
    "1 ${user_client} creds":
      content => template("kbp_rabbitmq/mcollective_client.cfg_connections"),
      target  => "/etc/mcollective/client.cfg";
    "1 ${user_server} creds":
      content => template("kbp_rabbitmq/mcollective_server.cfg_connections"),
      target  => "/etc/mcollective/server.cfg";
  }
}

class kbp_mcollective::disable {
  include gen_mcollective::disable
}
