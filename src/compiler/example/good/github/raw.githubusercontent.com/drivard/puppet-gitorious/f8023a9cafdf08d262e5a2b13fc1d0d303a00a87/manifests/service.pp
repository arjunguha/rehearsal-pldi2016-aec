class gitorious::service {
  # Basic service definition
  service {
    "git-ultrasphinx":
      enable      => true,
      ensure      => running,
      hasstatus   => true,
      hasrestart  => true;

    "git-daemon":
      ensure      => running,
      hasrestart  => true;

    "git-poller":
      pattern     => "gitorious-poller",
      ensure      => running,
      hasrestart  => true;

    "activemq":
      enable      => true,
      ensure      => running,
      hasstatus   => true,
      hasrestart  => true;

    "apache2":
      enable      => true,
      ensure      => running,
      hasstatus   => true,
      hasrestart  => true;

    "sendmail":
      enable      => true,
      ensure      => running,
      hasstatus   => true,
      hasrestart  => true;
      
    "memcached":
      enable      => true,
      ensure      => running,
      hasstatus   => true,
      hasrestart  => true;
  }
}
