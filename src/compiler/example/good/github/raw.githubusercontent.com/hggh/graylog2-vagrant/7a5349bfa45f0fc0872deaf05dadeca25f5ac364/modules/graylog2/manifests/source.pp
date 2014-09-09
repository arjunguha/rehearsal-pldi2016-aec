class graylog2::source {
  apt::source { "graylog2-hggh":
    location    => "http://finja.brachium-system.net/~jonas/packages/graylog2_repro/",
    release     => "wheezy",
    repos       => "main",
    key         => "016CFFD0",
    key_server  => "pgp.surfnet.nl",
    include_src => false,
  }
}
