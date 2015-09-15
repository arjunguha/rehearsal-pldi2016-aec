define storm::service( $start = 'no', $jvm_memory = '768m', $opts = "") {

  file { "/etc/default/storm-${name}":
    include => Package['storm'],
    content => 'storm/default-service.erb',
    owner   => 'root',
    group   => 'root',
    mode    => '0644'
  }

}

storm::service { 'nimbus':
	start => 'yes',
	jvm_memory => '1024m'
}