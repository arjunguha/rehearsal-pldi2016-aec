define kbp_ksplice($ensure='present') {
  if $ensure == 'present' {
    include gen_base::python_pycurl
    include kbp_icinga::ksplice
  }
  class { 'ksplice':
    ensure => $ensure;
  }
}

define kbp_ksplice::proxy ($proxy) {
  ksplice::proxy { $name:
    proxy => $proxy;
  }
}
