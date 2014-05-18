define logcheck::ignore($ensure=present, 
                        $rule,
                        $lvl='server',
                        $type='ignore',
                        $filename='') {
  case $type {
    'ignore': {
      $file = "/etc/logcheck/ignore.d.${lvl}/auto-puppet"
    }
    'violations','cracking': {
      $filename_real = $filename ? { '' => 'auto-puppet', default => $filename }
      $file = "/etc/logcheck/${type}.ignore.d/${filename_real}"
    }
    default: {
      fail "Uknown type $type for logcheck::ignore"
    }
  }
  concat::fragment {"set rule $name":
    target      => $file,
    content     => "$rule\n",
    ensure      => $ensure,
  }
}
