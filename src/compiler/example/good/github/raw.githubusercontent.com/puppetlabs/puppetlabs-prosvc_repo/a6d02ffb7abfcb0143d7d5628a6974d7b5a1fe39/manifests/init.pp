# Class: prosvc_repo
#
# This module manages prosvc_repo
#
#   It may be configured by setting the following global variables:
#
#   prosvc_repo_url: http://yum.puppetlabs.com/prosvc
#
# Parameters:
#
# Actions:
#
# Requires:
#
# Sample Usage:
#
#  Working with Vagrant, we can use the HTTP server on our laptop.
#
#  node default {
#    $prosvc_repo_url='http://10.0.2.2/yum/prosvc'
#    include prosvc_repo
#  }
#
# Or, for a dirty hack on the shell:
#
#   export FACTER_prosvc_repo_url='http://10.0.2.2/yum/prosvc'
#   puppet apply -e 'include prosvc_repo'
#
class prosvc_repo(
  $url = 'UNSET'
) {

  # Check if the url is set by the class parameter.
  if $url == 'UNSET' {
    # Then, check if there is a global variable set.
    if $prosvc_repo_url {
      # Use the URL from a global variable
      $my_url = $prosvc_repo_url
    } else {
      # Use the default URL
      $my_url = 'http://yum.puppetlabs.com/prosvc'
    }
  } else {
    # Use what was declared as a class parameter.
    $my_url = $url
  }

  file { '/etc/yum.repos.d/prosvc.repo':
    ensure  => file,
    owner   => '0',
    group   => '0',
    mode    => '0644',
    content => template("${module_name}/prosvc.repo.erb"),
    require => Exec['RPM-GPG-KEY-prosvc'],
  }

  exec { 'RPM-GPG-KEY-prosvc':
    path    => "/bin:/usr/bin:/sbin:/usr/sbin",
    command => "rpm --import '${my_url}/RPM-GPG-KEY-prosvc'",
    unless  => 'rpm -q gpg-pubkey-ed41696e-4d9dfc86',
  }

}
