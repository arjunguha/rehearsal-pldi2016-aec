# Author: Kumina bv <support@kumina.nl>

# Class: kbp_kvm
#
# Actions:
#  Undocumented
#
# Depends:
#  gen_kvm
#  gen_apt::preference
#  gen_puppet
#
class kbp_kvm {
  include gen_kvm
  include gen_base::libcurl3_gnutls

  if $lsbdistcodename != 'lenny' {
    include gen_base::qemu_utils
  }

  if $lsbdistcodename == 'squeeze' {
    gen_apt::preference { "qemu-utils":; }
  }

  # remove backports preference when upgraded to wheezy
  if $lsbdistcodename == 'wheezy' {
    gen_apt::preference { "qemu-utils":
      ensure => absent;
    }

    gen_insserv::disable_script { 'libvirt-guests':; }
  }

  # Enable KSM
  exec { "/bin/echo 1 > /sys/kernel/mm/ksm/run":
    onlyif => "/usr/bin/test `cat /sys/kernel/mm/ksm/run` -eq 0",
  }
}
