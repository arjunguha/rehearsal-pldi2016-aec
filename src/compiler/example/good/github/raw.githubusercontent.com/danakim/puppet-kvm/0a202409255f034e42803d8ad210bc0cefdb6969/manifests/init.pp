#
# Class: kvm
#
# A module for RedHat/CentOS based distros that ensures the KVM required packages are installed
# on a node and that the libvirtd service is running as to have a basic management tool for VMs.
# This module also configures the bridge interface - as this is the recommended networking mode for QEMU -
# and adds by default eth0 in the bridge. This is assuming "eth0" is your main interface. If not, change
# the $main_interface parameter to suit your needs. Example below.
#
# Example:
# class { "kvm":
#   main_interface => "eth0"
# }
#

class kvm (
    $main_interface = "eth0"
    ) {
    package {
        [
            "libvirt",
            "libvirt-python",
            "python-virtinst",
            "bridge-utils",
            "qemu-kvm",
        ]:
        ensure => latest
    }

    file {
        "/etc/sysconfig/network-scripts/ifcfg-$main_interface":
            mode    => 644,
            owner   => "root",
            group   => "root",
            ensure  => present,
            content => template("kvm/ifcfg-interface");
        "/etc/sysconfig/network-scripts/ifcfg-br0":
            mode    => 644,
            owner   => "root",
            group   => "root",
            ensure  => present,
            content => template("kvm/ifcfg-br0");
    }

    service { "libvirtd":
        ensure     => running,
        hasstatus  => true,
        hasrestart => true,
        require    => Package["libvirt"],
    }
}
