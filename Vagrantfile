Vagrant.require_version ">= 1.6.0", "< 1.8.0"

Vagrant.configure("2") do |config|

  config.vm.box = "puppetlabs/ubuntu-14.04-64-puppet"

  config.vm.provider "vmware_fusion" do |v|
    v.vmx["memsize"] = "3072"
    v.vmx["numvcpus"] = "2"
    v.gui = false
  end

  config.vm.provision "puppet"

  config.vm.synced_folder ".", "/home/vagrant/src"

  config.vm.hostname = "vm"


end
