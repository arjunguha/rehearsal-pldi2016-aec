$script = <<EOF
apt-get update -q
apt-get install -yq software-properties-common
add-apt-repository ppa:webupd8team/java
echo "deb https://dl.bintray.com/sbt/debian /" | sudo tee -a /etc/apt/sources.list.d/sbt.list
sudo apt-key adv --keyserver hkp://keyserver.ubuntu.com:80 --recv 642AC823

apt-get update -q

echo debconf shared/accepted-oracle-license-v1-1 select true | debconf-set-selections
apt-get install -yq oracle-java8-installer sbt unzip

wget -q http://www.scala-lang.org/files/archive/scala-2.11.7.deb
dpkg -i scala-2.11.7.deb
rm scala-2.11.7.deb
EOF

$userscript = <<EOF
cd /home/vagrant

ZIPFILE=z3-4.4.1-x64-ubuntu-14.04.zip
URL=https://github.com/Z3Prover/z3/releases/download/z3-4.4.1/$ZIPFILE
wget $URL
unzip $ZIPFILE
mv z3-4.4.1-x64-ubuntu-14.04 z3

git clone https://github.com/regb/scala-smtlib.git
cd scala-smtlib
git checkout 711e9a1ef994935482bc83ff3795a94f637f0a04
sbt publish-local
EOF

Vagrant.configure("2") do |config|

  config.vm.box = "ubuntu/trusty64"
  config.ssh.forward_x11 = false
  config.vm.synced_folder ".", "/vagrant"
  config.vm.provision "shell", inline: $script, privileged: true
  config.vm.provision "shell", inline: $userscript, privileged: false

  config.vm.provider :virtualbox do |vb|
    vb.gui = false
    vb.customize ["modifyvm", :id, "--memory", "4096"]
  end

end
