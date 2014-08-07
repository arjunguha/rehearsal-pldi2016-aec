Vagrant.require_version ">= 1.6.0", "< 1.7.0"

$script = <<EOF
set -x

SCALA_VERSION=2.10.4
SBT_VERSION=0.13.5
JAVA_VERSION=8

apt-get update -q
apt-get upgrade -yq
apt-get install -yq \
  docker.io \
  software-properties-common \
  facter

echo 'DOCKER_OPTS="-H tcp://127.0.0.1:2375 -H tcp://127.0.0.1:4243 -H unix:///var/run/docker.sock"' > /etc/default/docker.io

service docker.io restart

ln -s /usr/bin/docker.io /usr/bin/docker

 usermod -a -G docker vagrant

add-apt-repository ppa:webupd8team/java
apt-get update -q

echo debconf shared/accepted-oracle-license-v1-1 select true | \
  debconf-set-selections

apt-get install -yq oracle-java${JAVA_VERSION}-installer

wget -q http://www.scala-lang.org/files/archive/scala-${SCALA_VERSION}.deb
wget -q http://dl.bintray.com/sbt/debian/sbt-${SBT_VERSION}.deb
dpkg -i sbt-${SBT_VERSION}.deb
dpkg -i scala-${SCALA_VERSION}.deb
rm sbt-${SBT_VERSION}.deb scala-${SCALA_VERSION}.deb

apt-get install -f -q

EOF

Vagrant.configure("2") do |config|

  config.vm.box = "ubuntu/trusty64"

  config.vm.provider "virtualbox" do |v|
    v.memory = 2048
    v.cpus = 2
  end

  config.vm.provision :shell, inline: $script

  config.vm.synced_folder ".", "/home/vagrant/src"

  config.vm.hostname = "puppetvm"


end
