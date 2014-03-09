apt-get update
apt-get install -y vim openjdk-7-jdk openjdk-7-jre scala curl couchdb
wget http://repo.scala-sbt.org/scalasbt/sbt-native-packages/org/scala-sbt/sbt/0.13.1/sbt.deb
dpkg -i sbt.deb

# $1 is provided through Vagrant, see provisioning in Vagrantfile
echo $1
mkdir -p /var/cook
cp /vagrant/* /var/cook/ -rf
cd /var/cook && sbt clean && sbt "project agent" "run $1"
