wget -q https://apt.puppetlabs.com/puppetlabs-release-precise.deb
sudo dpkg -i puppetlabs-release-precise.deb
rm puppetlabs-release-precise.deb
sudo apt-get update -qq
sudo apt-get install -y -qq vim
