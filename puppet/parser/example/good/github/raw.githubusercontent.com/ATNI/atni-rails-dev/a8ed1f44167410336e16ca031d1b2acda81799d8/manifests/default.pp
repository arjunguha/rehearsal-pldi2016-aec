# Pre-install.
stage { 'preinstall':
  before => Stage['main']
}

class yum_update {
  exec { '/usr/bin/yum -y update':
    user => 'root',
    timeout => 0
  }
}

class { 'yum_update':
  stage => preinstall
}

# Install Ruby and its requirements.
package { [ 'gcc-c++',
  'patch',
  'readline',
  'readline-devel',
  'zlib',
  'zlib-devel',
  'libffi-devel',
  'openssl-devel',
  'make',
  'bzip2',
  'autoconf',
  'automake',
  'libtool',
  'bison',
  'git',
  'zsh']:
  ensure => installed
}

# Setup zsh.
user { "vagrant":
 ensure => present,
 shell => "/bin/zsh"
}

# Install oh-my-zsh.
exec { 'oh-my-zsh':
  command => 'git clone https://github.com/robbyrussell/oh-my-zsh.git /home/vagrant/.oh-my-zsh',
  path => [ '/bin', '/usr/bin' ],
  creates => '/home/vagrant/.oh-my-zsh/oh-my-zsh.sh',
  user => 'vagrant'
}

# Copy over the oh-my-zsh zshrc.
file { 'copy-new-zshrc':
  path => '/home/vagrant/.zshrc',
  source => '/home/vagrant/.oh-my-zsh/templates/zshrc.zsh-template',
  owner => 'vagrant'
}

# Setup rbenv in the .zshrc file.
rbenv::install { "vagrant":
  home => '/home/vagrant',
  rc => '.zshrc',
  before => Exec['get-vim-src']
}

# Compile Ruby.
rbenv::compile { "1.9.3-p484":
  user => "vagrant",
  home => "/home/vagrant",
  global => true
}

# Install Rails.
rbenv::gem { "rails":
  ensure => "3.2.15",
  user => "vagrant",
  ruby => "1.9.3-p484"
}

# Install therubyracer.
rbenv::gem { "therubyracer":
  user => "vagrant",
  ruby => "1.9.3-p484"
}

# Install SQLite.
package { [ 'sqlite', 'sqlite-devel']:
  ensure => installed;
}

# Install MySQL.
package { [ 'mysql',
  'mysql-devel',
  'mysql-libs']:
  ensure => installed
}

# Install pre-reqs for vim.
package { [ 'mercurial',
  'ncurses',
  'ncurses-devel',
  'perl-devel',
  'python-devel',
  'ruby-devel',
  'perl-ExtUtils-Embed']:
  ensure => installed,
  before => Exec['get-vim-src']
}

# Grab a copy of the vim source code.
exec { 'get-vim-src':
  command => 'hg clone https://vim.googlecode.com/hg/ /opt/vim-src',
  path => [ '/bin', '/usr/bin' ],
  creates => '/opt/vim-src/README.txt',
  user => 'root',
  timeout => 0,
  before => Exec['run-vim-configure']
}

# Configure vim for compile.
exec { 'run-vim-configure':
  command => 'configure --prefix=/opt/vim --with-features=huge --enable-rubyinterp --enable-pythoninterp',
  path => [ '/opt/vim-src', '/bin/', '/usr/bin' ],
  creates => '/opt/vim-src/src/auto/config.cache',
  cwd => '/opt/vim-src',
  user => 'root',
  before => Exec['compile-vim']
}

# Compile vim.
exec { 'compile-vim':
  command => 'make',
  path => [ '/bin/', '/usr/bin' ],
  cwd => '/opt/vim-src',
  creates => '/opt/vim-src/src/vim',
  user => 'root',
  before => Exec['install-vim']
}

# Install vim.
exec { 'install-vim':
  command => 'make install',
  path => [ '/bin/', '/usr/bin' ],
  cwd => '/opt/vim-src',
  creates => '/opt/vim/bin/vim',
  user => 'root',
  before => Exec['add-path-vim']
}

# Add the new vim to our path.
exec { 'add-path-vim':
  command => "echo 'export PATH=/opt/vim/bin:\$PATH' >> /home/vagrant/.zshrc",
  path => [ '/bin/', '/usr/bin' ],
  unless => 'grep "/opt/vim/bin" /home/vagrant/.zshrc 2>/dev/null',
  user => 'vagrant',
  before => Exec['install-vimpire']
}

# Install vimpire.
exec { 'install-vimpire':
  command => 'git clone --recursive https://github.com/ATNI/vimpire.git /home/vagrant/.vim',
  path => [ '/bin', '/usr/bin' ],
  creates => '/home/vagrant/.vim/README.md',
  user => 'vagrant',
  timeout => 0,
  before => File['copy-vimrc']
}

# Copy over vimpire's vimrc.
file { 'copy-vimrc':
  path => '/home/vagrant/.vimrc',
  source => '/home/vagrant/.vim/etc/vimrc',
  owner => 'vagrant'
}

# Add firewall exceptions for Rails development.
file { 'add-rails-to-firewall':
  path => '/etc/sysconfig/iptables',
  owner => 'root',
  group => 'root',
  mode => '0600',
  content => template('iptables/iptables.erb'),
  before => Exec['restart-iptables']
}

# Restart iptables so that the new rules take effect.
exec { 'restart-iptables':
  command => 'iptables restart',
  path => [ '/etc/init.d', '/bin', '/usr/bin' ],
  user => 'root'
}

# Install pre-reqs for git.
package { [ 'expat-devel',
  'perl-ExtUtils-MakeMaker',
  'gettext-devel',
  'libcurl-devel']:
  ensure => installed,
  before => Exec['get-git-src']
}
# Grab the git source
exec { 'get-git-src':
  command => 'git clone https://github.com/git/git.git /opt/git-src',
  path => [ '/bin', '/usr/bin' ],
  creates => '/opt/git-src/README',
  user => 'root',
  timeout => 0,
  before => Exec['checkout-git-version']
}

# Checkout the newest version of git.
exec { 'checkout-git-version':
  command => 'git checkout v1.8.4.3',
  path => [ '/bin', '/usr/bin' ],
  unless => 'git branch | grep v1.8.4.3 2>/dev/null',
  cwd => '/opt/git-src',
  user => 'root',
  before => Exec['compile-git']
}

# Compile git.
exec { 'compile-git':
  command => 'make prefix=/opt/git all',
  path => [ '/bin', '/usr/bin' ],
  creates => '/opt/git-src/git',
  cwd => '/opt/git-src',
  user => 'root',
  before => Exec['install-git']
}

# Install git.
exec { 'install-git':
  command => 'make prefix=/opt/git install',
  path => [ '/bin', '/usr/bin' ],
  creates => '/opt/git/bin/git',
  cwd => '/opt/git-src',
  user => 'root',
  before => Exec['add-path-git']
}

# Add the new git to our path.
exec { 'add-path-git':
  command => "echo 'export PATH=/opt/git/bin:\$PATH' >> /home/vagrant/.zshrc",
  path => [ '/bin/', '/usr/bin' ],
  unless => 'grep "/opt/git/bin" /home/vagrant/.zshrc 2>/dev/null',
  user => 'vagrant',
}
