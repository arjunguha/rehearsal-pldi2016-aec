# Author: Kumina bv <support@kumina.nl>

# Define: kbp_cifs::mount
#
# Actions:
#  Mount CIFS share from remote server
#
# Parameters:
#   name
#    Mountpoint
#   ensure
#    Same values as mount resource (http://docs.puppetlabs.com/references/stable/type.html#mount), default 'mounted'
#   unc
#    Uniform Naming Convention (http://en.wikipedia.org/wiki/Path_%28computing%29#Uniform_Naming_Convention), e.g. //servername/sharename/foo
#   options
#    Mount options, default 'rw'
#   username
#    CIFS username
#   password
#    CIFS password
#   domain
#    CIFS domain
#   user
#    The user that the files and dirs in the mount belong to (used when the SMB server does not support unix-type file permissions)
#   group
#    The group that the files and dirs in the mount belong to (used when the SMB server does not support unix-type file permissions)
#   dir_perms
#    The permissions of the directories within the mount in OCTAL (used when the SMB server does not support unix-type file permissions)
#   file_perms
#    The permissions of the files within the mount in OCTAL (used when the SMB server does not support unix-type file permissions)
#
# Depends:
#  gen_cifs
#
define kbp_cifs::mount($ensure='mounted', $unc, $options='rw', $user='root', $group='root', $dir_perms='0755', $file_perms='0644', $username, $password, $domain) {
  gen_cifs::mount { $name:
    ensure     => $ensure,
    unc        => $unc,
    options    => $options,
    username   => $username,
    password   => $password,
    user       => $user,
    group      => $group,
    dir_perms  => $dir_perms,
    file_perms => $file_perms,
    domain     => $domain;
  }

  kbp_backup::exclude { "exclude_cifsmount_${name}":
    content => "${name}/*";
  }

  kbp_icinga::mount { $name:; }
}
