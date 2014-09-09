# Author: Kumina bv <support@kumina.nl>

# Class: kbp_sudo
#
# Actions:
#  Undocumented
#
# Depends:
#  gen_sudo
#  gen_puppet
#
class kbp_sudo {
  include gen_sudo
}

# Class: kbp_sudo::rule
#
# Parameters:
#  entity
#    The user or group that can use the rule
#  command
#    The command that can be run
#  as_user
#    The user the command can be ran as
#  password_required
#    Is entering a password required? Defaults to true
#  comment
#    Optional comment, if none is supplied the resource name will be used
#  preserve_env_vars
#    Do the environment vars need to be preserved? Defaults to false
#
# Actions:
#  Set up a sudo rule
#
# Depends:
#  gen_sudo
#  gen_puppet
#
define kbp_sudo::rule($entity, $command, $as_user, $password_required = true, $comment = false, $preserve_env_vars=false) {
  include kbp_sudo

  gen_sudo::rule { $name:
    entity            => $entity,
    command           => $command,
    as_user           => $as_user,
    password_required => $password_required,
    comment           => $comment,
    preserve_env_vars => $preserve_env_vars,
  }
}

