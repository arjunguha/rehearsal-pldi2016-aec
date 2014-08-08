define mysql2::script(
    $want_script = true,
    $want_cron   = true,
    $want_init   = false,

    $parameters  = {},

# NOTE that your script paths may vary, particularly crons and inits
# if you have different operating systems, change these based on
# the variables ${operatingsystem}-${operatingsystemrelease}
# e.g. RedHat-6
    $script_path = '/usr/local/bin',
    $cron_path   = '/etc/cron.d',
    $init_path   = '/etc/init.d',
) {
    # We accept a hash parameters, that the various templates below may choose to use.
    validate_hash($parameters)

    # We need at least one of the want_ parameters to be true.
    if $want_script == false and $want_cron == false and $want_init == false {
        fail("mysql2::script '${title}' requires at least one of want_script, want_cron, want_init to be true.")
    }

    # Where do we get the script/cron/init templates?
    $source_prefix = "${module_name}/scripts"

    # The cron is either present with source, or absent without.
    $ensure_cron = $want_cron ? {
        true    => 'present',
        default => 'absent',
    }
    $source_cron = $want_cron ? {
        true    => template("${source_prefix}/${name}.cron"),
        default => undef,
    }

    # The init is either present with source, or absent without.
    $ensure_init = $want_init ? {
        true    => 'present',
        default => 'absent',
    }
    $source_init = $want_init ? {
        true    => template("${source_prefix}/${name}.init"),
        default => undef,
    }

    # Define the script, if wanted.
    if $want_script {
        file {
            # Script file, present if wanted, not declared at all if not.
            "${script_path}/${name}":
                ensure => true,
                mode => '0755',
                content => template("${source_prefix}/${name}");
        }
    }

    # Define the cron and init, either present or absent.
    file {
        # Script scheduling file, requires want_cron flag to be true, or will ensure absent.
        "${cron_path}/${name}":
            ensure => $ensure_cron,
            mode => '0644',
            content => $source_cron;

        # Init file. Requires "init" flag.
        "${init_path}/${name}":
            ensure => $ensure_init,
            mode => '0755',
            content => $source_init;
    }
}
