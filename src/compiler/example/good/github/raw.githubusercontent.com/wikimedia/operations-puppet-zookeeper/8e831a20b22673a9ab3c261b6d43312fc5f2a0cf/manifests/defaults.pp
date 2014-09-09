# == Class zookeeper::defaults
# Default zookeeper configs.
class zookeeper::defaults {
    $hosts            = { "${::fqdn}" => 1 }

    $data_dir         = '/var/lib/zookeeper'
    $data_log_dir     = undef
    $jmx_port         = 9998
    $cleanup_count    = 10
    $cleanup_script   = '/usr/share/zookeeper/bin/zkCleanup.sh'

    # Default puppet paths to template config files.
    # This allows us to use custom template config files
    # if we want to override more settings than this
    # module yet supports.
    $conf_template    = 'zookeeper/zoo.cfg.erb'
    $default_template = 'zookeeper/zookeeper.default.erb'
    $log4j_template   = 'zookeeper/log4j.properties.erb'

    # Zookeeper package version.
    $version          = 'installed'
}
