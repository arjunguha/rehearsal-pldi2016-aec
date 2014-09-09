# == Class zookeeper::server::jmxtrans
# Sets up a jmxtrans instance for a zookeeper Server Broker
# running on the current host.
# Note: This requires the jmxtrans puppet module found at
# https://github.com/wikimedia/puppet-jmxtrans.
#
# == Parameters
# $jmx_port      - Zookeeper JMX port
# $ganglia       - Ganglia host:port
# $graphite      - Graphite host:port
# $outfile       - outfile to which zookeeper stats will be written.
# $run_interval  - How often jmxtrans should run.        Default: 15
# $log_level     - level at which jmxtrans should log.   Default: info
#
# == Usage
# class { 'zookeeper::server::jmxtrans':
#     ganglia => 'ganglia.example.org:8649'
# }
#
class zookeeper::jmxtrans(
    $jmx_port       = $zookeeper::defaults::jmx_port,
    $ganglia        = undef,
    $graphite       = undef,
    $outfile        = undef,
    $run_interval   = 15,
    $log_level      = 'info',
) inherits zookeeper::defaults
{
    $jmx = "${::fqdn}:${jmx_port}"

    class {'::jmxtrans':
        run_interval => $run_interval,
        log_level    => $log_level,
    }

    # query for metrics from zookeeper's JVM
    jmxtrans::metrics::jvm { $jmx:
        outfile              => $outfile,
        ganglia              => $ganglia,
        graphite             => $graphite,
    }
}