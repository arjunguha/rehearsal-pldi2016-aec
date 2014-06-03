$fqdn = 'zoo1.domain.org'

class { 'zookeeper':
    hosts    => { 'zoo1.domain.org' => 1, 'zoo2.domain.org' => 2, 'zoo3.domain.org' => 3 },
    data_dir => '/var/lib/zookeeper',
}
