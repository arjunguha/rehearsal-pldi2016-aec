#!/bin/bash
$root=parser-tests/good

./run.sh deterbench monit $root/dhoppe-monit.pp ubuntu-trusty prune
./run.sh deterbench monit $root/dhoppe-monit.pp ubuntu-trusty noprune

      bench("monit", s"$root/dhoppe-monit.pp", g => isDeterministic(g) == true)
      bench("bind", s"$root/thias-bind.pp", g => isDeterministic(g) == true)
      bench("hosting", s"$root/puppet-hosting-fixed.pp", g => isDeterministic(g) == true)
      bench("dns", s"$root/antonlindstrom-powerdns.pp", g => isDeterministic(g) == false)
      // bench("irc", s"$root/spiky-reduced.pp", g => isDeterministic(g) == false, onlySliced = true, os = "centos-6")
      bench("xinetd", s"$root/ghoneycutt-xinetd.pp", g => isDeterministic(g) == false)
      bench("jpa", s"$root/pdurbin-java-jpa-tutorial.pp", g => isDeterministic(g) == true, os = "centos-6")
      bench("ntp", s"$root/thias-ntp.pp", g => isDeterministic(g) == false)
      bench("rsyslog", s"$root/xdrum-rsyslog.pp", g => isDeterministic(g) == false)
      bench("nginx", s"$root/BenoitCattie-puppet-nginx.pp", g => isDeterministic(g) == true)
      bench("amavis", s"$root/mjhas-amavis.pp", g => isDeterministic(g) == true)
      bench("clamav", s"$root/mjhas-clamav.pp", g => isDeterministic(g) == true)
      bench("logstash", s"$root/Nelmo-logstash.pp", g => isDeterministic(g) == false)
