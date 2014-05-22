class test1(
    $servicex = "sonar",
    $logfoldera = "${homex}/logs", 
    $logfoldere = "${homey}/logs", 
    $logfolderh = "${homez}/logs", 
    $logfolder = "${homex}/logs", 
    $homex = "/var/${servicex}",
    $homey = "/var/${servicex}",
    $homez = "/var/${servicex}") {

  notice($homex)
  notice($homey)
  notice($homez)
  notice("-----")
  notice($logfoldera)
  notice($logfoldere)
  notice($logfolderh)
  notice("===========")
}

class test2(
    $servicex = "sonar",
    $log_foldera = "${homex}/logs", 
    $log_foldere = "${homey}/logs", 
    $log_folderh = "${homez}/logs", 
    $logfolder = "${homex}/logs", 
    $homex = "/var/${servicex}",
    $homey = "/var/${servicex}",
    $homez = "/var/${servicex}") {

  notice($homex)
  notice($homey)
  notice($homez)
  notice("-----")
  notice($log_foldera)
  notice($log_foldere)
  notice($log_folderh)
  notice("===========")
}

class { "test1" :
}

class { "test2" :
}



/*
OUTPUT:

notice: Scope(Class[Test1]): /var/sonar
notice: Scope(Class[Test1]): /var/sonar
notice: Scope(Class[Test1]): /var/sonar
notice: Scope(Class[Test1]): -----
notice: Scope(Class[Test1]): /var/sonar/logs
notice: Scope(Class[Test1]): /logs
notice: Scope(Class[Test1]): /logs
notice: Scope(Class[Test1]): ===========
notice: Scope(Class[Test2]): /var/sonar
notice: Scope(Class[Test2]): /var/sonar
notice: Scope(Class[Test2]): /var/sonar
notice: Scope(Class[Test2]): -----
notice: Scope(Class[Test2]): /logs
notice: Scope(Class[Test2]): /var/sonar/logs
notice: Scope(Class[Test2]): /logs
notice: Scope(Class[Test2]): ===========
notice: Finished catalog run in 0.07 seconds
*/
