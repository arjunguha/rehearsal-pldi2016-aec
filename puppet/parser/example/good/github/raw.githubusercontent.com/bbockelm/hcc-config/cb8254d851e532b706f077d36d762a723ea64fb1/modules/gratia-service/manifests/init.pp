#
# Class: gratia-service
#

class gratia-service {

   package { gratia-service: name => "gratia-service", ensure => installed }

# TODO: service-configuration.properties ... once the passwords aren't kept in
# that file!

# TODO: Put server.xml in place

# TODO: Put tomcat5.conf in place

# TODO: httpcert in place and owned by tomcat

}
