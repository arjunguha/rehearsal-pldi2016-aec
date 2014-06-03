# Demo: NoOp
# This class inherits the motd class but marks the
# resource as noop to introduce pending resources
# into the catalog
class pe_demo::motd::noop inherits pe_demo::motd {

  File['/etc/motd'] {
    noop => true,
  }

}
