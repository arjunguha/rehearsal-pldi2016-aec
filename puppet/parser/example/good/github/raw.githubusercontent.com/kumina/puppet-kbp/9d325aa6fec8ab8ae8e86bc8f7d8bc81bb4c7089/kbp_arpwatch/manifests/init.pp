# Author: Kumina bv <support@kumina.nl>

# Class: kbp_arpwatch
#
# Actions:
#  Setup arpwatch.
#
# Depends:
#  arpwatch
#  kbp_icinga
#
class kbp_arpwatch {
  include arpwatch

  File <| title == "/etc/default/arpwatch" |> {
    content => template("kbp_arpwatch/arpwatch"),
  }

  kbp_icinga::service { "arpwatch":
    service_description => "Arpwatch daemon",
    check_command       => "check_arpwatch",
    nrpe                => true;
  }
}

# Class: kbp_arpwatch::disable
#
# Actions: Remove arpwatch from a machine
#
# Depends:
#  arpwatch
#
class kbp_arpwatch::disable {
  include arpwatch::disable
}
