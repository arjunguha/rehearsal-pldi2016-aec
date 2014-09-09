# This example adds the pe_facterci class to all nodes.  Note, the class
# requires the jenkins class to work properly.

node default {
  include pe_facterci
}
