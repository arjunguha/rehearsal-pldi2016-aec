# Author: Kumina bv <support@kumina.nl>

# Class: kbp_ceph
#
# Actions:
#  Setup ceph with btrfs for usage. You still need to manually create the
#  required partitions.
#
# Depends:
#  kbp_btrfs
#  kbp_ceph
#  gen_puppet
#
class kbp_ceph {
  include kbp_btrfs
  include gen_ceph
}
