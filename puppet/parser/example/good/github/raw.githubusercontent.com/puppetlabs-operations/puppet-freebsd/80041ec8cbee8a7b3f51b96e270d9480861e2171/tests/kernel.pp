# Creates a firewall kernel configuration
freebsd::kernel {
  "firewall":
    options => [
      "ipsec",
      "altq",
      "altq_cbq",
      "altq_red",
      "altq_rio",
      "altq_hsfc",
      "altq_priq",
      "altq_nopcc",
    ],
    devices => [
      'crypto',
      'pf',
      'pflog',
      'pfsync',
    ]
}
