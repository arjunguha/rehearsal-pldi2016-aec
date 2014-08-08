# Author: Kumina bv <support@kumina.nl>

# Class: kbp_ipsec
#
# Actions:
#  Configure basic ipsec settings; needs at least one kbp_ipsec::peer.
#
# Parameters:
#  listen
#    The IP address(es) that racoon listens on (default all)
#  ssl_path
#    The default path to ssl certificates (default /etc/ssl)
#
# Depends:
#  gen_ipsec
#
class kbp_ipsec ($listen=false, $ssl_path="/etc/ssl") {
  class { "gen_ipsec":
    listen => $listen,
    ssl_path => $ssl_path;
  }
}

# Define: kbp_ipsec::peer
#
# Actions:
#  Configure an ipsec peer
#  A key and certificate need to be created in advance.
#
# Parameters:
#  local_ip
#    Local endpoint of the ipsec tunnel
#  peer_ip
#    Remote endpoint of the ipsec tunnel
#  encap
#    Encapsulation mode. Must be "tunnel" (default) or "transport"
#  exchange_mode
#    Phase 1 exchange mode (optional, default "main")
#  proposal_check
#    racoon's proposal check (see racoon(8)) (optional, default "obey")
#  peer_asn1dn
#    Peer's ASN.1 DN (Everything after "Subject: " in output of openssl x509 -text)
#  localnet
#    (List of) local networks (e.g. ["10.1.2.0/24","10.1.4.0/23"])
#  remotenet
#    (List of) remote networks
#  authmethod
#    Phase 1 authentication method. Can be "rsasig" (default) or "psk"/"pre_shared_key"
#  psk
#    In case of authmethod=psk: the pre-shared key to be used
#  cert
#    Path to certificate file (optional)
#  key
#    Path to private key file (optional)
#  cafile
#    Path to CA certificate (optional)
#  phase1_enc
#    Phase 1 encryption algorithm (optional)
#  phase1_hash
#    Phase 1 hash algorithm (optional)
#  phase1_dh
#    Phase 1 Diffie-Hellman group (optional)
#  phase1_lifetime_time (optional)
#    Phase 1 lifetime (time); can be sec, min or hour (e.g. "12 hour")
#  phase2_dh
#    Phase 2 Diffie-Hellman group (optional)
#  phase2_enc
#    Phase 2 encryption algorithm (optional)
#  phase2_auth
#    Phase 2 authentication method (optional)
#  phase2_lifetime_time (optional)
#    Phase 2 lifetime (time); can be sec, min or hour (e.g. "12 hour")
#  policy_level
#    Policy level (search for "level" in setkey(8)) (optional)
#  monitoring_remote_ip
#    Remote IP to be checked (ping) by monitoring
#
# Depends:
#  gen_ipsec
#  kbp_ferm
#
define kbp_ipsec::peer ($local_ip, $peer_ip, $encap="tunnel", $exchange_mode="main", $proposal_check=false, $peer_asn1dn=false, $localnet=false, $remotenet=false, $authmethod="rsasig", $psk=false, $cert="certs/${fqdn}.pem", $key="private/${fqdn}.key", $cafile="cacert.pem", $phase1_enc="aes 256", $phase1_hash="sha1", $phase1_dh="5", $phase1_lifetime_time=false, $phase2_dh="5", $phase2_enc="aes 256", $phase2_auth="hmac_sha1", $phase2_lifetime_time=false, $policy_level="unique", $monitoring_remote_ip=false) {
  gen_ipsec::peer { $name:
    local_ip      => $local_ip,
    peer_ip       => $peer_ip,
    encap         => $encap,
    exchange_mode => $exchange_mode,
    proposal_check => $proposal_check,
    peer_asn1dn   => $peer_asn1dn,
    localnet      => $localnet,
    remotenet     => $remotenet,
    authmethod    => $authmethod,
    psk           => $psk,
    cert          => $cert,
    key           => $key,
    cafile        => $cafile,
    phase1_enc    => $phase1_enc,
    phase1_hash   => $phase1_hash,
    phase1_dh     => $phase1_dh,
    phase1_lifetime_time => $phase1_lifetime_time,
    phase2_dh     => $phase2_dh,
    phase2_enc    => $phase2_enc,
    phase2_auth   => $phase2_auth,
    phase2_lifetime_time => $phase2_lifetime_time,
    phase2_lifetime_byte => $phase2_lifetime_byte,
    policy_level  => $policy_level;
  }

  kbp_ferm::rule {
    "ESP from IPSEC peer $name":
      saddr  => $peer_ip,
      proto  => "esp",
      action => "ACCEPT";
    "ISAKMP from IPSEC peer $name":
      saddr  => $peer_ip,
      proto  => "udp",
      dport  => 500,
      action => "ACCEPT";
  }

  if $monitoring_remote_ip {
    kbp_ipsec::monitoring { $monitoring_remote_ip:
      peer => $name;
    }
  }
}

define kbp_ipsec::monitoring ($peer) {
  kbp_icinga::ipsec { "${fqdn}_${peer}_${name}":
    monitoring_remote_ip => $name;
  }
}
