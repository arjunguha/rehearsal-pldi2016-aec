class opdemand::common {
  
  # include base modules
  include apt
  include stdlib
      
  # manage orchestration inputs
  class {"opdemand::inputs":} ->
    
  # process ssh data
  class {"opdemand::ssh::dirs":} ->
  class {"opdemand::ssh::authorized_keys":} ->
  class {"opdemand::ssh::known_hosts":} ->
  class {"opdemand::ssh::private_keys":}
  
}
