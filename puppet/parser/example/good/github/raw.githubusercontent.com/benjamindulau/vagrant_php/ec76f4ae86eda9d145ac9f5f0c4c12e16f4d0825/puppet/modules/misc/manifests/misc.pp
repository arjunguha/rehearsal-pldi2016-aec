class misc::misc {
    package { ["vim", "curl", "nfs-common"]:
        ensure => latest,
        require => Exec["aptGetUpdate"],
    }
}