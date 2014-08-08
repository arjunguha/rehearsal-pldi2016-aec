#
# hccclass machines
#

class hccclass::common {

    ssh_authorized_key { 'root@red-man.unl.edu':
        ensure => present,
        key    => 'AAAAB3NzaC1yc2EAAAABIwAAAQEA3n0Auikb9DBXnMB1z+K1fym59ppEMVB+jvR86kdoyW4GMsnjp0u0MbC29ycCOvPuNg35DSKLNy0SAzBbyuH8ZxfxxTgYtQVeidgTqP0Ot2hac++Iz48/6Yyc8R+qaq6FTuxkeJmPT4wtA1ZjtT5MOZkepYMSCIyM6r4Ey8diTlqpHkqMfHGu9KFJMnux0tqEbZmI2KNXcujbcQ5FBbgZe4YnKFDk3bPnGqxpAgb6FrwUHL4BgVvJlOE2E04i7Zo9M+fB+dHvf1XzJIJ5weoVDUxVUBmEUpOhwdJwBuvCk9R2Ltsga5Jioeau9SgNYZd9uVNr5FY/omAwq2QMVaQPdQ==',
        type   => 'ssh-rsa',
        user   => 'root',
    }

    ssh_authorized_key { 'root@redtro.red.hcc.unl.edu':
        ensure => present,
        key    => 'AAAAB3NzaC1yc2EAAAADAQABAAABAQC8HHX5UzHWEWRp+gDp/vPstyAK64UmSMHpzemgBYIbFJXLSJtHEGd3aQ35gSpfhIJxUGj/kqNAG+2mrOdJlIBZBvgT4rD0Me3gyr1GUcZYKlCfe+uNjCbVXO0qageoZ/wgbsJsLqRw+cf8JmnUPu0ttGZA+zEAn3iTdVldTOqd7/b8JYCMV6oMMxkbE0BVyQqT5y5ZHX+7wqBMeljUJtCoxTuT5/trAc/8+eYqKfIC8HuLcevHR86CamNFy9yb2n7GsbQEM4/VJmlnexoaWjPW9iydsm9ImRYi8R8hGZk0bY8NI1nRIKN/uOlnQgliGQghecHki0Tiygjd0xVs598L',
        type   => 'ssh-rsa',
        user   => 'root',
    }

}
