
class yum::repo::hcc {

    # we have different repo paths for el5 and el6 due to mash naming issues
    case $::lsbmajdistrelease {

        5: {
            $hcc_repo_url = 'http://t2.unl.edu/store/repos/hcc/5/hcc-el5/$basearch'
            $hcc_testing_repo_url = 'http://t2.unl.edu/store/repos/hcc/5/hcc-testing-el5/$basearch'
        }

        6: {
            $hcc_repo_url = 'http://t2.unl.edu/store/repos/hcc/6/hcc-el6/$basearch'
            $hcc_testing_repo_url = 'http://t2.unl.edu/store/repos/hcc/6/hcc-el6-testing/$basearch'
        }

        default: { fail('no hcc repo defined for this distro release') }
    }

    yum::managed_yumrepo {

        'hcc':
            descr    => "HCC RPMs for EL$::lsbmajdistrelease - \$basearch",
            baseurl  => $hcc_repo_url,
            enabled  => 1,
            gpgcheck => 0,
            priority => 9 ;

        'hcc-testing':
            descr    => "HCC RPMs for EL$::lsbmajdistrelease - \$basearch - Testing",
            baseurl  => $hcc_testing_repo_url,
            enabled  => 0,
            gpgcheck => 0,
            priority => 9 ;

    }   # end yum::managed_repo

}
