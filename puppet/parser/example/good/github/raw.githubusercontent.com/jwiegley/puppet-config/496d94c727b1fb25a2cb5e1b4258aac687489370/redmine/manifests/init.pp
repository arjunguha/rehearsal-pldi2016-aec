class redmine_1_2_0
{
  package { 'i18n':
    ensure   => '0.4.2',
    provider => gem;
  }

  package { 'rack':
    ensure   => '1.1.1',
    provider => gem;
  }

  package { 'rails':
    ensure   => '2.3.11',
    provider => gem,
    require  => Package['rack'];
  }

  package { 'passenger':
    provider => gem;
  }

  mysql_database { 'redmine':
    user     => 'redmine',
    passwd   => '6kF79TbTM9QCWrXm';
  }
}
