#
# This file is part of puppet-phpsysinfo ( https://github.com/drivard/puppet-phpsysinfo ).
#
# Copyright (C) 2011 Dominick Rivard <dominick.rivard@gmail.com>
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

#
# This configuration will install PhpSysInfo into /usr/share/phpsysinfo
# and will create a virtualhost configuration file that will listen to port 8001.
# To access PhpSysInfo go to: http://your_server_hostname:8001/
#
node "gitorious.dr" {
  #
  # Custom Variables
  #

  #
  # Server configuration
  #
  class {
    'gitorious':
      mysql_server => "127.0.0.1";
  }

  # Modules
  include gitorious
}
