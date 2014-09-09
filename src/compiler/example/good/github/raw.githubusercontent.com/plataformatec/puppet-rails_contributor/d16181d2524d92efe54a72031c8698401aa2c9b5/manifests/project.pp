# Public: Clone a rails project
#
# Usage:
#
#   rails_contributor::project { 'rails': }
define rails_contributor::project($dirname = $title) {
  $dir = "${rails_contributor::dir}/${dirname}"

  repository { $dir:
    source => "rails/${title}"
  }
}
