# Author: Kumina bv <support@kumina.nl>

# Class: kbp_pagespeed
#
# Actions:
#  Setup mod-pagespeed so we can setup config on a per-vhost basis. This creates some
#  basic config and makes sure the module is available.
#
# Depends:
#  gen_pagespeed
#  kbp_apache
#
class kbp_pagespeed {
  include kbp_apache
  include gen_pagespeed

  kbp_apache::module { 'pagespeed':; }

  # Override the global config by a very minimal config. This essentially disabled pagespeed.
  file { "/etc/apache2/mods-enabled/pagespeed.conf":
    content => template('kbp_pagespeed/global-config'),
    notify  => Exec['reload-apache2'],
  }

  # Create the directories we require, we add subdirectories in these on a per-site basis.
  file { ['/srv/mod_pagespeed','/srv/mod_pagespeed/cache','/srv/mod_pagespeed/files']:
    ensure => directory,
    owner  => 'www-data',
  }
}

# Define: kbp_pagespeed::site
#
# Action:
#  Setup mod_pagespeed for a site with selected options. You choose either a selection or
#  you add a whole bunch of options. All options are off by default when using selection
#  'none'.
#
# Parameters:
#  name
#   Should be the non-SSL site, like www.example.com_80.
#  ssl_also
#   Whether this is an ssl site as well. If there's no non-SSL site, use the port
#   parameter. Defaults to false.
#  selection
#   Use default selections. Options are 'none' (which uses the settings you add, the
#   default), 'safe' (the core selection Google recommends), 'max' (which sets all
#   non-destructive settings possible) or 'defaults' (selection we use per default).
#   Defaults to 'none'.
#  add_head
#   The 'Add Head' filter is very simple: it adds a head to the document if it
#   encounters a <body> tag before finding a <head> tag.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-head-add
#  combine_css
#   'Combine CSS' seeks to reduce the number of HTTP requests made by a browser during
#   page refresh by replacing multiple distinct CSS files with a single CSS file,
#   containing the contents of all of them.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-combine
#  convert_meta_tags
#   The 'Convert Meta Tags' filter adds a response header that matches each meta tagi
#   with an http-equiv attribute.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-convert-meta-tags
#  extend_cache
#   Extends cache lifetime of all resources by signing URLs with content hash.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-cache-extend
#  inline_css
#   Inlines small CSS files into the HTML document.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-inline
#  inline_import_to_link
#   Inlines <style> tags comprising a single CSS @import by converting them to
#   equivalent <link> tags.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-inline-import
#  inline_javascript
#   Inlines small JS files into the HTML document.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-js-inline
#  rewrite_css
#   Rewrites CSS files to remove excess whitespace and comments, and, if enabled,
#   rewrite or cache-extend images referenced in CSS files.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-rewrite
#  rewrite_images
#   Optimizes images, re-encoding them, removing excess pixels, and inlining small
#   images.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize
#  rewrite_javascript
#   Rewrites Javscript files to remove excess whitespace and comments.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-js-minify
#  rewrite_style_attributes_with_url
#   Rewrite the CSS in style attributes if it contains the text 'url(' by applying
#   the configured rewrite_css filter to it
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-rewrite-style-attributes
#  trim_urls
#   Shortens URLs by making them relative to the base URL.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-trim-urls
#  combine_heads
#   Combines multiple <head> elements found in document into one.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-head-combine
#  strip_scripts
#   Removes all script tags from document to help run experiments.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-strip-scripts
#  outline_css
#   Externalize large blocks of CSS into a cacheable file.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-outline
#  outline_javascript
#   Externalize large blocks of JS into a cacheable file.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-js-outline
#  move_css_above_scripts
#   Moves CSS elements above <script> tags.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-above-scripts
#  move_css_to_head
#   Moves CSS elements into the <head>.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-css-to-head
#  rewrite_style_attributes
#   Rewrite the CSS in style attributes by applying the configured rewrite_css
#   filter to it.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-rewrite-style-attributes
#  flatten_css_imports
#   Inline CSS by flattening all @import rules.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-flatten-css-imports
#  make_google_analytics_async
#   Convert synchronous use of Google Analytics API to asynchronous.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-make-google-analytics-async
#  combine_javascript
#   Combines multiple script elements into one.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-js-combine
#  local_storage_cache
#   Cache inlined resources in HTML5 local storage.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-local-storage-cache
#  insert_ga
#   Adds the Google Analytics snippet to each HTML page.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-insert-ga
#  convert_jpeg_to_progressive
#   Convert larger jpegs to progressive format.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize#progressive
#  convert_png_to_jpeg
#   Converts gif and png images into jpegs.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize#png_to_jpeg
#  convert_jpeg_to_webp
#   Generates webp rather than jpeg images for browsers that support webp.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize#webp
#  insert_image_dimensions
#   Adds width and height attributes to <img> tags that lack them.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize#dimensions
#  inline_preview_images
#   Uses inlined low-quality images as placeholders which will be replaced with
#   original images once the web page is loaded.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize#inline_preview_images
#  resize_mobile_images
#   Works just like inline_preview_images, but uses smaller placeholder images
#   for mobile browsers.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-optimize#resize_mobile_images
#  remove_comments
#   Removes comments in HTML files (but not in inline JavaScript or CSS).
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-comment-remove
#  collapse_whitespace
#   Removes excess whitespace in HTML files (avoiding <pre>, <script>, <style>, and <textarea>).
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-whitespace-collapse
#  elide_attributes
#   Removes attributes which are not significant according to the HTML spec.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-attribute-elide
#  sprite_images
#   Combine background images in CSS files into one sprite.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-image-sprite
#  rewrite_domains
#   Rewrites the domains of resources not otherwise touched by mod_pagespeed, based on
#   ModPagespeedMapRewriteDomain and ModPagespeedShardDomain settings.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-domain-rewrite
#  remove_quotes
#   Removes quotes around HTML attributes that are not lexically required.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-quote-remove
#  add_instrumentation
#   Adds JavaScript to page to measure latency and send back to the server.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-instrumentation-add
#  defer_javascript
#   Defers the execution of javascript in HTML until page load complete.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-js-defer
#  inline_preview_images
#   Serves low quality images, which are replaced with high resolution images after
#   onload.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-inline-preview-images
#  lazyload_images
#   Loads images when they become visible in the client viewport.
#   https://developers.google.com/speed/docs/mod_pagespeed/filter-lazyload-images
#
# Depends:
#  kbp_pagespeed
#  kbp_apache
#
# TODO:
#  - Test if an apache reload is good enough for changing the site-specific settings.
#
define kbp_pagespeed::site ($ssl_also = false, $selection = 'none', $add_head = false, $combine_css = false, $convert_meta_tags = false, $extend_cache = false,
                            $inline_css = false, $inline_import_to_link = false, $inline_javascript = false, $rewrite_css = false, $rewrite_images = false,
                            $rewrite_javascript = false, $rewrite_style_attributes_with_url = false, $trim_urls = false, $combine_heads = false, $strip_scripts = false,
                            $outline_css = false, $outline_javascript = false, $move_css_above_scripts = false, $move_css_to_head = false, rewrite_style_attributes = false,
                            $flatten_css_imports = false, $make_google_analytics_async = false, $combine_javascript = false, $local_storage_cache = false, $insert_ga = false,
                            $convert_jpeg_to_progressive = false, $convert_png_to_jpeg = false, $convert_jpeg_to_webp = false, $insert_image_dimensions = false,
                            $inline_preview_images = false, $resize_mobile_images = false, $remove_comments = false, $collapse_whitespace = false, elide_attributes = false,
                            $sprite_images = false, $rewrite_domains = false, $remove_quotes = false, $add_instrumentation = false, $defer_javascript = false,
                            $inline_preview_images = false, $lazyload_images = false, $ports = '8080') {
  include kbp_pagespeed

  # Get the name without the port added.
  $real_name = regsubst($name,'^(.*)_(.*)$','\1')

  # If we set this up for SSL also, we simply copy the config into the default ssl vhost-additions directory.
  # I so wish there was a nicer way of doing this!
  if $ssl {
    kbp_pagespeed::site { "${real_name}_443":
      ssl_also                          => false,
      selection                         => $selection,
      add_head                          => $add_head,
      combine_css                       => $combine_css,
      convert_meta_tags                 => $convert_meta_tags,
      extend_cache                      => $extend_cache,
      inline_css                        => $inline_css,
      inline_import_to_link             => $inline_import_to_link,
      inline_javascript                 => $inline_javascript,
      rewrite_css                       => $rewrite_css,
      rewrite_images                    => $rewrite_images,
      rewrite_javascript                => $rewrite_javascript,
      rewrite_style_attributes_with_url => $rewrite_style_attributes_with_url,
      trim_urls                         => $trim_urls,
      combine_heads                     => $combine_heads,
      strip_scripts                     => $strip_scripts,
      outline_css                       => $outline_css,
      outline_javascript                => $outline_javascripts,
      move_css_above_scripts            => $move_css_above_scripts,
      move_css_to_head                  => $move_css_to_head,
      rewrite_style_attributes          => $rewrite_style_attributes,
      flatten_css_imports               => $flatten_css_imports,
      make_google_analytics_async       => $make_google_analytics_async,
      combine_javascript                => $combine_javascript,
      local_storage_cache               => $local_storage_cache,
      insert_ga                         => $insert_ga,
      convert_jpeg_to_progressive       => $convert_jpeg_to_progressive,
      convert_png_to_jpeg               => $convert_png_to_jpeg,
      convert_jpeg_to_webp              => $convert_jpeg_to_webp,
      insert_image_dimensions           => $insert_image_dimensions,
      inline_preview_images             => $inline_preview_images,
      resize_mobile_images              => $resize_mobile_images,
      remove_comments                   => $remove_comments,
      collapse_whitespace               => $collapse_whitespace,
      elide_attributes                  => $elide_attributes,
      sprite_images                     => $sprite_images,
      rewrite_domains                   => $rewrite_domains,
      remove_quotes                     => $remove_quotes,
      add_instrumentation               => $add_instrumentation,
      defer_javascript                  => $defer_javascript,
      inline_preview_images             => $inline_preview_images,
      lazyload_images                   => $lazyload_images,
    }
  }

  # This creates a site-specific cache location. By not using the global caching directories, removing a site entirely can be easier.
  # The 'if ! defined' is needed for the SSL sites that would create the same directories.
  if ! defined(File["/srv/mod_pagespeed/cache/${real_name}"]) {
    file { "/srv/mod_pagespeed/cache/${real_name}":
      ensure => directory,
      owner  => 'www-data',
      mode   => 750,
    }
  }
  if ! defined(File["/srv/mod_pagespeed/files/${real_name}"]) {
    file { "/srv/mod_pagespeed/files/${real_name}":
      ensure => directory,
      owner  => 'www-data',
      mode   => 750,
    }
  }

  # These selections provide us with easy defaults. It's a lot of code, though.
  case $selection {
    'none': {
      $real_add_head                          = $add_head
      $real_combine_css                       = $combine_css
      $real_convert_meta_tags                 = $convert_meta_tags
      $real_extend_cache                      = $extend_cache
      $real_inline_css                        = $inline_css
      $real_inline_import_to_link             = $inline_import_to_link
      $real_inline_javascript                 = $inline_javascript
      $real_rewrite_css                       = $rewrite_css
      $real_rewrite_images                    = $rewrite_images
      $real_rewrite_javascript                = $rewrite_javascript
      $real_rewrite_style_attributes_with_url = $rewrite_style_attributes_with_url
      $real_trim_urls                         = $trim_urls
      $real_combine_heads                     = $combine_heads
      $real_strip_scripts                     = $strip_scripts
      $real_outline_css                       = $outline_css
      $real_outline_javascript                = $outline_javascript
      $real_move_css_above_scripts            = $move_css_above_scripts
      $real_move_css_to_head                  = $move_css_to_head
      $real_rewrite_style_attributes          = $rewrite_style_attributes
      $real_flatten_css_imports               = $flatten_css_imports
      $real_make_google_analytics_async       = $make_google_analytics_async
      $real_combine_javascript                = $combine_javascript
      $real_local_storage_cache               = $local_storage_cache
      $real_insert_ga                         = $insert_ga
      $real_convert_jpeg_to_progressive       = $convert_jpeg_to_progressive
      $real_convert_png_to_jpeg               = $convert_png_to_jpeg
      $real_convert_jpeg_to_webp              = $convert_jpeg_to_webp
      $real_insert_image_dimensions           = $insert_image_dimensions
      $real_inline_preview_images             = $inline_preview_images
      $real_resize_mobile_images              = $resize_mobile_images
      $real_remove_comments                   = $remove_comments
      $real_collapse_whitespace               = $collapse_whitespace
      $real_elide_attributes                  = $elide_attributes
      $real_sprite_images                     = $sprite_images
      $real_rewrite_domains                   = $rewrite_domains
      $real_remove_quotes                     = $remove_quotes
      $real_add_instrumentation               = $add_instrumentation
      $real_defer_javascript                  = $defer_javascript
      $real_inline_preview_images             = $inline_preview_images
      $real_lazyload_images                   = $lazyload_images
    }
    'safe': {
      $real_add_head                          = true
      $real_combine_css                       = true
      $real_convert_meta_tags                 = true
      $real_extend_cache                      = true
      $real_inline_css                        = true
      $real_inline_import_to_link             = true
      $real_inline_javascript                 = true
      $real_rewrite_css                       = true
      $real_rewrite_images                    = true
      $real_rewrite_javascript                = true
      $real_rewrite_style_attributes_with_url = true
      $real_trim_urls                         = true
      $real_combine_heads                     = false
      $real_strip_scripts                     = false
      $real_outline_css                       = false
      $real_outline_javascript                = false
      $real_move_css_above_scripts            = false
      $real_move_css_to_head                  = false
      $real_rewrite_style_attributes          = false
      $real_flatten_css_imports               = false
      $real_make_google_analytics_async       = false
      $real_combine_javascript                = false
      $real_local_storage_cache               = false
      $real_insert_ga                         = false
      $real_convert_jpeg_to_progressive       = false
      $real_convert_png_to_jpeg               = false
      $real_convert_jpeg_to_webp              = false
      $real_insert_image_dimensions           = false
      $real_inline_preview_images             = false
      $real_resize_mobile_images              = false
      $real_remove_comments                   = false
      $real_collapse_whitespace               = false
      $real_elide_attributes                  = false
      $real_sprite_images                     = false
      $real_rewrite_domains                   = false
      $real_remove_quotes                     = false
      $real_add_instrumentation               = false
      $real_defer_javascript                  = false
      $real_lazyload_images                   = false
    }
    'max': {
      $real_add_head                          = true
      $real_combine_css                       = true
      $real_convert_meta_tags                 = true
      $real_extend_cache                      = true
      $real_inline_css                        = true
      $real_inline_import_to_link             = true
      $real_inline_javascript                 = true
      $real_rewrite_css                       = true
      $real_rewrite_images                    = true
      $real_rewrite_javascript                = true
      $real_rewrite_style_attributes_with_url = false # rewrite_style_attributes takes precendence
      $real_trim_urls                         = true
      $real_combine_heads                     = true
      $real_strip_scripts                     = false
      $real_outline_css                       = true
      $real_outline_javascript                = true
      $real_move_css_above_scripts            = true
      $real_move_css_to_head                  = true
      $real_rewrite_style_attributes          = true
      $real_flatten_css_imports               = true
      $real_make_google_analytics_async       = true
      $real_combine_javascript                = true
      $real_local_storage_cache               = true
      $real_insert_ga                         = false
      $real_convert_jpeg_to_progressive       = true
      $real_convert_png_to_jpeg               = true # Decreases quality of some images!
      $real_convert_jpeg_to_webp              = true
      $real_insert_image_dimensions           = true # Might cause problems when using sprites or images resized by css
      $real_inline_preview_images             = true # Causes low quality images to be loaded first, replacing afterwards
      $real_resize_mobile_images              = true # Together with inline_preview_images only
      $real_remove_comments                   = true
      $real_collapse_whitespace               = true # Might break pages that use the css "white-space: pre"
      $real_elide_attributes                  = true # Might break advanced CSS stuff, breaks w3c compatibility
      $real_sprite_images                     = true
      $real_rewrite_domains                   = false
      $real_remove_quotes                     = true # Breaks w3c compatibility
      $real_add_instrumentation               = false
      $real_defer_javascript                  = true # Might break heavily js stuff
      $real_lazyload_images                   = true
    }
    'defaults': {
      $real_add_head                          = true
      $real_combine_css                       = true
      $real_convert_meta_tags                 = true
      $real_extend_cache                      = true
      $real_inline_css                        = true
      $real_inline_import_to_link             = true
      $real_inline_javascript                 = true
      $real_rewrite_css                       = true
      $real_rewrite_images                    = true
      $real_rewrite_javascript                = true
      $real_rewrite_style_attributes_with_url = false # rewrite_style_attributes takes precendence
      $real_trim_urls                         = true
      $real_combine_heads                     = true
      $real_strip_scripts                     = false
      $real_outline_css                       = true
      $real_outline_javascript                = true
      $real_move_css_above_scripts            = true
      $real_move_css_to_head                  = true
      $real_rewrite_style_attributes          = true
      $real_flatten_css_imports               = true
      $real_make_google_analytics_async       = true
      $real_combine_javascript                = true
      $real_local_storage_cache               = true
      $real_insert_ga                         = false
      $real_convert_jpeg_to_progressive       = true
      $real_convert_png_to_jpeg               = false
      $real_convert_jpeg_to_webp              = true
      $real_insert_image_dimensions           = false
      $real_inline_preview_images             = false
      $real_resize_mobile_images              = false
      $real_remove_comments                   = true
      $real_collapse_whitespace               = false
      $real_elide_attributes                  = false
      $real_sprite_images                     = true
      $real_rewrite_domains                   = false
      $real_remove_quotes                     = false
      $real_add_instrumentation               = false
      $real_defer_javascript                  = false
      $real_lazyload_images                   = true
    }
    default: { fail("Use a proper selections argument!") }
  }

  # This actually adds the configuration, based on a template. The restart of Apache might be over to top, a
  # reload might be enough, but has not been tested yet.
  kbp_apache::vhost_addition { "${name}/pagespeed":
    content => template('kbp_pagespeed/site-settings'),
    require => File["/srv/mod_pagespeed/cache/${real_name}","/srv/mod_pagespeed/files/${real_name}"],
    notify  => Service['apache2'],
    ports   => $ports;
  }
}
