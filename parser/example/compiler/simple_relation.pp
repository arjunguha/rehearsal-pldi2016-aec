file{'/tmp/dir': ensure=>directory} -> file{'/tmp/dir/file1': ensure=>file}
file{'/home/abc/file1':ensure=>file} <- user{'abc': ensure=>present}
file{'/etc/apache2/httpd.conf':ensure=>file} ~> service{'apache2':ensure=>running}
service{'nginx':ensure=>running} <~ file{'/etc/nginx/nginx.conf':ensure=>file}
