# puppet original parser throws a warning that 'file' is a type and should be captialized
file ['/tmp/file1'] {
  checksum => md5lite
}
