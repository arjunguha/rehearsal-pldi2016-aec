import "file1.pp"

notify {'Setting up file1':
  before => File['/tmp/file1']
}
