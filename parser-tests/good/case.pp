case "foo" {
  "bar": { file{"/foo": } }
  "baz": { file{"/foo": } }
}

case "foo" {
  "bar": { file{"/fooz": } }
  default: { file{"/fooz": } }
}
