if "" {
  notify{"r1": message => "empty string is truthy"}
}
else {
  fail("empty string is falsy")
}

if "non-empty" {
  notify{"r2": message => "non-empty string is truthy"}
}
else {
  fail("non-empty string is falsy")
}