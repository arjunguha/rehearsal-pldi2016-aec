file1.pp: Two resource that should have been explicitly related but are not. The resources in the manifest are applied as desired due to puppet's quirk in ordering unrelated resources

file2.pp: Includes resources from file1 and creates an explicit dependency between its own resource and a resource in file1, changing the implicit order of resources in file1.pp and triggering a bug
