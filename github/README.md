A program to find Puppet code on Github. It prints the URL for each file found
to stdout. It optionally takes an OAuth token as a command-line argument. This
makes it run faster. If you run it, you'll that it prints several URLs, pauses
for a minute, and then repeats. This is normal: the GitHub API has a rate-limit.