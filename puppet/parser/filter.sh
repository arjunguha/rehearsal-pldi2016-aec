#! /bin/bash

TARGET=/tmp/github/
TXT_TARGET=/tmp/github_text_pp/
PARSABLE_TXT_TARGET=/tmp/github_good_pp/


# Plain copy
# wget -o wget.log -t 5 -c -x -P $TARGET -i github_pp.txt

# Could contain non-text files, filter them out
find $TARGET -exec file {} \; | grep text | cut -d: -f1 | while read f 
do
  cp --parent ${f} $TXT_TARGET
  rm ${f}
done

# Separate good ones from bad ones
find $TXT_TARGET -exec puppet parser validate '{}' 2>/dev/null \; -print | while read f 
do 
  cp --parent ${f} $PARSABLE_TXT_TARGET
  rm ${f}
done
