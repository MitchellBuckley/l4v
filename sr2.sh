#!/bin/bash

do_replace () {
# only if the replacement doesn't exist
if ! grep -r -w $2_corres .;
  then
  # search and replace
  find . -type f -exec sed -i "s/\b$1\b/$2_corres/g" {} +
  # commit the change
  #git commit -am "rename $1 to $2_corres"
else
  echo "Replacement string already exists"
fi
}



echo "read file >" $1

msg="Make the following replacements:"
cat $1 | while read line
do
	if [[ $line =~ (rename )([^ ]*)( to )([^ ]*) ]]
	then
	old=${BASH_REMATCH[2]}
	new=${BASH_REMATCH[4]}
	do_replace $old $new
	else
	echo "no match found: $line"
	fi
done

git commit -am "$msg"
echo "DONE"


