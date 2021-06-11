#!/bin/bash

do_replace () {
# only if the replacement doesn't exist
if ! grep -r -w $2_corres .;
  then
  # search and replace
  find . -type f -exec sed -i "s/\b$1\b/$2/g" {} +
  # commit the change
  #git commit -am "rename $1 to $2_corres"
else
  echo "Replacement string already exists"
fi
}


echo "READING: " $1

cat $1 | while read line
do
	if [[ $line =~ (rename )([^ ]*)( to )([^ ]*) ]]
	then
	old=${BASH_REMATCH[2]}
	new=${BASH_REMATCH[4]}
	do_replace $old $new
	echo "SUCCESS: $line"
	else
	echo "FAIL: $line"
	echo "MATCH NOT FOUND"
	fi
done

echo "DONE"


