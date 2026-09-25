#!/usr/bin/env bash

set -eu
set -o pipefail

./lagda_to_agda.sh $( find -H Inception -type f -name '*.lagda')
find -H Inception -type f -name '*.lagda' -exec rm {} \;

for file in $( find -H Inception -type f -name '*.agda' | sort ); do
    i=$( echo ${file} | sed 's/Inception\/\(.*\)\.l\?agda/Inception\/\1/' | sed 's/\//\./g' )
    echo "import ${i}" >> index.agda
done
