#!/bin/bash

# The translations are examples, not checked for todos and admits
in_theories() {
    grep theories | grep -v "^theories/Translations/"
}

if [[ $(git grep -c todo | in_theories) = theories/Utils/MRUtils.v:3 ]]
then
    echo "No todos found"
    if [[ $(git grep -c Admitted | in_theories) = "" ]]
    then
        echo "No Admitted results found"
        exit 0
    else
        echo "Found Admitted results:"
        git grep -c Admitted | in_theories
        exit 1
    fi
else
    echo "Found todos:"
    git grep -c todo | in_theories | grep -v "theories/Utils/MRUtils.v:3"
    exit 1
fi
