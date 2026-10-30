#!/bin/bash

if [[ $(git grep -c todo | grep theories) = theories/Utils/MRUtils.v:3 ]]
then
    echo "No todos found"
    if [[ $(git grep -c Admitted | grep theories) = "" ]]
    then
        echo "No Admitted results found"
        exit 0
    else
        echo "Found Admitted results:"
        git grep -c Admitted | grep theories
        exit 1
    fi
else
    echo "Found todos:"
    git grep -c todo | grep theories | grep -v "theories/Utils/MRUtils.v:3"
    exit 1
fi
endef

