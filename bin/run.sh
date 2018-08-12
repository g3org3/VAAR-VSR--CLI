#!/usr/bin/env bash
set -e
# TODO: check if path is absolute or not
FILE=$1
CUSTOM=$2
OUTPUT="output"
CONFIG="config"
IMAGE=registry.jorgeadolfo.com/epav:latest
# clear;

if [ -z "$FILE" ]; then
  echo "Please provide the file path as an argument."
elif [ -f $FILE ]; then
  echo "> Tosca conf detected"
  if [ -n "$CUSTOM" ]; then
    if [ -f $CUSTOM ]; then
      echo "> Custom rules detected"
      echo "> running tool..."
      echo ""
      docker run -v `pwd`/$CONFIG:/cli/config -v `pwd`/$OUTPUT:/cli/output -v `pwd`/$FILE:/cli/tosca-conf.yml -v `pwd`/$CUSTOM:/cli/user.smt $IMAGE
    fi
  else
    echo "> running tool..."
    echo ""
    docker run -v `pwd`/$CONFIG:/cli/config -v `pwd`/$OUTPUT:/cli/output -v `pwd`/$FILE:/cli/tosca-conf.yml $IMAGE
  fi
else
  echo "File $FILE does not exist."
fi
