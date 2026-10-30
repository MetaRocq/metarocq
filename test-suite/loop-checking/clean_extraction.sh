#!/usr/bin/env bash

# Lowercase the extracted modules, then remove those already linked in the
# template_rocq plugin, as in erasure-plugin/clean_extraction.sh

SED=`which gsed || which sed`

cd gen-src && ./to-lower.sh && cd ..

files=`cat ../../template-rocq/_PluginProject.in | grep "^[^#].*mli\?$"`
echo "Removing:" $files
rm -f $files
