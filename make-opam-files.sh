#/usr/bin/env bash

if (($# < 4))
then
    echo "Usage: make-opam-files.sh ../opam/released/packages <version> <tag> <package-url>"
    exit 0
fi

archive=`basename $4`
tag=$3

echo "Target directory: " $1
echo "Target version: " $2
echo "Releases package: " $4
echo "Archive:" $archive
echo "Tag:" $tag

if [ -f $archive ]
then
    echo "Removing existing archive!"
    rm $archive
fi

wget $4

hash=`shasum -a 512 $archive | cut -f 1 -d " "`

echo "Shasum = " $hash

# echo "Uploading to release assets"
# gh release upload $tag $archive
# release=https://github.com/MetaRocq/metarocq/releases/download/$tag/$archive
release=$4
skipline=""

for f in *.opam;
do
    opamf=${f/.opam/};
    target=$1/$opamf/$opamf.$2/opam;
    echo $opamf;
    mkdir -p $1/$opamf/$opamf.$2
    skipline="$skipline $opamf.$2"
    gsed -e "/^version:.*/d" $f > $target
    echo url { >> $target
    echo "  src:" \"$release\" >> $target
    echo "  checksum:" \"sha512=$hash\" >> $target
    echo } >> $target
done

echo "ci-skip:" $skipline
