#!/usr/bin/env bash
TOCOPY="ast_denoter.ml ast_quoter.ml denoter.ml plugin_core.ml plugin_core.mli reification.ml template_translation.ml quoter.ml run_extractable.ml run_extractable.mli tm_util.ml \
  caml_nat.mli caml_nat.ml caml_byte.ml caml_byte.mli caml_bytestring.ml"

# Test if gen-src is older than src
if [[ ! -f "gen-src/denoter.ml" ||
  "theories/Extraction.vo" -nt "gen-src/metarocq_template_plugin.cmx" || "$1" = "force" ]]
then
    echo "Updating gen-src from src"
    echo "Copying from src to gen-src"
    for x in ${TOCOPY}; do rm -f gen-src/$x; cp -a src/$x gen-src/$x; done
    echo "Renaming files to camelCase"
    (cd gen-src; ./to-lower.sh)
    rm -f gen-src/*.d gen-src/*.cm*
    echo "Prepare line endings for patching (for Windows)"
    for f in gen-src/*.ml*
    do
      tr -d '\r' < "$f" > tmp
      mv -f tmp $f
    done
    # Fix an extraction bug: wrong type annotation on eq_equivalence
    patch -N -p0 < extraction.patch
    patch -N -p0 < specFloat.patch
    exit 0
else
    echo "Extracted code is up-to-date"
fi
