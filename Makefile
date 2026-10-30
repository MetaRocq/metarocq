# MetaRocq is built with dune (see dune-project); these targets are shortcuts.

.PHONY: all test test-suite examples install uninstall html clean checktodos \
	ci-local ci-opam

all:
	dune build

# The test-suite and the examples
test:
	dune test

test-suite:
	dune build @test-suite/runtest

examples:
	dune build @examples/runtest

install:
	dune install

uninstall:
	dune uninstall

# rocq doc needs the .glob files, which dune puts next to the copies of the
# sources in _build/default.
html: all examples
	cd _build/default && rocq doc --multi-index -toc -utf8 -html \
	  --with-header $(CURDIR)/html/resources/header.html \
	  --with-footer $(CURDIR)/html/resources/footer.html \
	  --coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
	  --external https://rocq-prover.org/doc/V9.0.0/stdlib Stdlib \
	  -R utils/theories MetaRocq.Utils \
	  -R common/theories MetaRocq.Common \
	  -R template-rocq/theories MetaRocq.Template \
	  -R template-pcuic MetaRocq.TemplatePCUIC \
	  -R pcuic MetaRocq.PCUIC \
	  -R safechecker MetaRocq.SafeChecker \
	  -R safechecker-plugin/theories MetaRocq.SafeCheckerPlugin \
	  -R erasure MetaRocq.Erasure \
	  -R erasure-plugin/theories MetaRocq.ErasurePlugin \
	  -R quotation/theories MetaRocq.Quotation \
	  -R translations MetaRocq.Translations \
	  -R examples MetaRocq.Examples \
	  -d $(CURDIR)/html */theories/*.v */theories/*/*.v \
	  pcuic/*.v pcuic/*/*.v safechecker/*.v template-pcuic/*.v template-pcuic/*/*.v \
	  erasure/*.v erasure/*/*.v translations/*.v examples/*.v
	# Overwritten by rocq doc
	git checkout html/coqdoc.css

clean:
	dune clean

checktodos:
	sh checktodos.sh

ci-local:
	dune build @default @runtest

ci-opam:
# Use -v so that regular output is produced
	opam install --with-test -v -y .
	opam remove -y rocq-metarocq rocq-metarocq-template
