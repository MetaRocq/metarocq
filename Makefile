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
	  -R theories/Utils MetaRocq.Utils \
	  -R theories/Common MetaRocq.Common \
	  -R theories/Template MetaRocq.Template \
	  -R theories/TemplatePCUIC MetaRocq.TemplatePCUIC \
	  -R theories/PCUIC MetaRocq.PCUIC \
	  -R theories/SafeChecker MetaRocq.SafeChecker \
	  -R theories/SafeCheckerPlugin MetaRocq.SafeCheckerPlugin \
	  -R theories/Erasure MetaRocq.Erasure \
	  -R theories/ErasurePlugin MetaRocq.ErasurePlugin \
	  -R theories/Quotation MetaRocq.Quotation \
	  -R theories/Translations MetaRocq.Translations \
	  -R examples MetaRocq.Examples \
	  -d $(CURDIR)/html theories/*/*.v theories/*/*/*.v examples/*.v
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
