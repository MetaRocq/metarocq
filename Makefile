
all: printconf template-rocq pcuic safechecker erasure erasure-plugin safechecker-plugin

-include Makefile.conf

ifeq '$(METAROCQ_CONFIG)' 'local'
  ifeq ($(shell which cygpath 2>/dev/null),)
  OCAMLPATH := $(shell pwd)/template-rocq/:$(shell pwd)/safechecker-plugin/src:$(shell pwd)/erasure-plugin/src:$(OCAMLPATH)
  else
  OCAMLPATH := $(shell cygpath -m `pwd`)/template-rocq/;$(OCAMLPATH)
  endif
  export OCAMLPATH
endif

.PHONY: printconf all utils template-rocq pcuic erasure install uninstall html clean mrproper safechecker-plugin .merlin test-suite translations quotation

printconf:
ifeq '$(METAROCQ_CONFIG)' 'local'
	@echo "Local configuration"
else
ifeq '$(METAROCQ_CONFIG)' 'global'
	@echo "Global configuration"
else
	@echo "Run ./configure.sh first"
	@exit 1
endif
endif

install: all
	$(MAKE) -C utils install
	$(MAKE) -C common install
	$(MAKE) -C template-rocq install
	$(MAKE) -C pcuic install
	$(MAKE) -C safechecker install
	$(MAKE) -C template-pcuic install
# 	$(MAKE) -C quotation install
	$(MAKE) -C safechecker-plugin install
	$(MAKE) -C erasure install
	$(MAKE) -C erasure-plugin install

uninstall:
	$(MAKE) -C utils uninstall
	$(MAKE) -C common uninstall
	$(MAKE) -C template-rocq uninstall
	$(MAKE) -C pcuic uninstall
	$(MAKE) -C safechecker uninstall
	$(MAKE) -C template-pcuic uninstall
# 	$(MAKE) -C quotation uninstall
	$(MAKE) -C safechecker-plugin uninstall
	$(MAKE) -C erasure uninstall
	$(MAKE) -C erasure-plugin uninstall
	$(MAKE) -C translations uninstall

html: all
	"rocq doc" --multi-index -toc -utf8 -html \
    --with-header ./html/resources/header.html --with-footer ./html/resources/footer.html \
    --coqlib_url https://rocq-prover.org/doc/V9.0.0/corelib \
    --external https://rocq-prover.org/doc/V9.0.0/stdlib Stdlib \
		-R utils/theories MetaRocq.Utils \
		-R common/theories MetaRocq.Common \
		-R template-rocq/theories MetaRocq.Template \
		-R template-pcuic/theories MetaRocq.TemplatePCUIC \
		-R pcuic/theories MetaRocq.PCUIC \
		-R safechecker/theories MetaRocq.SafeChecker \
		-R safechecker-plugin/theories MetaRocq.SafeCheckerPlugin \
		-R erasure/theories MetaRocq.Erasure \
		-R erasure-plugin/theories MetaRocq.ErasurePlugin \
		-R translations MetaRocq.Translations \
		-R examples MetaRocq.Examples \
		-d html */theories/*.v */theories/*/*.v translations/*.v examples/*.v
	# Overwritten by rocq doc
	git co html/coqdoc.css

clean:
	$(MAKE) -C utils clean
	$(MAKE) -C common clean
	$(MAKE) -C template-rocq clean
	$(MAKE) -C pcuic clean
	$(MAKE) -C safechecker clean
	$(MAKE) -C safechecker-plugin clean
	$(MAKE) -C template-pcuic clean
# 	$(MAKE) -C quotation clean
	$(MAKE) -C erasure clean
	$(MAKE) -C erasure-plugin clean
	$(MAKE) -C examples clean
	$(MAKE) -C test-suite clean
	$(MAKE) -C translations clean

vos:
	$(MAKE) -C utils
	$(MAKE) -C common
	$(MAKE) -C template-rocq
	$(MAKE) -C pcuic vos
	$(MAKE) -C safechecker vos
	$(MAKE) -C safechecker-plugin vos
	$(MAKE) -C template-pcuic vos
# 	$(MAKE) -C quotation vos
	$(MAKE) -C erasure vos
	$(MAKE) -C erasure-plugin vos
	$(MAKE) -C translations vos

quick:
	$(MAKE) -C utils
	$(MAKE) -C common
	$(MAKE) -C template-rocq
	$(MAKE) -C pcuic quick
	$(MAKE) -C safechecker quick
	$(MAKE) -C safechecker-plugin quick
	$(MAKE) -C template-pcuic quick
# 	$(MAKE) -C quotation vos # quick # we cannot unset universe checking in 8.16 due to COQBUG(https://github.com/coq/coq/issues/17361), and quick does not buy much in quotation anyway, where almost everything is transparent
	$(MAKE) -C erasure quick
	$(MAKE) -C erasure-plugin quick
	$(MAKE) -C translations quick

mrproper:
	$(MAKE) -C utils mrproper
	$(MAKE) -C common mrproper
	$(MAKE) -C template-rocq mrproper
	$(MAKE) -C pcuic mrproper
	$(MAKE) -C safechecker mrproper
	$(MAKE) -C safechecker-plugin mrproper
	$(MAKE) -C template-pcuic mrproper
# 	$(MAKE) -C quotation mrproper
	$(MAKE) -C erasure mrproper
	$(MAKE) -C erasure-plugin mrproper
	$(MAKE) -C examples mrproper
	$(MAKE) -C test-suite mrproper
	$(MAKE) -C translations mrproper

.merlin:
	$(MAKE) -C utils .merlin
	$(MAKE) -C common .merlin
	$(MAKE) -C template-rocq .merlin
	$(MAKE) -C pcuic .merlin
	$(MAKE) -C safechecker .merlin
	$(MAKE) -C safechecker-plugin .merlin
	$(MAKE) -C template-pcuic .merlin
# 	$(MAKE) -C quotation .merlin
	$(MAKE) -C erasure .merlin
	$(MAKE) -C erasure-plugin .merlin

utils:
	$(MAKE) -C utils

common: utils
	$(MAKE) -C common

template-rocq: common
	$(MAKE) -C template-rocq

pcuic: common
	$(MAKE) -C pcuic

safechecker: pcuic
	$(MAKE) -C safechecker

template-pcuic: template-rocq pcuic
	$(MAKE) -C template-pcuic

# quotation: template-rocq pcuic template-pcuic
# 	$(MAKE) -C quotation

safechecker-plugin: safechecker template-pcuic
	$(MAKE) -C safechecker-plugin

erasure: safechecker template-pcuic
	$(MAKE) -C erasure

erasure-plugin: erasure template-pcuic
	$(MAKE) -C erasure-plugin

install-plugins: erasure-plugin safechecker-plugin
	$(MAKE) -C utils install
	$(MAKE) -C common install
	$(MAKE) -C template-rocq install
	$(MAKE) -C pcuic install
	$(MAKE) -C template-pcuic install
	$(MAKE) -C erasure install
	$(MAKE) -C safechecker-plugin install
	$(MAKE) -C erasure-plugin install

examples: safechecker-plugin erasure-plugin
	$(MAKE) -C examples

test-suite: safechecker-plugin erasure-plugin
	$(MAKE) -C test-suite

translations: template-rocq
	$(MAKE) -C translations

cleanplugins:
	$(MAKE) -C template-rocq cleanplugin
	$(MAKE) -C safechecker-plugin cleanplugin
	$(MAKE) -C erasure cleanplugin

ci-local-noclean:
	./configure.sh local
	$(MAKE) all translations test-suite TIMED=pretty-timed

ci-local: ci-local-noclean
	$(MAKE) clean

ci-quick:
	./configure.sh --enable-quick
	time $(MAKE) quick TIMED=pretty-timed

ci-opam:
# Use -v so that regular output is produced
	opam pin add -y .
	opam install --with-test -v -y rocq-metarocq
	opam remove -y rocq-metarocq rocq-metarocq-template

checktodos:
	sh checktodos.sh
