all: coq plugin

coq: Makefile.coq
	$(MAKE) -f Makefile.coq
	cd gen-src && ./to-lower.sh

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

Makefile.plugin: _PluginProject
	coq_makefile -f _PluginProject -o Makefile.plugin

plugin: Makefile.plugin coq
	$(MAKE) -f Makefile.plugin

.PHONY: plugin

clean: Makefile.coq Makefile.plugin
	$(MAKE) -f Makefile.coq clean
	$(MAKE) -f Makefile.plugin clean

.merlin:
	make -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
