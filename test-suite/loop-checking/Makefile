all: rocq plugin

rocq: Makefile.rocq
	$(MAKE) -f Makefile.rocq
	cd gen-src && ./to-lower.sh

Makefile.rocq: _RocqProject
	rocq makefile -f _RocqProject -o Makefile.rocq

Makefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o Makefile.plugin

plugin: Makefile.plugin rocq
	$(MAKE) -f Makefile.plugin

.PHONY: plugin

clean: Makefile.rocq Makefile.plugin
	$(MAKE) -f Makefile.rocq clean
	$(MAKE) -f Makefile.plugin clean

.merlin:
	make -f Makefile.plugin .merlin

cleanplugin: Makefile.plugin
	make -f Makefile.plugin clean
