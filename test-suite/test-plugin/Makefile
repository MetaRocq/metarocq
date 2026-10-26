all: plugin

Makefile.plugin: _PluginProject
	rocq makefile -f _PluginProject -o Makefile.plugin

_PluginProject: _PluginProject.in metarocq-config
	cat metarocq-config > _PluginProject
	cat _PluginProject.in >> _PluginProject

plugin: Makefile.plugin
	$(MAKE) -f Makefile.plugin

.PHONY: all plugin clean mrproper

clean: Makefile.plugin
	$(MAKE) -f Makefile.plugin clean

mrproper:
	rm -f Makefile.plugin _PluginProject

.merlin: Makefile.plugin
	$(MAKE) -f Makefile.plugin .merlin
