# Checks Demo.v against a built rocq-hylomorphisms (dune build), and writes
# the _RocqProject that VsRocq / rocq-lsp read. Override HYLO for another
# checkout, MEM for another memory cap.
HYLO  ?= $(HOME)/Work/Repos/Mechanisation/HYLO/arrays-as-hylos/deps/rocq-hylomorphisms/_build/default
MEM   ?= 3G
FLAGS  = -R $(HYLO)/theories Hylo -R $(HYLO)/examples Hylo.Examples \
         -R $(HYLO)/extraction-setup Hylo.Extraction

check: _RocqProject
	systemd-run --user --scope -p MemoryMax=$(MEM) -p MemorySwapMax=0 \
	  timeout 600 rocq compile $(FLAGS) Demo.v

_RocqProject: Makefile
	printf '%s\n' '-R $(HYLO)/theories Hylo' \
	  '-R $(HYLO)/examples Hylo.Examples' \
	  '-R $(HYLO)/extraction-setup Hylo.Extraction' > $@

clean:
	rm -f _RocqProject *.vo *.vok *.vos *.glob .*.aux .lia.cache .nia.cache
	rm -rf .coq-native

.PHONY: check clean
