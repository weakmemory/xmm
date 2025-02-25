COQMODULE    := xmm
COQTHEORIES  := src/reordering/*.v src/xmm/*.v src/lib/*.v src/traces/*.v src/xmm_cons/*.v src/sequentialization/*.v 

.PHONY: all theories clean tounicode

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

vio: Makefile.coq
	$(MAKE) -f Makefile.coq vio

checkproofs: Makefile.coq
	$(MAKE) -f Makefile.coq checkproofs

quick-check: Makefile.coq
	$(MAKE) -f Makefile.coq vio2vo J=8

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
	echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq

tounicode:
	sed -i 's/<</⟪/g' $(COQTHEORIES)
	sed -i 's/>>/⟫/g' $(COQTHEORIES)
	sed -i 's/;;/⨾/g' $(COQTHEORIES)
	sed -i 's/<|/⦗/g' $(COQTHEORIES)
	sed -i 's/|>/⦘/g' $(COQTHEORIES)
	sed -i 's/\^+/⁺/g' $(COQTHEORIES)
	sed -i 's/\^\*/＊/g' $(COQTHEORIES)
