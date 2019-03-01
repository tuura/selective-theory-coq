COQFLAGS = ""

VFILES = $(wildcard src/*.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

all: $(VOFILES)

%.vo: %.v Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean