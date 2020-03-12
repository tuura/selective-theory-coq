COQFLAGS = ""

VFILES = $(wildcard src/*.v)
VOFILES = $(patsubst %.v,%.vo,$(VFILES))

SRCS := $(shell egrep "^.*\.v$$" _CoqProject)

all: $(VOFILES)

%.vo: %.v Makefile.coq
	$(MAKE) -f Makefile.coq OPT=$(COQFLAGS)

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o $@

emacstags:
	-@coqtags $(SRCS)

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
