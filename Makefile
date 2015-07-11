VNAME := -name \*.v ! -name \*.\#\*

ALL := $(shell find . $(VNAME))

.PHONY: default all

default: all

all: soundness

soundness: T=TypeSoundness
soundness: build

COQC    := $(COQBIN)coqc

build:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(T))) -o Makefile.coq
	@echo '-include $(addsuffix .d,$(shell find . -name \*.v ! -name \*.#\*))' >> Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	rm -f Makefile.coq .depend
	./rmr .v.d
	./rmr .vo
	./rmr .glob
