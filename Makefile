VNAME := -name \*.v ! -name \*.\#\*

ALL := $(shell find . $(VNAME))

EXAMPLES := \
	examples/MergeSort \

.PHONY: default all examples

default: all

all: T=$(ALL)
all: build

examples: T=$(EXAMPLES)
examples: build

BEDROCK_ROOT := ~/bedrock
COQARGS := -I $(BEDROCK_ROOT)
COQC    := $(COQBIN)coqc $(COQARGS)

build:
	$(COQBIN)coq_makefile $(COQARGS) $(addsuffix .v,$(basename $(T))) -o Makefile.coq
	@echo '-include $(addsuffix .d,$(shell find . -name \*.v ! -name \*.#\*))' >> Makefile.coq
	$(MAKE) -f Makefile.coq

clean:
	rm -f Makefile.coq .depend
	./rmr .v.d
	./rmr .vo
	./rmr .glob

