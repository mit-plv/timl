.PHONY: default lib soundness clean

default: lib

lib: Makefile.coq
	$(MAKE) -f Makefile.coq Frap.vo

soundness: Makefile.coq
	$(MAKE) -f Makefile.coq Soundness.vo

Makefile.coq: Makefile _CoqProject *.v
	coq_makefile -f _CoqProject -o Makefile.coq

clean:: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
