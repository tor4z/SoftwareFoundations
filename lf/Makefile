MAKE         := make
COQ_MAKEFILE := coq_makefile


all: lib

coq.mk: _CoqProject
	$(COQ_MAKEFILE) -f $< -o $@ *.v


.PHONY: lib
lib: coq.mk
	$(MAKE) -f coq.mk


.PHONY: clean
clean:
	rm -rf *.vos *.vok *.vo *.glob \
	       .*.aux .*.mk.d coq.mk coq.mk.conf
