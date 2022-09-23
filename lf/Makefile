MAKE         := make
COQ_MAKEFILE := coq_makefile
COQ_FLAGS    := -Q . LF


all: lib

coq.mk:
	$(COQ_MAKEFILE) $(COQ_FLAGS) -o $@ *.v


.PHONY: lib
lib: coq.mk
	$(MAKE) -f coq.mk


.PHONY: clean
clean:
	rm -rf *.vos *.vok *.vo *.glob \
	       .*.aux .*.mk.d coq.mk coq.mk.conf
