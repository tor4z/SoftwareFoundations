COQ_MAKEFILE  := coq_makefile
COQ_FLAGS     := -Q . PLF
MAKE          := make
COQ_MK        := coq.mk


all: lib


$(COQ_MK):
	$(COQ_MAKEFILE) $(COQ_FLAGS) -o $@ *.v


.PHONY: lib
lib: $(COQ_MK)
	$(MAKE) -f $^

.PHONY: clean
clean:
	rm -rf *.vos *.vok *.vo *.glob \
	       .*.aux .*.mk.d coq.mk coq.mk.conf
