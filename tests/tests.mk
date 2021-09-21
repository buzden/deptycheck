# Mostly copied from the Idris2's makefile in the `test` dir

IDRIS2 ?= idris2

INTERACTIVE ?= --interactive
ifeq ($(shell uname), FreeBSD)
	NPROC = sysctl -n hw.ncpu
else
	NPROC = nproc
endif
threads ?= `$(NPROC)`

.PHONY: all runner test retest clean

all: test

runner:
	${IDRIS2} --build tests.ipkg

test: runner
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --failure-file failures --threads $(threads) --only "$(only)"

retest: runner
	./build/exec/runtests $(IDRIS2) $(INTERACTIVE) --failure-file failures --threads $(threads) --only-file failures --only "$(only)"

clean:
	${IDRIS2} --clean tests.ipkg
	$(RM) failures
	$(RM) -r build
	$(RM) -r **/**/build
	@find . -type f -name 'output' -exec rm -rf '{}' \;
	@find . -type f -name '*.ttc' -exec rm -f '{}' \;
	@find . -type f -name '*.ttm' -exec rm -f '{}' \;
	@find . -type f -name '*.ibc' -exec rm -f '{}' \;
