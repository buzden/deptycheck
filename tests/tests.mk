# Mostly copied from the Idris2's makefile in the `test` dir

IDRIS2 ?= idris2

RUNTESTS := build/exec/runtests

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
	$(RUNTESTS) $(IDRIS2) $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only "$(only)"

retest: runner
	$(RUNTESTS) $(IDRIS2) $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures --only "$(only)"

clean:
	${IDRIS2} --clean tests.ipkg
	$(RM) failures
	@find . -depth -type d -name build -exec rm -rf '{}' \;
	@find . -type f -name 'output' -delete
	@find . -type f -name '*.ttc'  -delete
	@find . -type f -name '*.ttm'  -delete
	@find . -type f -name '*.ibc'  -delete
