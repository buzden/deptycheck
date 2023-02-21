PACK ?= pack

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
	${PACK} build non-hermetic-tests.ipkg

test: runner
	${PACK} run non-hermetic-tests.ipkg "`pwd`/.pack_lock" $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only "$(only)"

retest: runner
	${PACK} run non-hermetic-tests.ipkg "`pwd`/.pack_lock" $(INTERACTIVE) --timing --failure-file failures --threads $(threads) --only-file failures --only "$(only)"

clean:
	${PACK} clean non-hermetic-tests.ipkg
	$(RM) failures
	@find . -depth -type d -name build -exec rm -rf '{}' \;
	@find . -type f -name 'output' -delete
	@find . -type f -name '*.ttc'  -delete
	@find . -type f -name '*.ttm'  -delete
	@find . -type f -name '*.ibc'  -delete
