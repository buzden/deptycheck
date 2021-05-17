export IDRIS2 ?= idris2

RUNTESTS := build/exec/runtests

.PHONY: all deptycheck clean

all: deptycheck

deptycheck: thirdparty-elab-util
	${IDRIS2} --build deptycheck.ipkg

clean:
	${IDRIS2} --clean deptycheck.ipkg
	${RM} -r build
	@
	${MAKE} -C tests -f tests.mk clean
	${MAKE} -C example -f pil.mk clean
	@
	${IDRIS2} --clean thirdparty/elab-util/elab-util.ipkg
	${RM} -r thirdparty/elab-util/build

.PHONY: test test-all test-deptycheck

test: test-all

test-all: test-deptycheck print-v-delimiter test-pil

test-deptycheck: deptycheck
	${MAKE} -C tests -f tests.mk only=${only}

.PHONY: thirdparty-elab-util

thirdparty-elab-util:
	${IDRIS2} --build thirdparty/elab-util/elab-util.ipkg

.PHONY: pil test-pil

pil: deptycheck
	${MAKE} -C example -f pil.mk

test-pil: pil
	${MAKE} -C example -f pil.mk test only=${only}

.PHONY: print-v-delimiter

print-v-delimiter:
	@echo
	@echo
	@echo "========================================================================"
	@echo
	@echo
