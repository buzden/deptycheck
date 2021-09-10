export IDRIS2 ?= idris2

RUNTESTS := build/exec/runtests

MKDIR := mkdir -p
LN := ln

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

.PHONY: thirdparties thirdparty-elab-util thirdparty-sop

thirdparties: thirdparty-elab-util thirdparty-sop

thirdparty-elab-util:
	${IDRIS2} --build thirdparty/elab-util/elab-util.ipkg

thirdparty-sop: thirdparty-elab-util
	${RM} -r thirdparty/sop/depends/
	${MKDIR} thirdparty/sop/depends/
	${LN} -sf ../../elab-util/build/ttc/ thirdparty/sop/depends/elab-util-0.3.1
	${IDRIS2} --build thirdparty/sop/sop.ipkg
	${RM} -r thirdparty/sop/depends/
	# TODO to make the `depends` dir be removed even on the compiler crash

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
