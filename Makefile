export IDRIS2 ?= idris2
export PACK ?= pack

MKDIR := mkdir -p
LN := ln

.PHONY: all deptycheck clean

all: deptycheck

deptycheck: thirdparty-elab-util
	${PACK} install-deps deptycheck.ipkg
	${IDRIS2} --build deptycheck.ipkg

clean:
	${IDRIS2} --clean deptycheck.ipkg
	${RM} -r build
	@
	${MAKE} -C docs clean
	@
	${MAKE} -C tests -f tests.mk clean
	${MAKE} -C example -f pil.mk clean
	@
	for pkg in thirdparty/*/*.ipkg; do ${IDRIS2} --clean "$${pkg}"; done
	${RM} -r thirdparty/*/build

.PHONY: install install-all install-deptycheck install-dependencies

install: install-all

install-all: install-dependencies install-deptycheck

install-deptycheck: deptycheck
	${IDRIS2} --install deptycheck.ipkg

install-dependencies: thirdparty-elab-util
	${MAKE} -C thirdparty/elab-util install

.PHONY: test test-all test-deptycheck

test: test-all

test-all: test-deptycheck print-v-delimiter test-pil

test-deptycheck: deptycheck thirdparty-sop thirdparty-summary-stat
	${MAKE} -C tests -f tests.mk only="${only}"

.PHONY: retest-deptycheck

retest-deptycheck: deptycheck thirdparty-sop
	${MAKE} -C tests -f tests.mk retest

.PHONY: test-installation

test-installation:
	${MAKE} -C tests/installation -f non-hermetic-tests.mk only="${only}"

.PHONY: thirdparties thirdparty-elab-util thirdparty-sop

thirdparties: thirdparty-elab-util thirdparty-sop thirdparty-summary-stat

thirdparty-elab-util:
	${IDRIS2} --build thirdparty/elab-util/elab-util.ipkg

thirdparty-sop: thirdparty-elab-util
	${RM} -r thirdparty/sop/depends/
	${MKDIR} thirdparty/sop/depends/
	${LN} -sf ../../elab-util/build/ttc/ thirdparty/sop/depends/elab-util-0.6.0
	${IDRIS2} --build thirdparty/sop/sop.ipkg
	${RM} -r thirdparty/sop/depends/
	# TODO to make the `depends` dir be removed even on the compiler crash

thirdparty-summary-stat:
	${IDRIS2} --build thirdparty/summary-stat/summary-stat.ipkg

.PHONY: pil test-pil

pil: deptycheck
	${MAKE} -C example -f pil.mk

test-pil: pil
	${MAKE} -C example -f pil.mk test only="${only}"

.PHONY: docs

docs:
	alias sh=bash
	${MAKE} -C docs dirhtml SPHINXOPTS="--color -W --keep-going"

.PHONY: print-v-delimiter

print-v-delimiter:
	@echo
	@echo
	@echo "========================================================================"
	@echo
	@echo
