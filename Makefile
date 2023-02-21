export IDRIS2 ?= idris2
export PACK ?= pack

MKDIR := mkdir -p
LN := ln

.PHONY: all deptycheck clean

all: deptycheck

deptycheck:
	${PACK} build deptycheck.ipkg

clean:
	${IDRIS2} --clean deptycheck.ipkg
	${RM} -r build
	@
	${MAKE} -C docs clean
	@
	${MAKE} -C tests -f tests.mk clean
	${MAKE} -C example -f pil.mk clean

.PHONY: test test-all test-deptycheck

test: test-all

test-all: test-deptycheck print-v-delimiter test-pil

test-deptycheck: deptycheck
	${PACK} install test
	${MAKE} -C tests -f tests.mk only="${only}"

.PHONY: retest-deptycheck

retest-deptycheck: deptycheck
	${MAKE} -C tests -f tests.mk retest

.PHONY: test-installation

test-installation:
	${PACK} install contrib test
	${MAKE} -C tests/installation -f non-hermetic-tests.mk only="${only}"

.PHONY: pil test-pil

pil: deptycheck
	${MAKE} -C example -f pil.mk

test-pil: pil
	${PACK} install contrib test
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
