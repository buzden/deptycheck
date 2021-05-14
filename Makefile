export IDRIS2 ?= idris2

RUNTESTS := build/exec/runtests

.PHONY: all test deptycheck clean

all: deptycheck

deptycheck:
	${IDRIS2} --build deptycheck.ipkg

test: deptycheck
	${MAKE} -C tests -f tests.mk only=${only}

clean:
	${IDRIS2} --clean deptycheck.ipkg
	${RM} -r build
	@
	${MAKE} -C tests -f tests.mk clean
	${MAKE} -C example -f pil.mk clean

.PHONY: pil test-pil clean

pil: deptycheck
	${MAKE} -C example -f pil.mk

test-pil: pil
	${MAKE} -C example -f pil.mk test only=${only}
