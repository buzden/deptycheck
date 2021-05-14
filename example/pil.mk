export IDRIS2 ?= idris2

RUNTESTS := build/exec/runtests

.PHONY: all test clean pil

all: pil

pil:
	${IDRIS2} --build pil.ipkg

test: pil
	${MAKE} -C tests -f tests.mk only=${only}

clean:
	${IDRIS2} --clean pil.ipkg
	${RM} -r build
	@
	${MAKE} -C tests -f tests.mk clean
