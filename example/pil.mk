export PACK ?= pack

.PHONY: all test clean pil

all: pil

pil:
	${PACK} build pil.ipkg

test: pil
	${MAKE} -C tests -f tests.mk only="${only}"

clean:
	${PACK} clean pil.ipkg
	${RM} -r build
	@
	${MAKE} -C tests -f tests.mk clean
