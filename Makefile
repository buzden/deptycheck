.PHONY: docs

docs:
	alias sh=bash
	${MAKE} -C docs dirhtml SPHINXOPTS="--color -W --keep-going"
