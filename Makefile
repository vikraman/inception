AGDA_SRCS = $(shell find -H Inception -type f \( -name '*.agda' -o -name '*.lagda' \) ! -path $(EVERYTHING))
EVERYTHING = Inception/Everything.agda

STUB = echo 'module Inception.Everything where' > $(EVERYTHING)

all: everything
	trap "$(STUB)" EXIT; agda index.agda

everything:
	{ echo 'module Inception.Everything where'; echo; \
	  for f in $(sort $(AGDA_SRCS)); do echo "$$f"; done \
	  | sed -E 's/\.l?agda$$//; s#/#.#g; s/^/import /'; } > $(EVERYTHING)

html: everything
	trap "$(STUB)" EXIT; agda --html --highlight-occurrences --css=Agda.css index.agda

todos:
	grep -E -n --colour=auto 'TODO' $(AGDA_SRCS)

LINT = scripts/AgdaLint.hs

lint:
	$(LINT)

lint-fix:
	$(LINT) --fix

cloc:
	cloc Inception/

clean:
	rm -rf _build

.PHONY: all everything html todos lint lint-fix cloc clean
