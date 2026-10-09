# graphics in keep-directory (would be removed by distclean otherwise)
GRAPHICS = cc-by.pdf lipics-logo-bw.pdf orcid.pdf
# all sources needed to build the paper
SOURCES = $(wildcard *.tex *.cls *.sty *.bib) $(GRAPHICS)
# sources for the arxiv version
ARXIV_SOURCES = $(filter-out $(wildcard *lics*),$(wildcard *.tex *.cls *.sty *.bib *.bbl) cc-by.pdf lipics-logo-bw.pdf)
# sources for the camera-ready version
TYPESPP_SOURCES = lics27-inc.tex $(filter-out $(wildcard *arxiv*)$(wildcard *lics*),$(wildcard *.tex *.cls *.sty *.bib *.bbl))
# targets to build: full paper, and the stripped submission
TARGETS = lics27-inc.pdf arxiv-inc.pdf
# latexmk setup
DEPS_DIR = .deps
ENGINE = -pdf
LATEXMK = latexmk -recorder -use-make $(ENGINE)

all: $(TARGETS)

$(GRAPHICS): %.pdf:
	cp keep/$@ $@

lics27-inc.pdf: $(SOURCES)
	$(LATEXMK) lics27-inc.tex

arxiv-inc.pdf: $(SOURCES)
	$(LATEXMK) arxiv-inc.tex

cont: continuous
continuous: LATEXMK += -f -interaction=nonstopmode -pvc
continuous: $(SOURCES)
	$(LATEXMK) arxiv-inc.tex

arxiv.tar.gz:
	tar achvf arxiv.tar.gz $(ARXIV_SOURCES)

lics27-inc.zip: $(SOURCES)
	zip lics27-inc.zip $(TYPESPP_SOURCES)

clean:
	latexmk -c

distclean: clean
	latexmk -C
	rm -rf *.axp *.xcp *.bbl *.blg *.aux *.xml *.cut *.pdf

cache-clean:
	rm -rf `biber --cache`

.PHONY: clean distclean cache-clean cont continuous
