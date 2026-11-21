# Rules shared by every deck of the challenge. A deck's Makefile sets
# PUBLISH (where `make publish` copies main.pdf), then includes this file.
# Code snippets live in the deck's code/; gen/ holds their highlighted LaTeX.
COMMON   = ../common
TEMPLATE = ../template
STYLE   ?= friendly
PYG      = pygmentize -f latex -O escapeinside=^^
CODE     = $(wildcard code/*.lean code/*.sql)
GEN      = $(patsubst code/%,gen/%.tex,$(CODE)) gen/pygments.tex

main.pdf: main.tex $(COMMON)/preamble.tex $(COMMON)/links.tex \
          $(TEMPLATE)/dcptalk.sty $(GEN)
	TEXINPUTS=$(COMMON)//:$(TEMPLATE)//: latexmk -lualatex \
	  -interaction=nonstopmode main.tex

# The copy for the website (unlisted: no _talks entry, not in the sitemap)
publish: main.pdf
	cp main.pdf $(PUBLISH)

gen/pygments.tex: $(COMMON)/deck.mk | gen
	$(PYG) -S $(STYLE) > $@

gen/%.lean.tex: code/%.lean | gen
	$(PYG) -l lean4 -o $@ $<

gen/%.sql.tex: code/%.sql | gen
	$(PYG) -l sql -o $@ $<

gen:
	mkdir -p gen

clean:
	latexmk -C
	rm -f main.notes
	rm -rf gen

.PHONY: clean publish
