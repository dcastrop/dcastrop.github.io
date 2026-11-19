# Code snippets live in code/; gen/ holds their highlighted LaTeX.
STYLE ?= friendly
PYG    = pygmentize -f latex -O escapeinside=^^
CODE   = $(wildcard code/*.lean code/*.sql)
GEN    = $(patsubst code/%,gen/%.tex,$(CODE)) gen/pygments.tex

main.pdf: main.tex preamble.tex links.tex sections/*.tex ../template/dcptalk.sty $(GEN)
	TEXINPUTS=../template//: latexmk -lualatex -interaction=nonstopmode main.tex

# The copy for the website (unlisted: no _talks entry, not in the sitemap)
publish: main.pdf
	cp main.pdf ../slides.pdf

gen/pygments.tex: Makefile | gen
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
