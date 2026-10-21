# Code snippets live in code/; gen/ holds their highlighted LaTeX.
STYLE ?= friendly
PYG    = pygmentize -f latex -O escapeinside=^^
CODE   = $(wildcard code/*.v code/*.ml code/*.txt)
GEN    = $(patsubst code/%,gen/%.tex,$(CODE)) gen/pygments.tex

main.pdf: main.tex preamble.tex sections/*.tex ../template/dcptalk.sty $(GEN)
	TEXINPUTS=../template//: latexmk -lualatex -interaction=nonstopmode main.tex
	python3 ../template/make-notes.py main --duration 55

# Slides with their notes on the right half: pdfpc -n right main-presenter.pdf
presenter: main-presenter.pdf

main-presenter.pdf: main.pdf ../template/make-presenter.py
	python3 ../template/make-presenter.py main
	latexmk -lualatex -interaction=nonstopmode main-presenter.tex

# Copies for the website: slides.pdf is linked, slides_notes.pdf is not
publish: main.pdf main-presenter.pdf
	cp main.pdf ../slides.pdf
	cp main-presenter.pdf ../slides_notes.pdf

gen/pygments.tex: Makefile | gen
	$(PYG) -S $(STYLE) > $@

gen/%.v.tex: code/%.v code/rocqlexer.py | gen
	$(PYG) -x -l code/rocqlexer.py:RocqLexer -o $@ $<

gen/%.ml.tex: code/%.ml | gen
	$(PYG) -l ocaml -o $@ $<

gen/%.txt.tex: code/%.txt | gen
	$(PYG) -l text -o $@ $<

gen:
	mkdir -p gen

clean:
	latexmk -C
	latexmk -C main-presenter.tex
	rm -f main-presenter.tex main.notes main.pdfpc main-notes.md
	rm -rf gen

.PHONY: clean presenter publish
