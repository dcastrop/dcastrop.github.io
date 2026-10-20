# Code snippets live in code/; gen/ holds their highlighted LaTeX.
STYLE ?= friendly
PYG    = pygmentize -f latex -O escapeinside=^^
CODE   = $(wildcard code/*.v code/*.ml code/*.txt)
GEN    = $(patsubst code/%,gen/%.tex,$(CODE)) gen/pygments.tex

main.pdf: main.tex preamble.tex sections/*.tex ../template/dcptalk.sty $(GEN)
	TEXINPUTS=../template//: latexmk -lualatex -interaction=nonstopmode main.tex
	python3 ../template/make-notes.py main --duration 50

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
	rm -f main.notes main.pdfpc main-notes.md
	rm -rf gen

.PHONY: clean
