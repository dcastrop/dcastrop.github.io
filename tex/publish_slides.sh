#!/bin/zsh

pushd $1
rm -f slides.tgz
latexmk -pdf slides.tex
latexmk -c slides.tex
rm -rf _minted-slides slides.nav slides.snm slides.vrb
popd

tar -cvzpf slides.tgz $1
mv slides.tgz $1
