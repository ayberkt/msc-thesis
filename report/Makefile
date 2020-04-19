all: main.pdf

.PHONY: references.bib
references.bib:
	wget http://127.0.0.1:23119/better-bibtex/collection?/1/Thesis//Core.bibtex -O $@

main.tex: main.lagda
	agda --latex --latex-dir=. $<

introduction.tex: introduction.lagda
	agda --latex --latex-dir=. $<

foundations.tex: foundations.lagda
	agda --latex --latex-dir=. $<

frames.tex: frames.lagda
	agda --latex --latex-dir=. $<

formal-topology.tex: formal-topology.lagda
	agda --latex --latex-dir=. $<

main.pdf: main.tex introduction.tex foundations.tex frames.tex formal-topology.tex agda.sty
	tectonic main.tex
