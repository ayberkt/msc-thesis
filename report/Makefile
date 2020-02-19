all: main.pdf

.PHONY: references.bib
references.bib:
	wget http://127.0.0.1:23119/better-bibtex/collection?/1/NGA6LCZ3.biblatex -O $@

main.pdf: main.tex
	tectonic $<
