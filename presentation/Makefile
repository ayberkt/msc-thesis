all: presentation.pdf

.PHONY: references.bib
references.bib:
	curl http://127.0.0.1:23119/better-bibtex/collection?/1/KVFQ2T85.biblatex > references.bib

presentation.pdf: presentation.tex
	latexmk -xelatex -interaction=nonstopmode $<

.PHONY: clean
clean:
	rm -f *.pdf *.bcf *.out
