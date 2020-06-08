all: main.pdf

main.pdf: main.tex macros.tex introduction.tex foundations.tex frames.tex formal-topology.tex conclusion.tex agda-formalisation.tex cantor.tex agda.sty
	latexmk -xelatex -interaction=nonstopmode main.tex

.PHONY: update-refs
update-refs: references.bib main.pdf

.PHONY: references.bib
references.bib:
	curl http://127.0.0.1:23119/better-bibtex/collection?/1/NGA6LCZ3.biblatex > $@

.PHONY: dropbox
dropbox: main.pdf
	cp -f main.pdf ~/Dropbox/thesis/main.pdf

.PHONY: literate-latex
literate-latex:
	rm -rf literate-latex
	cd ../code && ./latexify.sh
	mv ../code/literate-latex .

.PHONY: clean
clean:
	rm -f main.pdf *.bbl *.bcf *.blg *.fdb_latexmk *.fls *.loq *.lot *.out *.ptb *.run.xml *.toc *.aux *.log *.lof
