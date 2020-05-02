all: main.pdf

.PHONY: references.bib
references.bib:
	wget http://127.0.0.1:23119/better-bibtex/collection?/1/Thesis//Core.biblatex -O $@

.PHONY: literate-latex
literate-latex:
	rm -rf literate-latex
	cd ../code && ./latexify.sh
	mv ../code/literate-latex .

main.pdf: main.tex introduction.tex foundations.tex frames.tex formal-topology.tex conclusion.tex agda-formalisation.tex agda.sty
	xelatex -interaction=nonstopmode $<
	biber main.bcf
	xelatex -interaction=nonstopmode $<
	xelatex -interaction=nonstopmode $<
	rm -f main.aux main.bbl main.bcf main.blg main.lof main.lot main.out main.ptb main.run.xml main.toc

keep-log: main.tex introduction.tex foundations.tex frames.tex formal-topology.tex conclusion.tex agda-formalisation.tex agda.sty
	xelatex -interaction=nonstopmode $<
	biber main.bcf
	xelatex -interaction=nonstopmode $<
	xelatex -interaction=nonstopmode $<
	rm -f main.aux main.bbl main.bcf main.blg main.lof main.lot main.out main.ptb main.run.xml main.toc

.PHONY: remove-log
remove-log: main.pdf
	rm -f main.log

.PHONY: clean
clean:
	rm -f main.pdf
