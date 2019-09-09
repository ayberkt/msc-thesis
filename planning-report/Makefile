all: report.pdf

report.pdf: report.tex references.bib
	latexmk -pdf $<

clean:
	latexmk -C report.tex
