all: proposal.pdf

proposal.pdf: proposal.tex references.bib
	latexmk -pdf $<

clean:
	latexmk -C proposal.tex
