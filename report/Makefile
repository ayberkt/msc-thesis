all: main.pdf

foo:
	wget http://127.0.0.1:23119/better-bibtex/collection?/1/NGA6LCZ3.biblatex -O references-new.bib

references.bib: foo
	cmp references-new.bib $@ || mv references-new.bib $@
	rm -f references-new.bib

main.pdf: main.tex references.bib
	tectonic $<
