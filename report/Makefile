all: main.pdf

main.pdf: main.tex settings.tex content/introduction.tex
	tectonic $<

.PHONY:
clean:
	rm -f main.pdf
