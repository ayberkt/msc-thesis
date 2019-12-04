all: html/Coverage.html html/TreeType.html foo

html/%.md: %.lagda.md Agda.css
	agda --html --html-highlight=code $<
	cp Agda.css html/Agda.css

.ONESHELL:
html/%.html: html/%.md
	cd html
	pandoc $*.md --css Agda.css -o $*.html

foo: html/TreeType.html
	agda --html --html-dir=tmp Main.agda
	mv tmp/Main.html html
	mv tmp/Frame.html html
	mv tmp/Nucleus.html html
	mv tmp/Homotopy.html html
	mv tmp/Poset.html html
	mv tmp/FormalTopologySambin.html html

.PHONY:
clean:
	rm -rf html
