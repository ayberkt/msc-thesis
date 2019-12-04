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

.PHONY:
clean:
	rm -rf html
