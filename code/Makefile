all: html/Coverage.html html/TreeType.html

html/%.md: %.lagda.md Agda.css
	agda --html --html-highlight=code $<
	cp Agda.css html/Agda.css

.ONESHELL:
html/%.html: html/%.md
	cd html
	pandoc $*.md --css Agda.css -o $*.html

.PHONY:
clean:
	rm -rf html
