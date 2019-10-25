all: html/Coverage.html

html/Coverage.md: Coverage.lagda.md Agda.css
	agda --html --html-highlight=code Coverage.lagda.md
	cp Agda.css html/Agda.css

.ONESHELL:
html/Coverage.html: html/Coverage.md
	cd html
	pandoc Coverage.md --css Agda.css -o Coverage.html

.PHONY:
clean:
	rm -rf html
