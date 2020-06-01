FILES := html/Main.html html/Poset.html html/Basis.html html/Frame.html\
         html/Cover.html html/Nucleus.html html/CoverFormsNucleus.html\
         html/FormalTopology.html html/CantorSpace.html\
         html/SnocList.html html/UniversalProperty.html

all: main

.PHONY:
main: $(FILES)
	cp -f Agda.css html/Agda.css

html/%.md: %.lagda.md
	agda --html --html-highlight=auto $<

.ONESHELL:
html/%.html: html/%.md
	cd html
	pandoc $*.md --css Agda.css -o $*.html

release.zip: Main.lagda.md Basis.lagda.md Poset.lagda.md Frame.agda Nucleus.agda FormalTopology.agda Cover.lagda.md CoverFormsNucleus.lagda.md UniversalProperty.lagda.md SnocList.agda CantorSpace.lagda.md
	zip $@ $^

.PHONY:
clean:
	rm -rf html
