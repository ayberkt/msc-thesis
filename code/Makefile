FILES := html/Main.html html/Poset.html html/Basis.html html/Frame.html\
         html/HITCoverage.html html/Nucleus.html html/CoverFormsNucleus.html\
         html/Powerset.html html/FormalTopology.html html/CantorSpace.html\
         html/SnocList.html html/ProductTopology.html

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

.PHONY:
clean:
	rm -rf html
