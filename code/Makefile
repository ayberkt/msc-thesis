FILES := html/Main.html html/Poset.html html/Basis.html html/Frame.html\
         html/Cover.html html/Nucleus.html html/CoverFormsNucleus.html\
         html/FormalTopology.html html/CantorSpace.html\
         html/SnocList.html html/UniversalProperty.html html/Index.html

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

thesis-agda-formalisation.tar: README.md Index.lagda.md Main.lagda.md Basis.lagda.md Poset.lagda.md Frame.lagda.md Nucleus.lagda.md FormalTopology.lagda.md Cover.lagda.md CoverFormsNucleus.lagda.md UniversalProperty.lagda.md SnocList.lagda.md CantorSpace.lagda.md
	tar -c -f $@ $^

.PHONY:
clean:
	rm -rf html
