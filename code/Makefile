FILES := html/Main.html html/Poset.html html/Basis.html html/Frame.html\
         html/Cover.html html/Nucleus.html html/CoverFormsNucleus.html\
         html/FormalTopology.html html/CantorSpace.html\
         html/SnocList.html html/UniversalProperty.html html/Index.html

RELEASE_FILES := README.md formal-topology-in-UF.agda-lib lib html\
                 src/Index.lagda.md             src/Main.lagda.md\
                 src/Basis.lagda.md             src/Poset.lagda.md\
                 src/Frame.lagda.md             src/Nucleus.lagda.md\
                 src/FormalTopology.lagda.md    src/Cover.lagda.md\
                 src/CoverFormsNucleus.lagda.md src/UniversalProperty.lagda.md\
                 src/SnocList.lagda.md          src/CantorSpace.lagda.md

all: main

.PHONY:
main: $(FILES)
	cp -f Agda.css html/Agda.css

html/%.md: src/%.lagda.md
	agda --html --html-highlight=auto $<

.ONESHELL:
html/%.html: html/%.md
	cd html
	pandoc $*.md --css Agda.css -o $*.html

thesis-agda-formalisation.tar: $(RELEASE_FILES)
	tar -c -f $@ $^

.PHONY:
clean:
	rm -rf html
