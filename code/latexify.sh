#!/bin/bash

declare -a files=("Basis.lagda.md"
                  "FormalTopology.lagda.md"
                  "Cover.lagda.md"
                  "CoverFormsNucleus.lagda.md"
                  "Nucleus.lagda.md"
                  "Poset.lagda.md"
                  "SnocList.lagda.md"
                  "CantorSpace.lagda.md"
                  "Frame.lagda.md"
                  "UniversalProperty.lagda.md"
                 )

for file in "${files[@]}"
do
    ./latexify.py "$file"
done

cd literate-latex
for file in *.lagda; do
    echo "Running: agda --latex --latex-dir=. $file"
    agda --latex --latex-dir=. $file
done
