#!/bin/bash

declare -a files=("Basis.lagda.md"
                  "FormalTopology.agda"
                  "Cover.lagda.md"
                  "CoverFormsNucleus.lagda.md"
                  "Nucleus.agda"
                  "Poset.lagda.md"
                  "SnocList.agda"
                  "CantorSpace.lagda.md"
                  "Frame.agda"
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
