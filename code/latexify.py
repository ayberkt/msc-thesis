#!/usr/bin/env python3
import sys
import os

files = [ "Basis.lagda.md",
          "Powerset.agda",
          "Family.agda",
          "FormalTopology.agda",
          "Cover.lagda.md",
          "CoverFormsNucleus.lagda.md",
          "Nucleus.agda",
          "Poset.lagda.md",
          "SnocList.agda",
          "CantorSpace.lagda.md",
          "Frame.agda",
          "ProductTopology.agda",
          "UniversalProperty.lagda.md"
        ]

def latexify_illiterate(fname):
  print("Processing illiterate file: " + fname)
  output_file_name   = fname.split(".")[0] + ".lagda"
  output_file        = open("literate-latex/" + output_file_name, "w+")

  output_file.write("\\begin{code}\n")
  with open(fname, encoding="utf-8") as f:
    for line in f:
      output_file.write(line)
  output_file.write("\\end{code}")

  output_file.close()

def latexify(fname):
  print("Processing literate file: " + fname)

  code_block_started = False
  output_file_name   = fname.split(".")[0] + ".lagda"
  output_file        = open("literate-latex/" + output_file_name, "w+")

  with open(fname, encoding="utf-8") as f:
    for line in f:
      if line[0:3] == "```":
        if not code_block_started:
          output_file.write("\\begin{code}\n")
          code_block_started = True
        else:
          output_file.write("\\end{code}\n")
          code_block_started = False
      elif line[0:3] == "## ":
        output_file.write("\\subsection{{{}}}\n".format(line[3:].rstrip()))
      elif line[0:4] == "### ":
        output_file.write("\\subsubsection{{{}}}\n".format(line[4:].rstrip()))
      else:
        if code_block_started:
          output_file.write(line)
        else:
          if line == "\n":
            output_file.write("\n")
          else:
            output_file.write(line)

  output_file.close()

if __name__ == "__main__":
  try:
    os.mkdir("literate-latex")
    print("Directory " , "`literate-latex`", " created")
  except:
    print("Directory `literate-latex` already exists.")

  for fname in files:
    if len(fname.split(".")) == 3:
      latexify(fname)
    elif len(fname.split(".")) == 2:
      latexify_illiterate(fname)
