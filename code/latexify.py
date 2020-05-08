#!/usr/bin/env python3
import sys
import os
import subprocess

files = [ "Basis.lagda.md",
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

  output_file_name   = fname.split(".")[0] + ".lagda"
  output_file        = open("literate-latex/" + output_file_name, "w+")

  output_file.write("\\begin{code}\n")

  code_block_started = False

  with open(fname, encoding="utf-8") as f:
    for line in f:
      if line[0:3] == "```":
        code_block_started = not code_block_started
      elif line[0:3] == "## ":
        output_file.write("\\end{code}\n")
        output_file.write("\\subsection*{{{}}}\n".format(line[3:].rstrip()))
        output_file.write("\\begin{code}\n")
      elif line[0:4] == "### ":
        output_file.write("\\end{code}\n")
        output_file.write("\\subsubsection*{{{}}}\n".format(line[4:].rstrip()))
        output_file.write("\\begin{code}\n")
      else:
        if line == "\n":
          output_file.write("\n")
        else:
          if not code_block_started:
            output_file.write("-- " + line)
          else:
            output_file.write(line)

  output_file.write("\\end{code}\n")
  output_file.close()

if __name__ == "__main__":
  try:
    os.mkdir("literate-latex")
    print("Directory " , "`literate-latex`", " created")
  except:
    print("Directory `literate-latex` already exists.")

  fname              = sys.argv[1]
  output_file_name   = fname.split(".")[0] + ".lagda"

  if len(fname.split(".")) == 3:
    latexify(fname)
  elif len(fname.split(".")) == 2:
    latexify_illiterate(fname)
