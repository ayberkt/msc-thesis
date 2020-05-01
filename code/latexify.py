#!/usr/bin/env python3
import sys

code_block_started = False

with open(sys.argv[1], encoding="utf-8") as f:
  for line in f:
    if line[0:3] == "```":
      if not code_block_started:
        print("\\begin{code}")
        code_block_started = True
      else:
        print("\\end{code}")
        code_block_started = False
    elif line[0:3] == "## ":
      print("\\subsection{{{}}}".format(line[3:].rstrip()))
    else:
      print(line, end="")
