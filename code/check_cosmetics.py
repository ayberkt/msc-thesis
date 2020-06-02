#!/usr/bin/env python3
import sys

files = [ "FormalTopology.agda",
          "Cover.lagda.md",
          "CoverFormsNucleus.lagda.md",
          "Nucleus.agda",
          "Poset.lagda.md",
          "SnocList.agda",
          "CantorSpace.lagda.md",
          "Frame.agda",
          "UniversalProperty.lagda.md"
        ]

def check_cosmetics_of_file(fname):
  print("* Checking cosmetics of {}...".format(fname), end="")

  line_num = 1

  with open(fname, encoding="utf-8") as f:
    for line in f:
      if len(line) > 91:
        print("\n  - Line {} is longer than 90 characters.".format(line_num))
        return False

      if not (line == "\n"):
        if(line[-2].isspace()):
          print("\n  - Line {} has trailing spaces.".format(line_num))
          return False

      if " Set " in line:
        print("  - Line {} uses the name `Set`.".format(line_num))
        return False

      line_num += 1

  print("  OK")
  return True

if __name__ == "__main__":
  for fname in files:
    if not check_cosmetics_of_file(fname):
      sys.exit(1)

  sys.exit(0)
