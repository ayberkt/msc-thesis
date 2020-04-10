#!/usr/bin/env python3
import sys

line_num = 1

with open(sys.argv[1], encoding="utf-8") as f:
  for line in f:
    if len(line) > 91:
      print("Line {} is longer than 90 characters.".format(line_num))
      sys.exit(1)

    if not (line == "\n"):
      if(line[-2].isspace()):
        print("Line {} has trailing spaces.".format(line_num))
        sys.exit(1)

    line_num += 1

print("OK.")
sys.exit(0)
