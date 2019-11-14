#!/usr/bin/env python3
import sys

res = True

with open(sys.argv[1]) as f:
  for line in f:
    if len(line) > 91:
      print(line.strip())
      res = False

if res:
  print("OK.")
  sys.exit(0)
else:
  print("File has lines longer than 90 characters.")
  sys.exit(1)
