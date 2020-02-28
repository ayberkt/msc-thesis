#!/usr/bin/env python3
import sys

res = True

count = 1

with open(sys.argv[1], encoding="utf-8") as f:
  for line in f:
    if len(line) > 91:
      print(line.strip())
      res = False
      break
    count += 1

if res:
  print("OK.")
  sys.exit(0)
else:
  print("Line {} is longer than 90 characters.".format(count))
  sys.exit(1)
