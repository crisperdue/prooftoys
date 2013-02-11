#!/usr/bin/python

# Preprocessor for nicer OOP notation in JavaScript.

import glob
import os
import os.path
import re
import sys
import time

atPattern = re.compile('''/[*][*].*?[*]/|@[a-zA-Z_0-9]+''',
                       re.DOTALL | re.VERBOSE)

def compile(jr, jsc):
  sys.stdout.write('compiling {0}\n'.format(jr))
  def replace(match):
    m = match.group(0)
    if m.startswith('/**'):
      return m
    else:
      return 'self.__' + m[1:]
  with open(jr) as input:
    with open(jsc, 'w') as output:
      output.write(atPattern.sub(replace, input.read()))
  
def getmtime(fname):
  tm = 0.0
  try:
    return os.path.getmtime(fname)
  except OSError:
    return 0.0

def main():
  names = set(sys.argv[1:])
  mtimes = {}
  for js in names:
    basename, _ = os.path.splitext(js)
    jsc = basename + '.jsc'
    jstime = getmtime(js)
    jsctime = getmtime(jsc)
    if jsctime < jstime:
      # Compile the .js file
      compile(js, jsc)

if __name__ == '__main__':
    main()

