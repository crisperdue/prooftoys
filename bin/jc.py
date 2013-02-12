#!/usr/bin/python

# Preprocessor for nicer OOP notation in JavaScript.

import argparse
import glob
import os
import os.path
import re
import sys
import time

atPattern = re.compile('''/[*][*].*?[*]/|  # doc comment
                          @[a-zA-Z_0-9]+|  # @identifier
                          @[(]([a-zA-Z0-9$_,\s]*)[)]\s*[{]   # method
                       ''',
                       re.DOTALL | re.VERBOSE)

def compile(jr, jsc):
  sys.stdout.write('compiling {0}\n'.format(jr))
  def replace(match):
    m = match.group(0)
    if m.startswith('/**'):
      return m
    elif m.startswith('@('):
      return ('function(' + match.group(1) + ') { var self = this; ')
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
  parser = argparse.ArgumentParser()
  parser.add_argument('--monitor', action='store_true')
  parser.add_argument('files', nargs='+')
  args = parser.parse_args()
  names = args.files
  if args.monitor:
    sys.stderr.write('Unimplemented\n')
    sys.exit(1)
  else:
    for js in names:
      basename, _ = os.path.splitext(js)
      jsc = basename + '.jsc'
      jstime = getmtime(js)
      jsctime = getmtime(jsc)
      # Compile the .js file
      compile(js, jsc)

if __name__ == '__main__':
    main()

