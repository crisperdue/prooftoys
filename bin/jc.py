#!/usr/bin/python

# Preprocessor for nicer OOP notation in JavaScript.

import argparse
import glob
import os
import os.path
import re
import sys
import time

# Pattern to match preprocessor directives, or doc comments
# that should not be searched for directives.
atPattern = re.compile('''/[*][*].*?[*]/ |  # doc comment
                          @[a-zA-Z_0-9]+ |  # @identifier
                          @[(]([a-zA-Z0-9$_,\s]*)[)]\s*[{] |  # method (grp 1)
                          @[{]([a-zA-Z0-9$_,\s]*)[.]\s+ |     # fn (grp 2)
                          @[{]
                       ''',
                       re.DOTALL | re.VERBOSE)

# Compiles a file with possible preprocessor directives into plain JavaScript.
def compile(jsc, js):
  sys.stdout.write('compiling {0}\n'.format(jsc))
  def replace(match):
    m = match.group(0)
    if m.startswith('/**'):
      # doc comment
      return m
    elif m.startswith('@('):
      # method
      return ('function(' + match.group(1) + ') { var self = this; ')
    elif m.startswith('@{'):
      # function with immediate return expression
      if match.lastindex == 2:
        return ('function(' + match.group(2) + ') { return ')
      else:
        return 'function() { return '
    else:
      return 'self.__' + m[1:]
  try:
    os.mkdir('jsc')
  except OSError:
    # Ignore the OSError, which usually means the directory already exists.
    pass
  with open(jsc) as input:
    with open(js, 'w') as output:
      output.write(atPattern.sub(replace, input.read()))
  
# Gets the modification time of the named file, or return 0
# if the file cannot be found.
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
    for jsc in names:
      basename, _ = os.path.splitext(jsc)
      js = os.path.join('jsc', basename + '.js')
      jsctime = getmtime(jsc)
      jstime = getmtime(js)
      # Compile the .jsc file
      compile(jsc, js)

# For debugging use with LiveReload:
# with open('/tmp/foobar', 'w') as msg:
#   msg.write(str(str(sys.argv)) + '\n')

if __name__ == '__main__':
    main()

