#!/bin/bash

# Replace occurrences of || followed by an odd number of single quotes
# Multiple occurrences can be replaced per line.
perl -i -ple "s{\|\|(?=[^']*'([^']*'[^']*')*[^']*\$)}{|}g" *.js tests.html
# Similarly for &&
perl -i -ple "s{&&(?=[^']*'([^']*'[^']*')*[^']*\$)}{&}g" *.js tests.html
