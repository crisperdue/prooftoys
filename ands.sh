#!/bin/bash

# Find occurrences of a single ampersand 
# In HTML, ones followed by alphabetics or # are character entities,
# so don't show those.
grep -P "(?<!&)&(?![&a-zA-Z#])" $(ls *.js *.html | grep -v jquery-)
