#!/bin/bash

# Search for occurrences of single "|" characters.
grep -P "(?<![|])[|](?![|])" $(ls *.js *.html | grep -v jquery-)
