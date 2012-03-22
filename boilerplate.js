// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('boilerplate', function(Y) {

// Boilerplate text for the left navigation area.
var navText = [
  '<a class=nav href="proofbuilder.html">',
  'Interactive proof builder</a>',
  '<a class=nav href="http://code.google.com/p/jlogic/wiki/LanguageSummary">',
  'Summary of the Language</a>',
  '<a class=nav href="http://code.google.com/p/jlogic/wiki/AboutTheLogic">',
  'About the logic</a>',
  '<a class=nav href="http://code.google.com/p/jlogic">',
  'Project site</a>',
  '<a class=nav href="http://code.google.com/p/jlogic/source/checkout">',
  'Source code</a>',
  '<a class=nav',
  'href="http://code.google.com/p/jlogic/issues/entry?template=Comment/suggestion">',
  'Comments etc.</a>',
].join('\n');

Y.on('domready', function() {
  var nav = Y.one('#leftNav');
  if (nav) {
    nav.setContent(navText);
  }
});

});
