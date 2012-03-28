// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

var Toy = Toy || {};

// Boilerplate text for the left navigation area.
Toy.navText = [
  '<a class=nav href="index.html">',
  'Home page</a>',
  '<a class=nav href="http://code.google.com/p/jlogic/wiki/LanguageSummary">',
  'Summary of the Language</a>',
  '<a class=nav href="proofbuilder.html">',
  'Interactive proof builder</a>',
  '<a class=nav href="real-numbers.html">',
  'Working with real numbers',
  '<a class=nav href="http://code.google.com/p/jlogic/wiki/AboutTheLogic">',
  'About the logic</a>',
  '<a class=nav href="http://code.google.com/p/jlogic">',
  'Project site</a>',
  '<a class=nav href="http://code.google.com/p/jlogic/source/checkout">',
  'Source code</a>',
  '<a class=nav',
  'href="http://code.google.com/p/jlogic/issues/entry?template=Comment/suggestion">',
  'Feedback</a>',
].join('\n');

Toy.insertNav = function() {
  var nav = document.getElementById('leftNav');
  if (nav) {
    nav.innerHTML = Toy.navText;
  }
};

Toy.insertSlogans = function() {
  var slogans = ['toward tools and a community for connecting<br>' +
                 'people and mathematical reasoning'].join('\n');
  var elt = document.getElementById('slogans');
  if (elt) {
    elt.innerHTML = slogans;
  }
};


// Google analytics

var _gaq = _gaq || [];
_gaq.push(['_setAccount', 'UA-28801147-2']);
_gaq.push(['_trackPageview']);

(function() {
  var ga = document.createElement('script'); ga.type = 'text/javascript'; ga.async = true;
  ga.src = ('https:' == document.location.protocol ? 'https://ssl' : 'http://www') + '.google-analytics.com/ga.js';
  var s = document.getElementsByTagName('script')[0]; s.parentNode.insertBefore(ga, s);
})();
