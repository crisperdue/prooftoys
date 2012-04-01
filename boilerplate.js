// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

// TODO: deploy with yui-min.js rather than yui.js
var yuiPath =
  ('<script src="http://yui.yahooapis.com/3.4.1/build/yui/yui.js">' +
   '</script>\n');
// For debugging add explicit reference to source file(s) here
document.write(yuiPath);
document.write('<script src="expr.js"></script>\n');
document.write('<script src="step-editor.js"></script>\n');
document.write('<script src="proof.js"></script>\n');
document.write('<script src="theorems.js"></script>\n');

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
