## Mathtoys (and Prooftoys) development standards and practices

### Setting up development

The mathtoys and prooftoys repos are designed to be laid out as siblings.

With this layout you can serve a Mathtoys site (and a Prooftoys site)
immediately, provided that the web server is willing to follow the
symlinks in your checked out repos.  A Mathtoys site has the root
of the Mathtoys repo as its document root.

There are no absolute external dependencies, though Font Awesome is
referenced as a remote web site.

The one major external dependency is jQuery.  The system also uses
QUnit.  No external development tools are required.

### JavaScript language

The system is constructed to work in modern web browsers, on desktops only.
It would be great to work on phones, but the system depends heavily on
hovers, which phones do not support, and the screen real estate is also
a major issue on phones.

Polyfills are OK in principle, but at present the language must be
acceptable to Internet Explorer 11.  You may use const and let and rely
on block structure, but otherwise use ES5 syntax.  No translation is
allowed, though I am open to potential future conversion to TypeScript.

### Coding practices

Closely follow my indentation.  I use Java mode in Emacs, specifically
Aquamacs (for Mac OS).  Also follow my comment style.  Each function, method,
and public variable or constant requires careful, clear comments describing
its specification.  Complete sentences are required, except for summaries
of functions and methods, which omit the subject of the sentence.

Also follow my naming practices as far as possible, though they are not
entirely self-consistent.

Maximum line length is 80 characters.  Line terminators must be linefeed
only.

### Modular structure

The system exports exactly one name to the global space, the name "Toy".
Everything else is either a property of "Toy", or internal.  Top level
initializations are wrapped in function bodies to help accomplish this.

A web page gets access to the Mathtoys functionality by having a SCRIPT
tag that refers to boilerplate.js.  This in turn loads the rest of the
system including CSS and fonts.

In the "prooftoys" repository, in folder "js", the main file that
implements the logic is engine.js, and numbers.js
has axioms and theorems related to the real numbers, plus a few items
that properly belong in engine.js and should be moved there.
Files expr.js, prelim.js, util.js, worker.js, and xutil.js contain
various support functions and datatypes.

Files rendering.js and step-editor.js implement the user interface, with
solution-status.js providing support for these.

At present, the "mathtoys" repository contains just files to support the
http://mathtoys.org/ website, using the prooftoys engine.

### Development status

The current system is the result of a long series of experiments and refinements
going back several years.  I believe that the most recent developments to the proof engine
(which does not depend on the UI) are now technically ready to support substantial public use,
with documentation to get users started.  For example the relevant parts of
the Metamath Proof Explorer (http://us.metamath.org/) are proving straightforward
to translate into Mathtoys.

### Jobs for contracts

#### Restructuring engine.js

My top-priority for a contract task at this time is a code restructuring that splits engine.js
into two parts, leaving tautology checking, rules of inference, and proofs of 
the few theorems they depend on in engine.js, but moving the rest of the
definitions and theorems into a new file logic.js, structured in a natural order
with fundamental definitions and theorems first, followed by ones that depend on them.

The changes along the way would need to pass the system test suite, accessed in
the local "prooftoys" site at /tests/index.html.  These take about 30 seconds to run
on a MacBook Air.






