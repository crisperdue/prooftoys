## Mathtoys (and Prooftoys) development standards and practices

### Setting up development

The mathtoys and prooftoys repos are designed to be laid out as siblings.

With this layout you can serve a Mathtoys site (and a Prooftoys site)
immediately, provided that the web server is willing to follow the
symlinks in your checked out repos.

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

### Modular structure

The system exports exactly one name to the global space, the name "Toy".
Everything else is either a property of "Toy", or internal.  Top level
initializations are wrapped in function bodies to help accomplish this.
