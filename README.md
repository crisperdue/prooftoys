# Prooftoys

Prooftoys is a visual proof assistant and
the engine behind Mathtoys (http://mathtoys.org).
The Prooftoys implementation is based on [Alonzo Church's 
simple type theory](http://plato.stanford.edu/entries/type-theory-church/)
as formulated by Carnegie Mellon University
[Professor Peter Andrews](http://gtps.math.cmu.edu/andrews.html)
under the name [Q0](http://en.wikipedia.org/wiki/Q_zero).
Simple type theory is suitable for construction
of most of mathematics, comparable to first-order
logic plus set theory.  It uses a minimum of
simple, understandable concepts, expressing them with
a handful of axioms and inference rules. 

Prooftoys is written in TypeScript, which runs as
JavaScript in the user's
web browser.  It is designed to be highly interactive and delivered
to users through the Web, so they can play with it instantly.
Prooftoys has a web site with pages for interacting with it
at http://prooftoys.org/.

This repo used to have the assets for the prooftoys.org website, but
files related to the webiste are now at
http://github.com/crisperdue/prooftoys-site/.

[Mathtoys](http://mathtoys.org) is an interface to Prooftoys tuned for
working high school algebra problems.  Its unique HTML and code is also
on GitHub at http://github.com/crisperdue/mathtoys.

## Embedding Prooftoys in another website

While in principle the two can be separated, the Prooftoys engine is intended to
be integrated with its web-based user interface.  The two together _are_
intended for embedding in other websites.  Here is a sample page that shows
a simple embedding of Prooftoys in a web page.

The usage here is in the most straightforward form, suitable for development
but entirely unoptimized.  For example the `.js` files are
all loaded individually rather than being concatenated first.

````HTML
<!doctype html>
<html lang=en>
<head>
<title>Prooftoys sample</title>
<meta charset="utf-8">
<meta name="viewport"
 content="width=device-width, initial-scale=1, shrink-to-fit=no">
<link rel="stylesheet"
 href="https://cdn.jsdelivr.net/npm/bootstrap@4.6.1/dist/css/bootstrap-reboot.css"
 crossorigin="anonymous">

<link rel="stylesheet" href="/css/pt.css">
<script src="https://code.jquery.com/jquery-3.6.0.js"></script>
</head>

<body>
<h2>Prooftoys proof builder</h2>
<div class="proof-editor logicZone">

<script src="/pt/js/site.js"></script>
<script src="/pt/js/util.js"></script>
<script src="/pt/js/prelim.js"></script>
<script src="/pt/js/expr.js"></script>
<script src="/pt/js/xutil.js"></script>
<script src="/pt/js/engine.js"></script>
<script src="/pt/js/unify.js"></script>
<script src="/pt/js/logic.js"></script>
<script src="/pt/js/numbers.js"></script>
<script src="/pt/js/step-editor.js"></script>
<script src="/pt/js/rendering.js"></script>
<script src="/pt/js/solution-status.js"></script>
</body>
</html>
````

This example assumes that the Prooftoys JavaScript files have
been copied over to locations served as `/pt/js`.
The file `/css/pt.css` is generated from `scss/pt.scss`
(and implicitly `scss/proofs.scss`) using the 
[sass](https://sass-lang.com/) transpiler and placed
in the `css` directory of the site, e.g. `sass pt.scss pt.css`.

I use the [Hugo](https://gohugo.io/) static site generator, which has an
embedded implementation of `sass`.  Given a repository
with `pt.scss` and `proofs.scss` available in `assets/scss/`,
this is typically done in Hugo with code like:

````
{{ $pt := resources.Get "scss/pt.scss" |
   toCSS (dict "targetPath" "css/pt.css") }}
<link rel="stylesheet" href="{{ $pt.RelPermalink }}">
````
