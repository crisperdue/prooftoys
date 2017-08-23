// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

////
//// Support utilities for expr.js
////


// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

// Make some names available without "Toy" prefix.
var assert = Toy.assertTrue;
var err = Toy.err;

////
//// Bindings -- variable binding contexts and bookkeeping for
//// changing names of bound variables.
////

/**
 * Binding (for a set of variables).  From is a Atom, to is an Expr it
 * is bound to.  "More" refers to another bindings unlless it is null,
 * so this can represent a set of bindings rather than just one.  Used
 * in copying to replace occurrences of variables with replacements.
 *
 * In _addFreeNames, bindings contain variables that are bound and thus
 * not free in an expression's lexical context.  In that case the
 * bindings all have the value "true".
 */
function Bindings(from, to, more) {
  this.from = from;
  this.to = to;
  this.more = more;
}

/**
 * Returns the number of bindings represented by this object,
 * or you could say, the depth of nesting.
 */
function numBindings(bindings) {
  var i = 0;
  for (var b = bindings; b; b = b.more) {
    i++;
  }
  return i;
}

/**
 * Finds and returns the binding in bindings with "from" equal
 * to the target, or null if it finds no such binding.
 */
function findBinding(target, bindings) {
  return bindings == null
    ? null
    : (target == bindings.from)
    ? bindings
    : findBinding(target, bindings.more);
}

/**
 * Like findBinding, but searches for a binding with "to" part equal
 * to the target value.
 */
function findBindingValue(targetValue, bindings) {
  return bindings == null
    ? null
    : (targetValue === bindings.to)
    ? bindings
    : findBindingValue(targetValue, bindings.more);
}

/**
 * Returns the replacement for the target in the given Bindings, or
 * null if none is found.
 */
function getBinding(target, bindings) {
  var found = findBinding(target, bindings);
  return found ? found.to : null;
}


////
//// Path -- designating parts of expressions.
////

// TODO: Consider defining distinct subclases for forward and reverse
//   paths.

/**
 * Construct a Path from a segment string ('fn', 'arg', 'bound',
 * 'body', 'left', 'right', 'binop', or null) and an optional Path,
 * which defaults to an empty path.  Thus if "rest" is null the result
 * is a path with a single segment, and if both are null it is an
 * empty path.
 */
function Path(segment, rest) {
  this.segment = segment;
  this.rest = rest || _end;;
}

// The chain of Path objects goes on forever.
Path.none = new Path(null, null);

// This makes the chain endless.
Path.none.rest = Path.none;

// This marks the end of the path.  Past this is nothing
// interesting.
var _end = new Path(null, Path.none);

// The empty path.
Path.empty = _end;

/**
 * Truthy value iff this path is precisely empty (and not beyond).
 */
Path.prototype.isMatch = function() {
  return this == _end;
};

Path.prototype.isEnd = function() {
  return this == _end;
};

/**
 * Does the path refer to an expression on the left side of an infix
 * operator?  The given path must be applicable to a call to an infix
 * operator.
 *
 * TODO: Change this when changing the meaning of infix.
 */
Path.prototype.isLeft = function() {
  return (this.segment == 'left'
          || (this.segment == 'fn'
              && this.rest
              && this.rest.segment =='arg'));
};

Path.prototype.getLeft = function() {
  assert(this.isLeft(), 'Not a leftward path: {1}', this);
  // TODO: Change this when changing the meaning of infix.
  return this.rest.rest;
};

/**
 * Returns a Path that has all but the last segment of this path.
 * If this path has no segments, throws an error.
 */
Path.prototype.parent = function() {
  var segment = this.segment;
  if (!segment) {
    // Also includes the case where we are past the end.
    err('Empty path can have no parent.');
  }
  var rest = this.rest;
  if (rest.isEnd()) {
    return path();
  } else {
    return new Path(segment, this.rest.parent());
  }
};

/**
 * Returns the path that results by getting the "rest" of this path
 * N times in succession.
 */
Path.prototype.nth = function(n) {
  var tail = this;
  for (var i = 0; i < n; i++) {
    tail = tail.rest;
  }
  return tail;
};

/**
 * Returns a path with the first N segments of this path.
 */
Path.prototype.firstN = function(n) {
  var tail = this;
  var rev = Toy.Path.empty;
  for (var i = 0; i < n; i++) {
    rev = new Path(tail.segment, rev);
    tail = tail.rest;
  }
  return rev.reverse();
};

/**
 * Returns the prefix of this path preceding the given tail.  If the
 * given tail is not actually a tail of this path, returns null.  No
 * conversion between pretty and non-pretty paths is done, each must
 * have the same style.
 *
 * If the tail is given as a string it will be converted to a path.
 */
Path.prototype.upTo = function(tail) {
  var revTail = path(tail).reverse();
  var revPath = this.reverse();
  while (true) {
    if (revTail.isEnd()) {
      return revPath.reverse();
    }
    if (revPath.isEnd()) {
      return null;
    }
    if (revPath.segment != revTail.segment) {
      return null;
    }
    revPath = revPath.rest;
    revTail = revTail.rest;
  }
};

/**
 * Gets the last segment from the path, or null if the path is empty.
 */
Path.prototype.last = function() {
  var p = this;
  var segment = null;
  while (!p.isEnd()) {
    segment = p.segment;
    p = p.rest;
  }
  return segment;
};

/**
 * Does the path refer to an expression on the right side of an infix
 * operator?  The given path must be applicable to a call to an infix
 * operator.
 *
 * TODO: Change this when changing the meaning of infix.
 */
Path.prototype.isRight = function() {
  return this.segment == 'right' || this.segment == 'arg';
};

Path.prototype.getRight = function() {
  assert(this.isRight(), 'Not a rightward path: {1}', this);
  // TODO: Change this when changing the meaning of infix.
  return this.rest;
};

Path.prototype.tail = function() {
  return this.rest;
};

/**
 * Empty path displays as '', otherwise "/ segment"
 * for each segment of the path.
 */
Path.prototype.toString = function() {
  var content = '';
  if (this == Path.none) {
    content = '(none)';
  } else if (this == _end) {
    content = '';
  } else {
    var path = this;
    while (path != _end) {
      content = content + '/' + path.segment;
      path = path.rest;
    }
  }
  return content;
};

/**
 * Pseudo-constructor: returns a Path based on a "/"-separated string
 * or an array of strings, or a Bindings.  The parts become the
 * segments of the path.  Some segments serve as macros that expand
 * into a list of other segments, currently 'left', 'right', and
 * 'binop'.
 *
 * If the optional expr is supplied, adjust any /main path according
 * to whether the expr has hypotheses or not, and any /rt path
 * based on the expr being a conditional.
 *
 * A null input indicates an empty path.
 */
function path(arg, opt_expr) {
  var expr = opt_expr;

  // If the initial segment of the path is 'main', and the expression
  // is given and has hypotheses, return a path to its RHS.
  // Similarly for 'rt' for a conditional.
  function adjust(path) {
    if (expr) {
      var segment = path.segment;
      if (segment == 'main') {
        path = path.rest;
        if (expr.hasHyps) {
          path = new Path('right', path);
        }
      } else if (segment == 'rt') {
        path = path.rest;
        if (expr.isCall2('=>')) {
          path = new Path('right', path);
        }
      }
    }
    return path;
  }

  if (arg instanceof Path) {
    return adjust(arg);
  }
  if (arg == null) {
    arg = '';
  }
  // If a Bindings, reverse it into an array and go from there.
  if (arg instanceof Bindings) {
    var array = [];
    while (bindings != null) {
      array.unshift(bindings.from);
    }
    arg = array;
  }
  var segments = (typeof arg == 'string')
    ? arg.split('/')
    : arg;
  // Remove the empty first element resulting from an initial "/".
  // Even an empty string splits into an array with one element.
  if (segments[0] == '') {
    segments.splice(0, 1);
  }
  // Handle the result of splitting '/' => ['', '']:
  if (segments.length == 1 && segments[0] == '') {
    segments = [];
  }
  var result = _end;
  while (segments.length) {
    var piece = segments.pop();
    result = new Path(piece, result);
  }
  return adjust(result);
}

/**
 * Create a path that contains all the segments of this path followed
 * by all the segments of the path argument.
 */
Path.prototype.concat = function(p) {
  p = path(p);
  if (this == _end) {
    return p;
  } else {
    return new Path(this.segment, this.rest.concat(p));
  }
};

/**
 * For a forward path, expands left, right, and binop segments into
 * their primitive fn and arg components.
 */
Path.prototype.expand = function() {
  function xpand(segment, tail) {
    var xrest = tail.isEnd() ? tail : xpand(tail.segment, tail.rest);
    switch (segment) {
    case 'left':
      return new Path('fn', new Path('arg', xrest));
    case 'right':
      return new Path('arg', xrest);
    case 'binop':
      return new Path('fn', new Path('fn', xrest));
    default:
      return new Path(segment, xrest);
    }
  }
  assert(this !== Path.none, 'Illegal "none" Path');
  return (this.isEnd()
          ? this
          : xpand(this.segment, this.rest));
};

/**
 * Returns a new Path whose segments are the reverse of the segments
 * in the given path.
 */
Path.prototype.reverse = function() {
  var revPath = this;
  var result = path();
  while (!revPath.isEnd()) {
    result = new Path(revPath.segment, result);
    revPath = revPath.tail();
  }
  return result;
};

//// Export public names.

Toy.Bindings = Bindings;
Toy.numBindings = numBindings;
Toy.findBinding = findBinding;
Toy.findBindingValue = findBindingValue;
Toy.getBinding = getBinding;

Toy.Path = Path;
Toy.path = path;

})();
