// Copyright Crispin Perdue.  All rights reserved.

////
//// Support utilities for expr.js
////


// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

'use strict';

// Make some names available without "Toy" prefix.
var assert = Toy.assertTrue;
var abort = Toy.abort;

////
//// Bindings -- variable binding contexts and bookkeeping for
//// changing names of bound variables.
////

/**
 * Binding (for a set of variables).  From is usually a variable name,
 * "to" is an Expr it is bound to.  "More" refers to another bindings
 * unless it is null, so this can represent a set of bindings rather
 * than just one.  Used in copying to replace occurrences of variables
 * with replacements.
 *
 * In _addFreeVars, bindings simply have the value "true".
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
function Path(segment, opt_rest) {
  this.segment = segment;
  this.rest = opt_rest || _end;;
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
 * Converts a path with fancy segments right, left, binop, rt, and
 * main into one with just the basic ones.  If the optional argument
 * is truthy, treat initial /main as for a conditional.
 */
Path.prototype.uglify = function(opt_isImplies) {
  const segments = [];
  let tail = this;
  let first = true;
  while (!tail.isEnd()) {
    const tailSeg = tail.segment;
    switch(tailSeg) {
    case 'fn':
    case 'arg':
    case 'bound':
    case 'body':
      segments.push(tailSeg);
      break;
    case 'right':
      segments.push('arg');
      break;
    case 'left':
      segments.push('fn');
      segments.push('arg');
      break;
    case 'binop':
      segments.push('fn');
      segments.push('fn');
      break;
    case 'rt':
    case 'main':
      if (first) {
        if (opt_isImplies) {
          segments.push('arg');
        }
      } else {
        assert(false, 'Segment "{1}" not first in path {2}', tailSeg, this);
      }
      break;
    default:
      assert(false, 'Bad segment "{1}" in path {2}', tailSeg, this);
    }
    first = false;
    tail = tail.rest;
  }
  // This uses a private calling convention of asPath.
  return asPath(segments); 
};

/**
 * Returns a Path that has all but the last segment of this path.
 * If this path has no segments, throws an error.
 */
Path.prototype.parent = function() {
  var segment = this.segment;
  if (!segment) {
    // Also includes the case where we are past the end.
    abort('Empty path can have no parent.');
  }
  var rest = this.rest;
  if (rest.isEnd()) {
    return Path.empty;
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
  var revTail = Toy.asPath(tail).reverse();
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
 * operator.  This does not handle /main.
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
 * Pseudo-constructor: coerces its argument to a Path given a string
 * consisting of segments starting with "/", or an array of strings,
 * or a Bindings, or null.  The parts become the segments of the path.
 * Bindings are reversed, with the first binding ("from" part)
 * becoming the last segment of the path.
 *
 * A null input or no arg given indicates an empty path; passes
 * through a Path argument.
 */
function asPath(arg) {
  if (arg instanceof Path) {
    return arg;
  }
  let segments;
  if (arg == null) {
    segments = [];
  } else if (Array.isArray(arg)) {
    segments = arg;
  } else if (arg instanceof Bindings) {
    // If a Bindings, reverse it into an array and go from there.
    segments = [];
    while (bindings != null) {
      segments.unshift(bindings.from);
    }
  } else if (typeof arg === 'string') {
    segments = arg.split('/');
    assert(segments[0] === '', 'Not a path: {1}', arg);
    // Ignore the first element of the result of the split.
    segments.splice(0, 1);
  } else {
    assert(false, 'Bad arg to asPath: {1}', arg);
  }
  var result = _end;
  while (segments.length) {
    var piece = segments.pop();
    result = new Path(piece, result);
  }
  return result;
}

/**
 * Create a path that contains all the segments of this path followed
 * by all the segments of the path argument.
 */
Path.prototype.concat = function(p) {
  p = Toy.asPath(p);
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
  var result = Toy.asPath('');
  while (!revPath.isEnd()) {
    result = new Path(revPath.segment, result);
    revPath = revPath.tail();
  }
  return result;
};

/**
 * Under the precondition that the given path is equal to an initial
 * portion of this path, returns the tail of this path following the
 * argument path.
 */
Path.prototype.remainder = function(path) {
  let self = this;
  let that = path;
  while (!that.isEnd()) {
    assert(self.segment === that.segment);
    self = self.rest;
    that = that.rest;
  }
  return self;
};

//// Export public names.

Toy.Bindings = Bindings;
Toy.numBindings = numBindings;
Toy.findBinding = findBinding;
Toy.findBindingValue = findBindingValue;
Toy.getBinding = getBinding;

Toy.Path = Path;
Toy.asPath = asPath;

})();
