// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('expr', function(Y) {

/**
 * Returns a new expression resulting from substitution of copies of
 * the replacement expression for all free occurrences of the given
 * name (or variable) in the target expression.  Used by Axiom 4
 * (lambda conversion).
 */
function subFree(replacement, name, target) {
  if (name instanceof Y.Var) {
    name = name.name;
  }
  var cleanTarget = decapture(target, replacement);
  return cleanTarget.subst(replacement, name);
}

/**
 * Returns the name given if it is not in existingNames.  Otherwise
 * returns a generated name with the same "base" as the one given, and
 * not in existingNames.  The base is the name with any "_N" suffix
 * removed.  The generated suffix will be the lowest-numbered one not
 * yet in use, starting with "_1".
 */
function genName(name, existingNames) {
  var base = name.replace(/_[0-9]+$/, '');
  var candidate = name;
  for (var i = 1; existingNames[candidate]; i++) {
    candidate = base + '_' + i;
  }
  existingNames[candidate] = true;
  return candidate;
}

/**
 * Returns a copy of the target, renaming any bound variables in it
 * that have the same name as a free variable of the replacement to be
 * distinct from all variables appearing in either expression.  After
 * decapturing, straightforward substitution is safe from capturing.
 */
function decapture(target, replacement) {
  var freeNames = replacement.freeNames();
  var allNames = {};
  replacement._addNames(allNames);
  target._addNames(allNames);
  return target._decapture(freeNames, allNames, null);
}

/**
 * Returns an equivalent expression with normalized names for bound
 * variables.
 */
function normalized(expr) {
  return expr.normalized(new Counter(1), null);
}

function appendSpan(node) {
  return node.appendChild('<span class=expr></span>');
}

var space = '&nbsp;';


//// Expression, the base class

/**
 * Instantiated only for templates.  An instance of this class
 * in a replacement template indicates the place in the larger
 * expression where the replacement is to occur.
 */
function Expr() {
  this.sort = Expr.expr;
  // Can also have "node" property for an associated
  // DOM node (refers to a YUI Node).
  // Can have a "_string" property with the result of toString.
  // If inferred, has an "inference" property with the inference
  //   that produced it.
}

// The different sorts of expressions:
Expr.expr = 'expr';
Expr.var = 'var';
Expr.call = 'call';
Expr.lambda = 'lambda';

// This counts up to supply a unique name for bound variables renamed
// to avoid capturing.
Expr.counter = 1;

/**
 * Memoizing version of toString.
 */
Expr.prototype.asString = function() {
  var string = this.toString();
  this._string = string;
  return string;
};

Expr.prototype.toString = function() {
  return '*';
};

/**
 * Finds and returns a Map of the free variables in this expression,
 * from the name to "true".
 */
Expr.prototype.freeNames = function() {
  var byName = {};
  this._addFreeNames(byName, null);
  return byName;
};

Expr.prototype.occurrence = function(expr, nth) {
  function likeFrom(expr) {
    return expr.matches(from) ? expr : false;
  }
  return expr.search(likeFrom);
};

Expr.prototype.isBinOp = function() {
  return this instanceof Call && this.fn instanceof Call;
};

/**
 * Returns the function in a call that has two arguments.
 */
Expr.prototype.getBinOp = function() {
  return this.fn.fn;
};

/**
 * Returns the LHS (left-hand side) of a function of two arguments.
 */
Expr.prototype.getLeft = function() {
  return this.fn.arg;
};

/**
 * Returns the RHS (right-hand side) of a function of two arguments.
 */
Expr.prototype.getRight = function() {
  return this.arg;
};

/**
 * Returns true iff this expression is a call to a function
 * with the given name, with two arguments.
 */
Expr.prototype.isCall2 = function(name) {
  if (this instanceof Y.Call) {
    var left = this.fn;
    return left instanceof Y.Call
      && left.fn instanceof Y.Var
      && left.fn.name == name;
  } else {
    return false;
  }
}

/**
 * Returns a string that identifies this expression.
 */
Expr.prototype.repr = function() {
  // Currently the same as toString.
  return this.toString();
};

/**
 * Public version of "locate", finding a subexpression
 * from its path.
 */
Expr.prototype.locate = function(_path) {
  return this.locate1(path(_path));
};

/**
 * Renders this expression into the given DOM or YUI node,
 * returning a copy of this expression annotated with references
 * from each subexpression into the node where it is presented.
 */
Expr.prototype.render = function(node) {
  if (!(node instanceof Y.Node)) {
    // Coerce from a DOM node to a YUI node.
    node = new Y.node(node);
  }
  var result = this.copy();
  result._render(node);
  return result;
};

/**
 * Searches for a subexpression of this that passes the test, given as
 * a boolean function of one argument.  Returns a path from this to
 * the occurrence, or null if none found.  Tests this expression
 * first, followed by the rest in top-down left-to-right order.
 */
Expr.prototype.pathTo = function(pred) {
  var revPath = this.path1(pred, path('/'));
  if (revPath == null) {
    return null;
  }
  var result = path();
  while (!revPath.isEnd()) {
    result = new Path(revPath.segment, result);
    revPath = revPath.tail();
  }
  return result;
};


// Methods defined on expressions, but defined only in the subclasses:
//
// dump()
//
// Converts expression to a string like toString, but without special
// handling of functions of more than one argument or infix operators.
// 
//
// subst(Expr replacement, String name)
// 
// Substitutes copies of the replacement expression for all (free)
// occurrences of the given name in this expression.  For use in
// logic, this expression must not bind any variables in the
// replacement, at least not at any locations where the given variable
// is free.
//
// TODO: Could we decapture as part of the substitution?
//
//
// copy()
//
// Makes and returns a deep copy of this Expr, not including any
// display-related information.  A null value indicates zero bindings.
//
//
// _addNames(Map result)
//
// Adds all names occurring in this expression to the Map, with value
// of true for each.  Not public.
//
//
// _addFreeNames(Map result, Bindings bindings)
// 
// Adds names of all free variables that occur in this Expr to the
// result object, with the Var object as the value associated with
// each name found.  Assumes that names in the Bindings object are
// bound in this expression's lexical context.  Helper for the
// freeNames method (not public).
//
//
// _decapture(freeNames, allNames, bindings)
//
// Returns a copy of this expression that has no variable bindings
// using any of the names in the freeNames map, and does not use any
// of the names in the allNames map in any of the new bindings.
// Furthermore, the result does not use the same new name within any
// scope using that name, avoiding capturing among new names.
//
// The bindings should map from old variable name to new variable name.
//
// Helper for the decapture function (not public).
//
//
// normalized(counter, bindings)
//
// Returns an equivalent expression with all bound variables
// systematically renamed, so that "normalized" of any expressions that
// differ only by names of bound variables gives the same result.
//
// The current implementation names the bound variables in the
// normalized expression $1, $2, $3, etc. in order of appearance in
// the expression.  As a result, the bound names of normalized
// expressions never clash with free names, such as free names in
// hypotheses.
//
//
// replace(path, xformer)
//
// Returns a copy of this expression.  If some part matches the path,
// that part is replaced by the result of calling the xformer function
// on it.
//
//
// matches(e2, bindings)
//
// Tests whether this expression and e2 are the same except for names
// of bound variables.  Their constants, free variables, and structure
// must match.  The bindings map from names of variables bound in expressions
// containing this expression to corresponding variable names of the
// expression containing e2.
//
//
// search(test)
//
// Searches for a subexpression of this that passes the given test,
// given as a boolean function of one argument.  Returns the first
// subexpression that passes the test, with this expression itself
// tested first, followed by the rest in top-down, left-to-right
// order, or null if there is none.
//
//
// _render(node)
//
// Render this expression at the end of the contents of the given YUI
// node, setting the expression's "node" property to refer to the node
// created to enclose this expression.  Should be done only once to
// any given expression.  Note: a YUI node represents a DOM node.
// Helper for the render method.  (Not public)
// 
// TODO: Consider setting the node property to the actual DOM node.
//
//
// findAll(name, action1, expr2, action2)
//
// Apply the action function to every subexpression in this that is
// a free variable with the given name.  This method also does the
// same traversal of expr2, so it must have expressions at all the
// locations where this does.  Performs action2 on every subexpression
//


//// Var -- variable bindings and references

function Var(name) {
  this.sort = Expr.var;
  this.name = name;
};
Y.extend(Var, Expr);

Var.prototype.toString = function() {
  return this.name;
};

Var.prototype.dump = function() {
  return this.name;
}

Var.prototype.subst = function(replacement, name) {
  return (name == this.name ? replacement.copy() : this);
};

Var.prototype.copy = function() {
  return new Var(this.name);
};

Var.prototype._addNames = function(map) {
  map[this.name] = true;
};

Var.prototype._addFreeNames = function(map, bindings) {
  if (getBinding(this.name, bindings) == null) {
    map[this.name] = true;
  }
};

Var.prototype._decapture = function(freeNames, allNames, bindings) {
  var newName = getBinding(this.name, bindings) || this.name;
  return new Var(newName);
};

Var.prototype.normalized = function(counter, bindings) {
  return new Var(getBinding(this.name, bindings) || this.name);
};

Var.prototype.replace = function(path, xformer) {
  return path.isMatch() ? xformer(this) : this.copy();
};

Var.prototype.locate1 = function(path) {
  return path.isMatch() ? this : null;
};

Var.prototype.matches = function(expr, bindings) {
  if (expr instanceof Var) {
    var expectedName = getBinding(this.name, bindings) || this.name;
    return expr.name == expectedName;
  } else {
    return false;
  }
};

Var.prototype.search = function(pred) {
  return pred(this) ? this : null;
};

Var.prototype.path1 = function(pred, revPath) {
  return pred(this) ? revPath : null;
};

Var.prototype._render = function(node) {
  node.append(this.name);
  this.node = node;
};

Var.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.name == name) {
    action1(this);
    action2(expr2);
  }
};


//// Call -- application of a function to an argument

function Call(fn, arg) {
  this.sort = Expr.call;
  this.fn = fn;
  this.arg = arg;
}
Y.extend(Call, Expr);

Call.prototype.toString = function() {
  if (this._string) {
    return this._string;
  }
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    if (isInfixDesired(this.fn.fn.name)) {
      return '(' + this.fn.arg + ' ' + this.fn.fn + ' ' + this.arg + ')';
    } else {
      return '(' + this.fn.fn + ' ' + this.fn.arg + ' ' + this.arg + ')';
    }
  } else if (this.fn instanceof Var && isInfixDesired(this.fn.name)) {
    return '(' + this.arg + ' ' + this.fn + ')';
  } else {
    return '(' + this.fn + ' ' + this.arg + ')';
  }
};

Call.prototype.dump = function() {
  return '(' + this.fn + ' ' + this.arg + ')';
};

Call.prototype.subst = function(replacement, name) {
  return new Call(this.fn.subst(replacement, name),
                  this.arg.subst(replacement, name));
};

Call.prototype.copy = function() {
  return new Call(this.fn.copy(), this.arg.copy());
};

Call.prototype._addNames = function(map) {
  this.fn._addNames(map);
  this.arg._addNames(map);
};

Call.prototype._addFreeNames = function(map, bindings) {
  this.fn._addFreeNames(map, bindings);
  this.arg._addFreeNames(map, bindings);
};

Call.prototype._decapture = function(freeNames, allNames, bindings) {
  return new Call(this.fn._decapture(freeNames, allNames, bindings),
                  this.arg._decapture(freeNames, allNames, bindings));
};

Call.prototype.normalized = function(counter, bindings) {
  return new Call(this.fn.normalized(counter, bindings),
                  this.arg.normalized(counter, bindings));
};

Call.prototype.replace = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else {
    var fn = this.fn.replace(path.rest('fn'), xformer);
    var arg = this.arg.replace(path.rest('arg'), xformer);
    return new Call(fn, arg);
  }
};

Call.prototype.locate1 = function(path) {
  if (path.isMatch()) {
    return this;
  } else {
    return this.fn.locate1(path.rest('fn'))
      || this.arg.locate1(path.rest('arg'));
  }
};

Call.prototype.matches = function(expr, bindings) {
  if (expr instanceof Call) {
    return (this.fn.matches(expr.fn, bindings)
            && this.arg.matches(expr.arg, bindings));
  } else {
    return false;
  }
};

Call.prototype.search = function(pred) {
  return pred(this)
    ? this
    : this.fn.search(pred) || this.arg.search(pred);
};

Call.prototype.path1 = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.fn.path1(pred, new Path('fn', revPath))
      || this.arg.path1(pred, new Path('arg', revPath));
};

Call.prototype._render = function(node) {
  this.node = node;
  node.append('(');
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    if (isInfixDesired(this.fn.fn.name)) {
      // Non-alphabetic characters: use infix.
      var fnNode = appendSpan(node);
      this.fn.node = fnNode;
      this.fn.arg._render(appendSpan(fnNode));
      fnNode.append(space);
      this.fn.fn._render(appendSpan(fnNode));
      node.append(space);
      this.arg._render(appendSpan(node));
    } else {
      // Alphabetic characters: function comes first.
      var fnNode = appendSpan(node);
      this.fn.node = fnNode;
      this.fn.fn._render(appendSpan(fnNode));
      fnNode.append(space);
      this.fn.arg._render(appendSpan(fnNode));
      node.append(space);
      this.arg._render(appendSpan(node));
    }
  } else if (this.fn instanceof Var && isInfixDesired(this.fn.name)) {
    var argNode = appendSpan(node);
    this.arg._render(argNode);
    node.append('&nbsp;');
    var opNode = appendSpan(node);
    this.fn._render(opNode);
  } else {
    var opNode = appendSpan(node);
    this.fn._render(opNode);
    node.append('&nbsp;');
    var argNode = appendSpan(node);
    this.arg._render(argNode);
  }
  node.append(')');
};

Call.prototype.findAll = function(name, action1, expr2, action2) {
  this.fn.findAll(name, action1, expr2.fn, action2);
  this.arg.findAll(name, action1, expr2.arg, action2);
};


//// Lambda -- variable bindings

/**
 * Make a variable binding from a Var and an Expr.  Any occurrences
 * of the same variable in the body should already be represented
 * by the same Var.
 */
function Lambda(bound, body) {
  this.sort = Expr.lambda;
  this.bound = bound;
  this.body = body;
}
Y.extend(Lambda, Expr);

Lambda.prototype.toString = function() {
  if (this._string) {
    return this._string;
  }
  return '{' + this.bound + ' : ' + this.body + '}';
};

Lambda.prototype.dump = function() {
  return '{' + this.bound + ' : ' + this.body + '}';
};

Lambda.prototype.subst = function(replacement, name) {
  return new Lambda(this.bound,
                    this.body.subst(replacement, name));
};

Lambda.prototype.copy = function() {
  return new Lambda(this.bound.copy(), this.body.copy());
};

Lambda.prototype._addNames = function(map) {
  map[this.bound.name] = true;
  this.body._addNames(map);
};

Lambda.prototype._addFreeNames = function(map, bindings) {
  var name = this.bound.name;
  this.body._addFreeNames(map, new Bindings(name, true, bindings));
};

Lambda.prototype._decapture = function(freeNames, allNames, bindings) {
  var oldName = this.bound.name;
  var newName = freeNames[oldName] ? genName(oldName, allNames) : oldName;
  // Alternatively add a binding only when the new name is different.
  var newBindings = new Bindings(oldName, newName, bindings);
  return new Lambda(new Var(newName),
                    this.body._decapture(freeNames, allNames, newBindings));
};

Lambda.prototype.normalized = function(counter, bindings) {
  var newVar = new Var('$' + counter.next());
  var newBindings = new Bindings(this.bound.name, newVar.name, bindings);
  return new Lambda(newVar, this.body.normalized(counter, newBindings));
};

Lambda.prototype.replace = function(path, xformer) {
  return path.isMatch()
    ? xformer(this)
    : new Lambda(this.bound.copy(),
                 this.body.replace(path.rest('body'), xformer));
};

Lambda.prototype.locate1 = function(path) {
  return path.isMatch()
    ? this
    : this.bound.locate1(path.rest('bound'))
        || this.body.locate1(path.rest('body'));
};

Lambda.prototype.matches = function(expr, bindings) {
  if (expr instanceof Lambda) {
    var newBindings = new Bindings(this.bound.name, expr.bound.name, bindings);
    return this.body.matches(expr.body, newBindings);
  } else {
    return false;
  }
};

Lambda.prototype.search = function(pred) {
  return pred(this) ? this : this.body.search(pred);
};

Lambda.prototype.path1 = function(pred, revPath) {
  return pred(this)
    ? this
    : this.body.path1(pred, new Path('body', revPath));
};

Lambda.prototype._render = function(node) {
  this.node = node;
  node.append('{');
  this.bound._render(appendSpan(node));
  node.append('&nbsp;|&nbsp;');
  this.body._render(appendSpan(node));
  node.append('}');
};

Lambda.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.bound.name != name) {
    this.body.findAll(name, action1, expr2.body, action2);
  }
};


//// Counter -- stateful counter for internal use

/**
 * Mutable counter object.  The default initial value is 1.
 */
function Counter(start) {
  if (start == null) {
    start = 1;
  }
  this.counter = start;
}

/**
 * Returns the next value of the counter and increments it.
 * The first call returns the starting value.
 */
Counter.prototype.next = function() {
  return this.counter++;
};


//// Internal utility functions

/**
 * Names containing "_" are reserved for use by the system.  The current
 * strategy simply uses a counter to uniqueify.
 */
function generateName(name) {
  return name + '_' + Expr.counter++;
}


//// Bindings
////
//// Variable binding contexts and bookkeeping for changing names
//// of bound variables.

/**
 * Binding (for a set of variables).  From is a Var, to is an Expr it
 * is bound to.  "More" refers to another bindings unlless it is null,
 * so this can represent a set of bindings rather than just one.  Used
 * in copying to replace occurrences of variables with replacements.
 *
 * In _addFreeNames, bindings contain variables that are bound and thus
 * not free in an expression's lexical context.  In that case the
 * values of the bindings are all null.
 */
function Bindings(from, to, more) {
  this.from = from;
  this.to = to;
  this.more = more;
}

/**
 * Returns the replacement for the target in the given Bindings, or
 * null if none is found.
 */
function getBinding(target, bindings) {
  return bindings == null
    ? null
    : (target == bindings.from)
    ? bindings.to
    : getBinding(target, bindings.more);
}


//// Path
////
//// Representing parts of expressions -- or other objects!

function Path(segment, rest) {
  this.segment = segment;
  this._rest = rest;
}

// The chain of Path objects goes on forever.
Path.none = new Path(null, null);

// This makes the chain endless.
Path.none._rest = Path.none;

// This marks the end of the path.  Past this is nothing
// interesting.
var _end = new Path(null, Path.none);

/**
 * Traverses into the given object by getting the property named by
 * this Path's segment.  If the value of the property is a function,
 * applies it as a method, e.g. 'getLeft'.
 */
Path.prototype.next = function(o) {
  var steps = {
    fn: function() { return o.fn; },
    arg: function() { return o.arg; },
    body: function() { return o.body; },
    binop: function() { return o.getBinOp(); },
    left: function() { return o.getLeft(); },
    right: function() { return o.getRight(); }
  };
  return steps[this.segment]();
};

Path.prototype.isMatch = function() {
  return this == _end;
};

Path.prototype.isEnd = function() {
  return this == _end;
};

Path.prototype.tail = function() {
  return this._rest;
};

Path.prototype.rest = function(direction) {
  return this.segment == direction ? this._rest : Path.none;
};

/**
 * Empty path displays as '', otherwise "/ segment"
 * for each segment of the path.
 */
Path.prototype.toString = function() {
  if (this == Path.none) {
    return '(none)';
  } else if (this == _end) {
    return '';
  } else {
    var path = this;
    var result = '';
    while (path != _end) {
      var result = result + '/' + path.segment;
      path = path._rest;
    }
    return result
  }
};

/**
 * Pseudo-constructor: returns a Path based on a "/"-separated string
 * or an array of strings.  The parts become the segments of the path.
 * Some segments serve as macros that expand into a list of other
 * segments, currently 'left', 'right', and 'binop'.
 *
 * A null input is treated as '/'.
 */
function path(arg) {
  if (arg instanceof Path) {
    return arg;
  }
  if (arg == null) {
    arg = '/';
  }
  var segments = (typeof arg == 'string')
    ? arg.split('/')
    : arg;
  // Remove the empty first element resulting from an initial "/".
  // Even an empty string splits into an array with one element.
  if (segments[0] == '') {
    segments.splice(0, 1);
  }
  // Handle the result of splitting '/' --> ['', '']:
  if (segments.length == 1 && segments[0] == '') {
    segments = [];
  }
  var macros = {
    left: ['fn', 'arg'],
    right: ['arg'],
    binop: ['fn', 'fn']
  };
  var result = _end;
  while (segments.length) {
    var piece = segments.pop();
    var expansion = macros[piece];
    if (expansion) {
      for (var i = 0; i < expansion.length; i++) {
        segments.push(expansion[i]);
      }
    } else {
      result = new Path(piece, result);
    }
  }
  return result;
}


//// UTILITY FUNCTIONS

/**
 * This controls the policy over which function names are
 * to be rendered as infix.
 */
function isInfixDesired(name) {
  return name.match(/^[^A-Za-z]+$/);
}

/**
 * Asserts that the condition is true, throwing an exception
 * if it is not.  The message may be either a string or
 * a function of no arguments that returns something that
 * can be logged.
 */
function assert(condition, message) {
  if (!condition) {
    if (typeof message == 'function') {
      message = message();
    }
    console.log(message);
    throw new Error(message);
  }
}

/**
 * Asserts that the expression is an equation (must have
 * both left and right sides.
 */
function assertEqn(expr) {
  assert(expr instanceof Y.Call
         && expr.fn instanceof Y.Call
         && expr.fn.fn instanceof Y.Var
         && expr.fn.fn.name == '=',
         'Must be an equation: ' + expr);
}


//// Useful utilities

var utils = {

  /**
   * Finds the first Var in the bindings having the given
   * name, and returns that, or null if it finds none.
   * Uses only the "from" part of each binding.
   */
  findByName: function(name, bindings) {
    if (bindings == null) {
      return null;
    } else if (name == bindings.from.name) {
      return bindings.from;
    } else {
      return findByName(name, bindings.more);
    }
  },

  // Shortcut functions for building expressions.
  expr: function() {
    return new Y.Expr();
  },

  _var: function(name) {
    return new Y.Var(name);
  },

  // This calls a function with any number of arguments.
  call: function(fn, arg) {
    if ((typeof fn) == 'string') {
      fn = new Y.Var(fn);
    }
    if ((typeof arg) == 'string') {
      arg = new Y.Var(arg);
    }
    var result = new Y.Call(fn, arg);
    // Skip fn and the first "arg" after that.
    for (var i = 2; i < arguments.length; i++) {
      result = call(result, arguments[i]);
    }
    return result;
  },

  /**
   * Builds an expression [lhs = rhs] if RHS is present,
   * otherwise just [= lhs].
   */
  equal: function(lhs, rhs) {
    if (rhs) {
      return call('=', lhs, rhs);
    } else {
      return call('=', lhs);
    }
  },

  lambda: function(bound, body) {
    return new Y.Lambda(bound, body);
  },

  x: new Var('x'),
  y: new Var('y'),
  z: new Var('z'),
  f: new Var('f'),
  g: new Var('g'),
  h: new Var('h'),
  p: new Var('p'),
  q: new Var('q'),
  r: new Var('r'),
  T: new Var('T'),
  F: new Var('F'),

  // TODO: Do something other than importing these into
  // the global environment.
  import: function(where) {
    where = where || window;
    // Import the useful names into the window !?
    for (var x in utils) {
      where[x] = utils[x];
    }
  }

};


//// Export public names.

Y.Expr = Expr;
Y.Var = Var;
Y.Call = Call;
Y.Lambda = Lambda;
Y.Path = Path;

Y.subFree = subFree;
Y.normalized = normalized
Y.decapture = decapture;
Y.path = path;
Y.getBinding = getBinding;

Y.assert = assert;
Y.assertEqn = assertEqn;

Y.Expr.utils = utils;

}, '0.1', {use: ['node', 'array-extras']});
