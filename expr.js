// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('expr', function(Y) {

/**
 * Returns a new expression resulting from substitution of copies of
 * the replacement expression for all free occurrences of the given
 * variable in the target expression.
 */
function subFree(replacement, variable, target) {
  var freeNames = replacement.freeNames();
  return target.subst(replacement, variable, freeNames);
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

/**
 * Find an instance of "from" in the target, and return a copy of the
 * target, with that occurrence replaced by "to".  The "from"
 * expression is a "locator copy" of this, an expression with null
 * values for many of its parts and a "found" property at the point to
 * be replaced.
 *
 * TODO: Remove this.
 */
function replace(from, to, expr, skipN) {
  if (skipN) {
    throw new Error('Unimplemented');
  }
  function likeFrom(x) {
    return x.matches(from) ? x : false;
  }
  var subexpr = expr.search(likeFrom);
  if (!subexpr) {
    throw new Error('Not found!');
  }
  return expr.replace1(subexpr, to);
}


//// Expression, the base class
//
// In the current implementation all occurrences of the same bound
// variable refer to the same Var object, and the implementation of
// subst relies on this, destructively changing bound variable names
// that may class with variables that should be free.  The "rescope"
// method maintains this invariant.
//
// Occurrences of the same free variable however may use different Var
// objects.
//
// TODO: Remove all reliance on use of the same Var for all
// occurrences of a variable.  Remove "same" and "rescope" as not
// needed, and reimplement subst to be nondestructive.

/**
 * Instantiated only for templates.  An instance of this class
 * in a replacement template indicates the place in the larger
 * expression where the replacement is to occur.
 */
function Expr() {
  this.sort = Expr.expr;
}

// The different sorts of expressions:
Expr.expr = 'expr';
Expr.var = 'var';
Expr.call = 'call';
Expr.lambda = 'lambda';

// This counts up to supply a unique name for bound variables renamed
// to avoid capturing.
Expr.counter = 1;

Expr.prototype.toString = function() {
  return '*';
};

/**
 * Finds and returns a Map of the free variables in this expression,
 * from the name to the Var object of that name.
 */
Expr.prototype.freeNames = function() {
  var byName = {};
  this.addFreeNames(byName, null);
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

Expr.prototype.render = function(node) {
  if (!(node instanceof Y.Node)) {
    node = new Y.node(node);
  }
  this.render1(node);
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
//
// subst(Expr replacement, Var variable, Map freeNames)
// 
// Substitutes copies of the replacement expression for all (free)
// occurrences of the given variable in this expression.  As a
// convenience, renames bound variables in this expression to avoid
// using any names that appear in the freeNames map, to make it clear
// to human readers that the occurrences are not captured by any of
// this expression's bound variables.  The current implementation
// destructively alters names of bound variables that clash with names
// of free variables of the replacement, but that could be avoided.
//
//
// copy(Bindings bindings)
//
// Makes and returns a copy of this Expr.  Copies all of its
// subexpressions, and makes one copy of each Var object bound by
// lambda abstraction subexpressions.  The bindings define zero or
// more replacements to be used for references to Var objects found in
// this expression.  A null value indicates zero bindings.
//
//
// addFreeNames(Map result, Bindings bindings)
// 
// Adds names of all free variables that occur in this Expr to the result
// object, with the Var object as the value associated with each name
// found.  Assumes that variables in the Bindings object are bound in this
// expression's lexical context.
//
//
// same(Expr e2, Bindings bindings) <== REMOVE??
//
// Tests whether this expression and e2 are the same except for names
// of bound variables.  Their constants, free variables, and structure
// must match.  If given, the bindings map from variables bound in
// expressions containing this expression to corresponding bound
// variables of the expression containing e2.
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
// rescope(bindings)
//
// Recursively walks through all parts of this expression, changing
// references to variables (Var objects) as needed to match the given
// bindings, plus any other bindings within this expression.  The
// result has all occurrences of all bound variables in this using the
// same Var object.
//
//
// replace1(from, to, bindings)
//
// Replaces the "from" expression with "to" in this expression,
// linking free occurrences of variables in the "to" expression with
// occurrences in this expression so they use the same Var object.
// The bindings object describes variable bindings of expressions
// enclosing this one, and defaults to null for none.  The "from"
// expression must be an actual part of this; copies of it will
// not match.
//
//
// matches(expr, bindings)
//
// Returns true iff this expression matches the structure and names of
// the given expression.  Names free in this expression (though
// potentially bound in enclosing expressions) must match names in the
// given expression, and bound variables must have corresponding bound
// variables in each, though the names may differ.  If bindings are
// given, they connect variables bound in enclosing expressions of
// this and enclosing expressions of the argument, and a variable in
// this matches a variable of the argument iff the argument variable
// is found as the "to" part of a binding for the variable in this.
//
//
// search(test)
//
// Searches for a subexpression of this that passes the given test,
// given as a boolean function of one argument.  Returns the first
// subexpression that passes the test, with this expression itself
// tested first, followed by the rest in top-down, left-to-right
// order.
//
//
// render1(node)
//
// Render this expression at the end of the contents of the given DOM
// node, setting the expression's "node" property to refer to the node
// created to enclose this expression.  Should be done only once to
// any given expression.

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

Var.prototype.subst = function(replacement, variable, freeNames) {
  return (variable == this) ? replacement.copy() : this;
};

// Don't actually copy any variable reference, just return its
// replacement in the bindings or leave it as-is.
Var.prototype.copy = function(bindings) {
  return getBinding(this, bindings) || this;
};

Var.prototype.addFreeNames = function(map, bindings) {
  if (getBinding(this, bindings) == null) {
    map[this.name] = this;
  }
};

Var.prototype.same = function(e2, bindings) {
  var result = this == e2 || getBinding(this, bindings) == e2;
  if (!result) {
    Y.log(this.toString() + ' != ' + e2.toString());
  }
  return result;
};

Var.prototype.normalized = function(counter, bindings) {
  var bindings = getBinding(this, bindings);
  return bindings || this;
};

Var.prototype.rescope = function(bindings) {
  return findByName(this.name, bindings) || this;
};

Var.prototype.replace = function(path, xformer, bindings) {
  return path.isMatch() ? xformer(this).rescope(bindings) : this;
};

Var.prototype.locate1 = function(path) {
  return path.isMatch() ? this : null;
};

Var.prototype.replace1 = function(from, to, bindings) {
  Y.log('var ' + this);
  return from && from.sort == 'expr'
    ? to.rescope(bindings)
    : this;
};

Var.prototype.matches = function(expr, bindings) {
  if (expr instanceof Var) {
    var binding = getBinding(expr, bindings);
    return binding ? expr == binding : this.name == expr.name;
  } else {
    return false;
  }
};

Var.prototype.search = function(pred) {
  return pred(this) ? this : false;
};

Var.prototype.path1 = function(pred, revPath) {
  return pred(this) ? revPath : null;
};

Var.prototype.render1 = function(node) {
  node.append(this.name);
  this.node = node;
};


//// Call -- application of a function to an argument

function Call(fn, arg) {
  this.sort = Expr.call;
  this.fn = fn;
  this.arg = arg;
}
Y.extend(Call, Expr);

Call.prototype.toString = function() {
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    if (this.fn.fn.name.match(/^[^A-Za-z]+$/)) {
      return '(' + this.fn.arg + ' ' + this.fn.fn + ' ' + this.arg + ')';
    } else {
      return '(' + this.fn.fn + ' ' + this.fn.arg + ' ' + this.arg + ')';
    }
  } else {
    return '(' + this.fn + ' ' + this.arg + ')';
  }
};

Call.prototype.dump = function() {
  return '(' + this.fn + ' ' + this.arg + ')';
};

Call.prototype.subst = function(replacement, variable, freeNames) {
  return new Call(this.fn.subst(replacement, variable, freeNames),
                  this.arg.subst(replacement, variable, freeNames));
};

Call.prototype.copy = function(bindings) {
  return new Call(this.fn.copy(bindings), this.arg.copy(bindings));
};

Call.prototype.addFreeNames = function(map, bindings) {
  this.fn.addFreeNames(map, bindings);
  this.arg.addFreeNames(map, bindings);
};

Call.prototype.same = function(e2, bindings) {
  var result;
  if (!(e2 instanceof Call)) {
    result = false;
  } else {
    result = this.fn.same(e2.fn, bindings) && this.arg.same(e2.arg, bindings);
  }
  if (!result) {
    Y.log(this.toString() + ' != ' + e2.toString());
  }
  return result;
};

Call.prototype.normalized = function(counter, bindings) {
  return new Call(this.fn.normalized(counter, bindings),
                  this.arg.normalized(counter, bindings));
};

Call.prototype.rescope = function(bindings) {
  return new Call(this.fn.rescope(bindings), this.arg.rescope(bindings));
};

Call.prototype.replace = function(path, xformer, bindings) {
  if (path.isMatch()) {
    return xformer(this).rescope(bindings);
  } else {
    var fn = this.fn.replace(path.rest('fn'), xformer, bindings);
    var arg = this.arg.replace(path.rest('arg'), xformer, bindings);
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

Call.prototype.replace1 = function(from, to, bindings) {
  Y.log('call ' + this);
  return from && from.sort == 'expr'
    ? to.rescope(bindings)
    : new Call(this.fn.replace1(from && from.fn, to, bindings),
               this.arg.replace1(from && from.arg, to, bindings));
};

Call.prototype.matches = function(expr, bindings) {
  if (expr instanceof Call) {
    return this.fn.matches(expr.fn, bindings)
      && this.arg.matches(expr.arg, bindings);
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

Call.prototype.render1 = function(node) {
  node.append('(');
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    if (this.fn.fn.name.match(/^[^A-Za-z]+$/)) {
      // Non-alphabetic characters: use infix.
      var fnNode = appendSpan(node);
      this.fn.arg.render1(appendSpan(fnNode));
      fnNode.append(space);
      this.fn.fn.render1(appendSpan(fnNode));
      node.append(space);
      this.arg.render1(appendSpan(node));
    } else {
      // Alphabetic characters: function comes first.
      var fnNode = appendSpan(node);
      this.fn.fn.render1(appendSpan(fnNode));
      fnNode.append(space);
      this.fn.arg.render1(appendSpan(fnNode));
      node.append(space);
      this.arg.render1(appendSpan(node));
    }
  } else {
    var opNode = appendSpan(node);
    this.fn.render1(opNode);
    node.append('&nbsp;');
    var argNode = appendSpan(node);
    this.arg.render1(argNode);
  }
  node.append(')');
  this.node = node;
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
  return '{' + this.bound + ' : ' + this.body + '}';
};

Lambda.prototype.dump = function() {
  return '{' + this.bound + ' : ' + this.body + '}';
};

Lambda.prototype.subst = function(replacement, variable, freeNames) {
  // Possibly change the name of the bound variable to make clear
  // to human readers that it is not the same as any free variable
  // of the replacement expression.
  if (freeNames.hasOwnProperty(this.bound.name)) {
    this.bound.name = generateName(this.bound.name);
  }
  return new Lambda(this.bound,
                    this.body.subst(replacement, variable, freeNames));
};

Lambda.prototype.copy = function(bindings) {
  // A copy of a lambda expression has a new bound variable in it.
  var newVar = new Var(this.bound.name);
  var newBindings = new Bindings(this.bound, newVar, bindings);
  return new Lambda(newVar, this.body.copy(newBindings));
};

Lambda.prototype.addFreeNames = function(map, bindings) {
  this.body.addFreeNames(map, new Bindings(this.bound, this.bound, bindings));
};

Lambda.prototype.same = function(e2, bindings) {
  var newBindings = new Bindings(this.bound, e2.bound, bindings);
  var result = (e2 instanceof Lambda) && this.body.same(e2.body, newBindings);
  if (!result) {
    Y.log(this.toString() + ' != ' + e2.toString());
  }
  return result;
};

Lambda.prototype.normalized = function(counter, bindings) {
  var newVar = new Var('$' + counter.next());
  var newBindings = new Bindings(this.bound, newVar, bindings);
  return new Lambda(newVar, this.body.normalized(counter, newBindings));
};

Lambda.prototype.rescope = function(bindings) {
  return lambda(this.bound,
                this.body.rescope(new Bindings(this.bound, null, bindings)));
};

Lambda.prototype.replace = function(path, xformer, bindings) {
  return path.isMatch()
    ? xformer(this).rescope(bindings)
    : new Lambda(this.bound,
                 this.body.replace(path.rest('body'), xformer,
                                   new Bindings(this, null, bindings)));
};

Lambda.prototype.locate1 = function(path) {
  return path.isMatch()
    ? this
    : this.bound.locate1(path.rest('bound'))
        || this.body.locate1(path.rest('body'));
};

Lambda.prototype.replace1 = function(from, to, bindings) {
  Y.log('lambda ' + this.toString());
  return from && from.sort == 'expr'
    ? to.rescope(bindings)
    :  new Lambda(this.bound,
                  this.body.replace1(from && from.body, to,
                                     new Bindings(this, null, bindings)));
};

Lambda.prototype.matches = function(expr, bindings) {
  if (expr instanceof Lambda) {
    var newBindings = new Bindings(this.bound, expr.bound, bindings);
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

Lambda.prototype.render1 = function(node) {
  node.append('{');
  this.bound.render1(appendSpan(node));
  node.append('&nbsp;:&nbsp;');
  this.body.render1(appendSpan(node));
  node.append('}');
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
 * In addFreeNames, bindings contain variables that are bound and thus
 * not free in an expression's lexical context.  In that case the
 * values of the bindings are all null.
 */
function Bindings(from, to, more) {
  this.from = from;
  this.to = to;
  this.more = more;
}

/**
 * Returns the replacement for the variable defined by this
 * Bindings, or null if none is found.
 */
function getBinding(variable, bindings) {
  return bindings == null
    ? null
    : (variable == bindings.from)
    ? bindings.to
    : getBinding(variable, bindings.more);
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
Y.replace = replace;
Y.path = path;

Y.Expr.utils = utils;

}, '0.1', {use: ['node', 'array-extras']});
