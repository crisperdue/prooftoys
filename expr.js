// Copyright 2011, 2012, 2013 Crispin Perdue.  All rights reserved.

// Initialize the app namespace.
var Toy = Toy || {};

// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

//// GENERAL UTILITIES

/**
 * Configure the given object with the given property descriptors.
 * This is like Object.defineProperties, except key values that are
 * not specifically of type Object are treated as plain values and
 * not made writable, enumerable, or configurable.
 */
function configure(object, properties) {
  var define = Object.defineProperty;
  for (key in properties) {
    var value = properties[key];
    if (typeof value === 'object' && value.constructor === Object) {
      define(object, key, value);
    } else {
      define(object, key, {value: value});
    }
  }
  return object;
}

/**
 * Returns an object with no prototype, having the own properties
 * of the input object as its properties.
 */
function ownProperties(object) {
  // If it has no prototype just return it.
  if (Object.getPrototypeOf(object) === null) {
    return object;
  }
  var result = Object.create(null);
  Object.getOwnPropertyNames(object).forEach(function(name) {
      result[name] = object[name];
    });
  return result;
}

/**
 * Builds and returns an object with no prototype and properties taken
 * from the arguments, an alternating sequence of string keys and
 * values.  The argument list length must be even.
 */
function object0(_args) {
  var result = Object.create(null);
  var nargs = arguments.length;
  if (nargs % 2) {
    throw new Error('object0 bad arguments list');
  }
  for (var i = 0; i < nargs; i += 2) {
    result[arguments[i]] = arguments[i + 1];
  }
  return result;
}

/**
 * Builds and throws a new Error object with the given info.  If the
 * info is a string, it becomes the message, otherwise treats the info
 * as property names and values to assign to the error.
 *
 * The optional type if given is the error constructor, defaulting to
 * Error.
 */
function err(info, type) {
  var error = new (type || Error)();
  if (typeof info == 'string') {
    error.message = info;
  } else {
    jQuery.extend(error, info);
  }
  throw error;
}

/**
 * Calls the given function on each element of the array, passing it
 * the element, the index, and the array.  If on any iteration the
 * function returns any value other than undefined, immediately
 * returns that value, otherwise the value is undefined.  Remembers
 * the array length at the start and uses that value throughout.
 */
function each(array, fn) {
  var len = array.length;
  assert(typeof len === 'number', function() {
      return 'Not an array: ' + array;
    });
  for (var i = 0; i < len; i++) {
    var result = fn(array[i], i, array);
    if (result !== undefined) {
      return result;
    }
  }
}

/**
 * Returns a function that access the value resulting from a call to
 * fn.  On its first call the returned "memo function" calls fn and
 * remembers the value.  Subsequent calls return the remembered value.
 *
 * The result has a property "done" that has the value true iff
 * it has been called at least once.
 */
function memo(fn) {
  var value;
  var memoFn = function() {
    return memoFn.done ? value : (memoFn.done = true, value = fn());
  }
  memoFn.done = false;
  return memoFn;
}

/**
 * Returns a string derived from the format string and the map by
 * replacing occurrences of {<string>} in the format string by the
 * value of that string in the map.
 */
function format(fmt, map) {
  return fmt.replace(/\{.*?\}/g, function(matched) {
      return map[matched.slice(1, -1)];
    });
}

// Map from function name to data (calls and times)
var trackingData = {};

/**
 * Return a function that calls the given one, timing and counting
 * calls on it.  Uses the function's name or the opt_name if given.
 */
function tracked(fn, opt_name) {
  var name = opt_name || fn.name;
  if (typeof fn !== 'function' || !name) {
    throw new Error('Not a named function');
  }
  var data = trackingData[name];
  if (!data) {
    data = trackingData[name] = {calls: 0, times: 0};
  }
  return function() {
    var start = Date.now();
    try {
      return fn.apply(this, arguments);
    } finally {
      data.calls++;
      data.times += Date.now() - start;
    }
  }
}

/**
 * Replace the given property of the given object with a tracked
 * version, reporting using the property name or opt_name if
 * present.
 */
function track(object, property, opt_name) {
  var old = object[property];
  object[property] = tracked(object[property], opt_name || property);
}


//// CLASSES ////

/**
 * Throw one of these to return an arbitrary value
 * from a recursive function.
 */
function Result(value) {
  this.value = value;
}

/**
 * Call the given function with the given arguments, returning the
 * undefined value if the function throws, else the value returned
 * from the function call.
 */
function normalReturn(fn, _args) {
  var result;
  var args = jQuery.makeArray(arguments);
  args.shift();
  try {
    return fn.apply(undefined, args);
  } catch(e) {
    return;
  }
}

/**
 * Call the given function of no arguments.  If it throws a Result
 * object, return its "value".  Rethrow anything else, and return the
 * function value if it does not throw.
 */
function catchResult(fn) {
  try {
    return fn();
  } catch(e) {
    if (e instanceof Result) {
      return e.value;
    } else {
      throw e;
    }
  }
}

function ErrorInfo(message, info) {
  this.message = message;
  this.info = info;
}

/**
 * Specialized error for use when type checking/inference fails.
 */
function TypeCheckError(msg) {
  // Do not call Error because that behaves specially,
  // just fill in a "message" property.
  this.message = msg;
}
Toy.extends(TypeCheckError, Error);

// Stack of active NestedTimers.
_timers = [];

function NestedTimer(name) {
  this.name = name;
  this.elsewhere = 0;
}

NestedTimer.prototype = {

  start: function() {
    _timers.push(this);
    this.elsewhere = Date.now();
  },

  done: function() {
    var now = Date.now();
    assertTrue(this == _timers[_timers.length - 1], 'Timer not nested');
    _timers.pop();
    var elapsed = now - this.elsewhere;
    if (_timers.length) {
      var prev = _timers[_timers.length - 1];
      prev.elsewhere += elapsed;
    }
    console.log(format('Timer {name}: {elapsed}ms',
                       {name: this.name,
                        elapsed: elapsed}));
    return elapsed;
  }
};


// SET

function Set(stringifier) {
  this.map = {};
  this.stringifier = stringifier || String;
}

var emptySet = Object.freeze(new Set());

/**
 * Add an element.
 */
Set.prototype.add = function(value) {
  this.map[this.stringifier(value)] = value;
};

/**
 * Add all the values in the array to this Set.
 * Return this set.
 */
Set.prototype.addAll = function(array) {
  var self = this;
  array.forEach(function(value) { self.add(value); });
  return self;
};

/**
 * Does the set contain the element (one with the same key)?
 */
Set.prototype.has = function(value) {
  return this.map.hasOwnProperty(this.stringifier(value));
};

/**
 * Remove the element.
 */
Set.prototype.remove = function(value) {
  delete this.map[this.stringifier(value)];
};

/**
 * Call the given function for each element of the set, passing the
 * set element as its argument.  Use the optional thisObj as "this"
 * for the calls, or "undefined" if it is not given.  If the function
 * returns any value other than "undefined" that value becomes the
 * return value of this method, and iteration ends.
 */
Set.prototype.each = function(fn, thisObj) {
  var map = this.map
  for (var key in map) {
    var result = fn.call(thisObj, map[key], key);
    if (result !== undefined) {
      return result;
    }
  }
};

/**
 * Count of distinct elements.
 */
Set.prototype.size = function() {
  var counter = 0;
  this.each(function () { counter++; });
  return counter;
};

/**
 * Is the set empty?
 */
Set.prototype.isEmpty = function() {
  for (var key in this.map) {
    return false;
  }
  return true;
};

/**
 * Returns an element of the set or undefined if the set is empty.
 */
Set.prototype.choose = function() {
  for (var key in this.map) {
    return this.map[key];
  }
};


// MAP

/**
 * Arguments are a function to convert a key object to an identifying
 * string, and a default value when getting a key that is not in the
 * map.  The default default is the undefined value.
 */
function Map(stringifier, dfault) {
  this.map = {};
  this.stringifier = stringifier || String;
  this.dfault = dfault;
}

/**
 * Set the value of a map element.
 */
Map.prototype.set = function(key, value) {
  this.map[this.stringifier(key)] = value;
};

/**
 * Does it have an element with matching key?
 */
Map.prototype.has = function(key) {
  return this.map.hasOwnProperty(this.stringifier(key));
};

/**
 * Gets the value at a key or undefined if no such element.
 */
Map.prototype.get = function(key) {
  var map = this.map;
  var k = this.stringifier(key);
  return map.hasOwnProperty(k) ? map[k] : this.dfault;
};

/**
 * Remove any element with matching key.
 */
Map.prototype.remove = function(key) {
  delete this.map[this.stringifier(key)];
};

/**
 * Iterate over the map, allowing early return.  The fn receives a
 * value and (string) key.
 */
Map.prototype.each = function(fn, thisObj) {
  var map = this.map
  for (var key in map) {
    var result = fn.call(thisObj, map[key], key);
    if (result !== undefined) {
      return result;
    }
  }
};

/**
 * Number of distinct keys in the map.
 */
Map.prototype.size = function() {
  var counter = 0;
  this.each(function () { counter++; });
  return counter;
};

/**
 * Is it empty?
 */
Map.prototype.isEmpty = function() {
  for (var key in this.map) {
    return false;
  }
  return true;
};


//// TermSet and TermMap

/**
 * TermSet and TermMap identify terms by their "dump"
 * as a string.
 */
function identifyTerm(term) {
  // TODO: Make this function memoize dumps.
  return term.dump();
};

function TermSet(term) {
  Set.call(this, identifyTerm);
  if (term) {
    this.add(term);
  }
}  
Toy.extends(TermSet, Set);

/**
 * A Map from terms to variables.  Use TermMap.addTerm to set up
 * values, never TermMap.set.  The "subst" field maintains a
 * corresponding substitution from names to terms.
 */
function TermMap() {
  Map.call(this, identifyTerm);
  this.counter = 1;
  this.subst = {};
}
Toy.extends(TermMap, Map);

/**
 * Ensure the term is in this map.  If not already present, assign it
 * a new variable as its value.  In all cases return the map value.
 * Maintains the "subst" field as well.
 */
TermMap.prototype.addTerm = function(term) {
  if (!this.has(term)) {
    var name = 'a' + this.counter++
    this._set(term, new Atom(name));
    this.subst[name] = term;
  }
  return this.get(term);
};

// Make TermMap.set private.
TermMap.prototype._set = Map.prototype.set;

TermMap.prototype.set = function(term, name) {
  throw new Error('Unsupported: TermMap.set', term, name);
};


// Utilities

// Used to order execution of proof steps so they can display
// in order of execution in an automatically-generated proof.
// This increments on every call to "justify".
// Conceptually it could be incremented just by rule R.
var stepCounter = 1;

function getStepCounter() {
  return stepCounter;
}

/**
 * Returns a copy of the target, renaming any bound variables in it
 * that have the same name as a free variable of the replacement.  It
 * makes them distinct from all variables appearing in either
 * expression.  After decapturing, straightforward substitution is
 * safe from capturing.  Unused, also its helper methods.
 */
function decapture(target, replacement) {
  var freeNames = replacement.freeNames();
  var allNames = {};
  replacement._addNames(allNames);
  target._addNames(allNames);
  // Now allNames contains every variable name occurring anywhere in
  // either expression.
  return target._decapture(freeNames, allNames, null);
}


//// Expr -- the base class

// Note on the sourceStep property and structure sharing among proof steps.
//
// Operations that create new hypotheses (currently only
// rules.assume), mark the expression with the step of the proof with
// which it is to be associated in displays.  Inference steps do
// nothing with these properties, but proper functioning of displays
// need them to be present in subsequent steps as hypotheses are
// carried down from one step to the next.
//
// The current solution is that all transformations on expressions that
// leave a given subexpression the same return the identical
// subexpression object they were given.  This means that all
// operations that transform expressions must avoid copying except
// when necessary.  (Rendered copies are not relied on to maintain the
// sourceStep property.)

/**
 * Superclass for terms of all kinds: Atom, Call, Lambda.
 * See internal comments for details.
 */
function Expr() {
  // Extensible set of remembered information, especially useful
  // since the result is conceptually immutable.
  // Duplicated in subclass constructors for speed.
  //
  // TODO: Rendered copies really should share memos with the originals
  // but they don't.
  this.memos = {};
  // If part of a proof, has properties set by the "justify" method.
  // If it has a rendered copy, has "rendering" property.
  //
  // If rendered, has a "node" property for an associated
  // DOM node.
  //
  // If rendered as a proof step, has:
  //   stepNode property with the DOM node of the entire step.
  //   ordinal property with its step number in the rendered proof.
  //   stepNumber property with its rendered step number.
  //
  // The "assume" rule records its step as the sourceStep of the input
  // expression.  Transformation methods on expressions carefully do
  // not copy when not needed, so this property carries down through a
  // proof, which helps to support displaying the source step number
  // when displaying hypotheses.
  //
  // The "assume" rule flags its result as "hasHyps" as well as
  // recording the sourceStep of its input.  The "justify" method
  // recalculates and records "hasHyps" whenever it runs, unless the
  // wff already has a hasHyps flag.  This makes it possible to turn
  // off hypothesis-style display for a specific step in a proof.
  //
  // TODO: Reimplement so hypothesis display is controlled in a
  // rendered step rather than a proof step.
}
Toy.extends(Expr, null);

// This counts up to supply a unique name for bound variables renamed
// to avoid capturing.
Expr.counter = 1;

// Controls prefixing Calls and Lambdas with sourceStep info.
// A debugging and perhaps proof development aid when turned on.
Toy.trackSourceSteps = false;

// Controls generation of Unicode vs. ASCII strings, internal
// to Expr.toString and Expr.toUnicode.
var useUnicode = false;

Expr.prototype.toString = function() {
  if (this instanceof Atom) {
    return this._toString();
  }
  var prefix = '';
  if (Toy.trackSourceSteps) {
    if (this.sourceStep) {
      prefix = '$';
      var stepNum =
        this.sourceStep.rendering && this.sourceStep.rendering.stepNumber;
      if (stepNum) {
        prefix += stepNum;
      }
    }
  }
  if (Toy.trackSourceSteps
      && this.hasHyps
      && this.isCall2('==>')
      && isInfixDesired(this.fn.fn)) {
    var imply = new Atom('|-');
    return (prefix + '(' + this.fn.arg._toString() + ' ' + imply + ' '
            + this.arg._toString() + ')');
  } else {
    return prefix + this._toString();
  }
};

/**
 * Converts this Expr to a Unicode string.  The display is currently
 * just the same as the non-Unicode display except that names (or
 * pnames) that have Unicode counterparts are presented as Unicode.
 */
Expr.prototype.toUnicode = function() {
  useUnicode = true;
  try {
    return this.toString();
  } finally {
    useUnicode = false;
  }
}

/**
 * Returns true iff this term is atomic (a variable or constant).
 */
Expr.prototype.isAtomic = function() {
  return this instanceof Atom;
}

// Categorization of Vars:
//
// Identifiers
//   Variables (start with a single lowercase ASCII letter)
//   Consts (such as sin, cos, forall, exists)
// Literals (numeric, string, etc)
// OpSyntax (+, -, etc)

// All "opSyntax" Vars are operators, plus some designated
// identifers, currently "forall" and "exists".

/**
 * True iff this is a Atom named as a variable.  If the optional
 * name is given, this variable must have the given name.
 */
Expr.prototype.isVariable = function(opt_name) {
  if (!(this instanceof Atom) || !this.name.match(variableRegex)) {
    return false;
  }
  return opt_name ? this.name === opt_name : true;
};

/**
 * True iff this is a var with the given name.
 */
Expr.prototype.hasName = function(name) {
  return this instanceof Atom && this.name === name;
};

/**
 * True iff this is a Atom named as a constant.  If the optional name
 * is given, this constant must have the given name.
 */
Expr.prototype.isConst = function(opt_name) {
  if (!(this instanceof Atom) || !isConstantName(this.name)) {
    return false;
  }
  return opt_name ? this.name === opt_name : true;
};

// True iff the expression is a literal constant.
Expr.prototype.isLiteral = function() {
  return this instanceof Atom && this._value !== undefined;
}

/**
 * True iff the given string is an identifier (named variable or
 * constant).
 */
function isIdentifier(str) {
  return !!str.match(identifierRegex);
}

function isIntegerLiteral(name) {
  return name.match(numeralRegex);
}

/**
 * True iff this is a Atom that displays as an identifier.  This is
 * based on Unicode display, which may be a non-identifier in cases such
 * as "forall" and "exists", even when the internal name is an identifier.
 */
Expr.prototype.displaysIdentifier = function() {
  return (this instanceof Atom &&
          this.toUnicode().match(identifierRegex));
};

/**
 * Is this a numeric literal?
 */
Expr.prototype.isNumeral = function() {
  return this instanceof Atom && typeof this._value == 'number';
};

/**
 * Check that the given value is numeric, raise an error if not,
 * return the value if it is.
 */
Expr.prototype.getNumValue = function() {
  assert(this.isNumeral(), function() {
      return 'Not a numeral: ' + this;
    });
  return this._value;
}

// JavaScript is defined to use IEEE 64-bit floating point in "round
// to nearest" mode.  2**53 is confusable with 2**53 + 1, so this is
// the greatest integer value we "allow".
var MAX_INT = Math.pow(2, 53) - 1;

/**
 * Check that the given number is within the range where integer
 * arithmetic is exact, returning it if so, raising an Error if not.
 */
function checkRange(number) {
  assert(Math.abs(number) <= MAX_INT,
         function() { return 'Number out of range: ' + number; });
  return number;
}

/**
 * Is this a string literal?
 */
Expr.prototype.isString = function() {
  return this instanceof Atom && typeof this._value == 'string';
};

/**
 * Return the string value of a string literal.  Throws if not
 * a string literal.
 */
Expr.prototype.getStringValue = function() {
  assert(this.isString(), function() {
      return 'Not a string literal: ' + this;
    });
  return this._value;
};

/**
 * This is a constant T or F.
 */
Expr.prototype.isBoolConst = function() {
  return (this instanceof Atom &&
          (this.name == 'T' || this.name == 'F'));
};

/**
 * Does this Expr have any variable(s)?
 */
Expr.prototype.hasVars = function() {
  var map = this.freeNames();
  return !isEmpty(map);
};

/**
 * Returns a new expression like this implication, but marked as
 * having hypotheses.  Useful in tests, perhaps other contexts also.
 */
Expr.prototype.asHyps = function() {
  // Note: requires theorems.js to run.
  return Toy.rules.asHypotheses(this);
};

/**
 * Returns true iff this is a call that would display in infix (a Call
 * internally of the form ((op arg1) arg2), where op is a symbol
 * defined to display as infix.
 */
Expr.prototype.isInfixCall = function() {
  return (this instanceof Call
          && this.fn instanceof Call
          && this.fn.fn instanceof Atom
          && isInfixDesired(this.fn.fn));
};

/**
 * Returns a new Atom with a name that does not occur free
 * in this expression.  If a name is given, uses that name
 * as the starting point for the name of the new variable.
 */
Expr.prototype.freshVar = function(name) {
  name = name || 'x';
  return genVar(name, this.freeNames());
};

/**
 * Returns a new expression that "concatenates" this expression with
 * zero or more expressions joined by the named operator.  A null
 * value indicates zero expressions, otherwise the expressions have
 * the form (((e1 op e2) op e3) ... ).
 */
Expr.prototype.concat = function(expr, op) {
  if (!expr) {
    return this;
  }
  if (expr.isCall2(op)) {
    return infixCall(this.concat(expr.getLeft(), op),
                     op, expr.getRight());
  } else {
    return infixCall(this, op, expr);
  }
};

/**
 * Returns a shallow copy of this, annotating the copy with the rule
 * name, rule arguments, hasHyps flag, and dependencies (ruleName,
 * ruleArgs, ruleDeps).  "This" becomes the "details" property if it
 * already has a justification.  (Axioms, definitions and assertions
 * are not generated by rules, though theorems are.)  The ruleArgs and
 * ruleDeps arrays are both optional, empty if not given.
 *
 * If this is identical to one of its ruleDeps, returns this
 * unchanged.  (The purpose is to reduce clutter for readers of the
 * proof.)
 *
 * TODO: Consider making proof steps distinct from Exprs.  That might
 * simplify and/or clarify some code.
 */
Expr.prototype.justify = function(ruleName, ruleArgs, ruleDeps) {
  var ruleDeps = jQuery.makeArray(ruleDeps || []);
  for (var i = 0; i < ruleDeps.length; i++) {
    if (ruleDeps[i] == this) {
      // If the step returns an input step, return it as-is.
      return this;
    }
  }
  var expr = this.dup();
  // Record the original Expr as details.
  if (this.ruleName) {
    expr.details = this;
  }
  // Give the new Expr the specified ruleName.
  expr.ruleName = ruleName;
  // Make the step be its own original, for uniform access to an original.
  expr.original = expr;
  // Give this step its own new ordinal.
  expr.ordinal = stepCounter++;
  // Carry other information forward.
  expr.hasHyps = this.hasHyps;
  expr.ruleArgs = jQuery.makeArray(ruleArgs || []);
  expr.ruleDeps = ruleDeps;
  return expr;
};

Expr.$ = {
           
  /**
   * Applies the named rule to this Expr and any other given arguments
   * as if by a call to Toy.rules[name](args).  Private to Expr.justify.
   */
  apply: function(name, arg1) {
    var nm = name;
    arguments[0] = this;
    return Toy.rules[nm].apply(Toy.rules, arguments);
  },
      
  /**
   * Applies rules.rewriteWithFact to this Expr passing in a path and
   * fact to use.  Private to Expr.justify.
   */
  rewrite: function(path, fact) {
    return Toy.rules.rewriteWithFact(this, path, fact);
  },

  /**
   * Applies rules.replace to this Expr passing in a path and
   * equation to use.  Private to Expr.justify.
   */
  replace: function(path, eqn) {
    return Toy.rules.replace(eqn, this, path);
  }
};

/**
 * Matches the given "schematic" expression against the other
 * expression, returning a subsitution that yields the given
 * expression when given the schema; or null if there is none.
 * Assumes that the schema contains no variable bindings.  The
 * substitution maps from names to expressions.  Tautologies for
 * example qualify as schemas.
 *
 * This is a special case of unification of expressions.
 */
Expr.prototype.matchSchema = function(schema) {
  if (typeof schema == 'string') {
    schema = parse(schema);
  }
  var substitution = {};
  var result = schema._matchAsSchema(this, substitution);
  return result ? substitution : null;
};

/**
 * Returns a truthy value iff this and the given Expr differ only in
 * names of free and/or bound variables.  When true, the value is a
 * substition ("alpha conversion") that maps free variable names in
 * this to Atom objects in the Expr.  Applying the substitution to this
 * Expr results in an Expr that "matches" the Expr argument of this
 * method.
 */
Expr.prototype.alphaMatch = function(expr_arg) {
  var expr = termify(expr_arg);
  var subst = expr.matchSchema(this);
  var result = false;
  if (!subst) {
    return false;
  }
  // Reverse mapping from name in expr to name in this.
  var rsubst = {};
  for (var name in subst) {
    var value = subst[name];
    if (!(value.isVariable())) {
      return false;
    }
    if (rsubst[value.name]) {
      return false;
    }
    rsubst[value.name] = name;
  }
  return subst;
};

/**
 * Alternate name for Expr.matchSchema.  The argument is the schema.
 */
Expr.prototype.findSubst = Expr.prototype.matchSchema;

/**
 * Returns a new expression resulting from substitution of copies of
 * the replacement expression for all free occurrences of the given
 * name (or variable) in this expression.  Used by Axiom 4
 * (lambda conversion).
 *
 * Renames bound variables in the target to prevent them from
 * capturing variables in the replacement.  The strategy is based on
 * the idea that all occurrences of bound variables always remain
 * bound.  Substitution for a bound variable (Axiom 4) never creates a
 * WFF with any variable both free and bound.  Application of Rule R
 * to a target step requires an equation as its other input, so any
 * variables it introduces as free relative to the target scope were
 * free in the input equation.  Thus if a bound variable is given a
 * name different from the name of any other bound variable appearing
 * anywhere at the time, and the name is not reused in the future as a
 * bound variable name, then it can never be made to occur free.
 *
 * Note that Rule R can introduce previously free variables into a
 * scope where they become bound.
 */
Expr.prototype.subFree = function(map_arg) {
  var map = Object.create(null);
  for (var name in map_arg) {
    var replacement = map_arg[name];
    if (replacement instanceof Atom && replacement.name == name) {
      // No changes required.
      continue;
    }
    map[name] = replacement;
  }
  return isEmpty(map) ? this : this._subFree(map);
};

/**
 * Substitutes the replacement for a single name, which can be
 * a string or Atom as done by Expr.subFree.
 */
Expr.prototype.subFree1 = function(replacement, name) {
  return this.subFree(object0(name, replacement));
};

/**
 * For a rendered step, returns a path to the equation RHS if the rule
 * was "consider" or the step hasLeftElision; else the main part if
 * there are hypotheses; else the whole wff.
 */
Expr.prototype.pathToVisiblePart = function() {
  return path(this.rendering &&
              (this.ruleName === 'consider' ||
               this.rendering.hasLeftElision)
              ? '/main/right'
              : (this.hasHyps ? '/main' : ''));
};

var _assertionCounter = 1;

////
//// Methods that properly belong to Exprs that are proof steps
////

/**
 * Modifies the trace information of a proof step to treat it as an
 * assertion, with rule name, args, and deps to match, and no
 * details.  Adds a very small ordinal if there is none already.
 */
Expr.prototype.assert = function() {
  this.ruleName = 'assert';
  this.ruleArgs = [];
  this.ruleDeps = [];
  this.details = null;
  if (!this.ordinal) {
    this.ordinal = _assertionCounter / 1e9;
    _assertionCounter++;
  }
  return this;
};

/**
 * Computes the "base instance" of a proof step.  Each level of
 * justification has its own Expr, all equal, but each with its
 * own justification and details.  This accesses the bottom level
 * step.
 */
Expr.prototype.getBase = function() {
  var result = this;
  while (result.details) {
    result = result.details;
  }
  return result;
};


/**
 * Copies this Expr as a proof step, including the parts specific to
 * proof steps.  Makes only a shallow copy of the step-related parts,
 * also a shallow copy of the wff unless the optional argument is
 * true.  Does not copy any information related to rendering.
 */
Expr.prototype.copyStep = function(deeply) {
  var expr = deeply ? this.copy() : this.dup();
  expr.details = this.details;
  expr.ruleName = this.ruleName;
  // Some elements of ruleArgs may refer to originals of other steps.
  expr.ruleArgs = this.ruleArgs;
  // ruleDeps refers to originals of other steps.
  expr.ruleDeps = this.ruleDeps;
  expr.hasHyps = this.hasHyps;
  return expr;
};


Expr.prototype.addUser = function() {
  this.users++;
  $(this.stepNode).addClass('hasUsers');
  // It would be nice to do this, but in Chrome hover events
  // don't work right with this code.
  // $(this.stepNode).find('.deleteStep').prop('disabled', true);
};

Expr.prototype.removeUser = function() {
  this.users--;
  if (this.users <= 0) {
    $(this.stepNode).removeClass('hasUsers');
    // It would be nice to do this, but in Chrome hover events
    // don't work right with this code.
    // $(this.stepNode).find('.deleteStep').prop('disabled', false);
  }
};

//// End of methods for proof steps

/**
 * Finds and returns a Map of free variable names in this expression,
 * from name to true.
 */
Expr.prototype.freeNames = function() {
  var byName = {};
  this._addFreeNames(byName, null);
  return byName;
};

/**
 * Finds all occurrences of free variables in this expression that are
 * used as inputs to known math operators.  This is a convenience
 * rather than a type analysis.  Returns them as a set (map from name
 * to true).
 */
Expr.prototype.mathVars = function() {
  var map = {}; 
  this._addMathVars(null, map);
  return map;
};

/**
 * Returns a conjunction of conditions that each of the mathVars of
 * this expression is of type R (real), or null if the set of mathVars
 * is empty.
 *
 * If the optional expr is present, uses that as an initial conjunct
 * to add to.
 */
Expr.prototype.mathVarConditions = function(expr) {
  var real = new Atom('R');
  // Order the names for nice presentation.
  var names = [];
  for (var v in this.mathVars()) {
    names.push(v);
  }
  names.sort();
  names.forEach(function(name) {
      if (expr) {
        expr = infixCall(expr, '&', call(real, name));
      } else {
        expr = call(real, name);
      }
    });
  return expr;
};

/**
 * Finds and returns a set of all the names bound in this expression
 * at the location given by the path, represented by a Map from names
 * to true.
 */
Expr.prototype.boundNames = function(path) {
  path = Toy.path(path);
  var bindings = this._boundNames(path, null);
  if (bindings) {
    var map = {};
    for (var more = bindings[0]; more; more = more.more) {
      map[more.from] = true;
    }
    return map;
  } else {
    return {};
  }
};

/**
 * Finds and returns a Map with all names occurring in this expression
 * as the keys, with values of "true".
 */
Expr.prototype.allNames = function() {
  var byName = {};
  this._addNames(byName);
  return byName;
};

/**
 * Returns whether this is a Call with a function part that is also a
 * Call.
 */
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
 * Gets the "main part" of a statement.  If the statement
 * is a conditional gets its conclusion, otherwise the statement
 * itself.
 *
 * TODO: Hopefully rework the system so this gets used in place
 *   of hasHyps and unHyp.
 */
Expr.prototype.getMain = function() {
  return this.isCall2('==>') ? this.getRight() : this;
};

/**
 * Returns the nth "element" of this expression.  Recurs top down
 * through function parts of calls until finding a Atom, which is
 * consider element 0.  The arg part of that call is element 1,
 * and the arg goes up by 1 for each level.  The effect is that a
 * call written as (f a b c) gives the Atom "f" as element 0, "a"
 * as element 1, "b" as element 2, and "c" as element 3.
 */
Expr.prototype.nth = function(n) {
  var result = this._nth(n);
  assert(result instanceof Expr, function() {
      return 'Expr ' + result + ' has no position ' + n;
    });
  return result;
};

/**
 * Returns the RHS of the step if it has hypotheses, otherwise the
 * expression itself.
 */
Expr.prototype.unHyp = function() {
  return this.hasHyps ? this.getRight() : this;
};

/**
 * Returns true iff this expression is a call to a function with the
 * given name, with one argument.  Or if name is not given, a call to
 * any named function.
 */
Expr.prototype.isCall1 = function(name) {
  if (this instanceof Call) {
    return (this.fn instanceof Atom &&
            (name == null || this.fn.name == name));
  } else {
    return false;
  }
};

/**
 * Returns true iff this expression is a call to a function
 * with the given name, with two arguments.  Or if name is not given,
 * a call to any named function.
 */
Expr.prototype.isCall2 = function(name) {
  if (this instanceof Call) {
    var left = this.fn;
    return left instanceof Call
      && left.fn instanceof Atom
      && (name == null || left.fn.name == name);
  } else {
    return false;
  }
};

/**
 * True iff this is a call to a lambda expression.
 */
Expr.prototype.isOpenCall = function() {
  return this instanceof Call && this.fn instanceof Lambda;
};

Expr.$ = {

  /**
   * Is it an equation, possibly with assumptions?
   */
  isEquation: function() {
    return (this.isCall2('=') ||
            (this.isCall2('==>') && this.getRight().isCall2('=')));
  },

  /**
   * Gets the left side of an equation, possibly with assumptions.
   */
  eqnLeft: function() {
    var eqn = this.isCall2('==>') ? this.getRight() : this;
    eqn.assertCall2('=');
    return eqn.getLeft();
  },
  
  /**
   * Gets the right side of an equation, possibly with assumptions.
   */
  eqnRight: function() {
    var eqn = this.isCall2('==>') ? this.getRight() : this;
    eqn.assertCall2('=');
    return eqn.getRight();
  }

};

/**
 * Throw an error with message if this is not a call to a function
 * with the given name.  If no name is given, any named function will
 * do.
 */
Expr.prototype.assertCall1 = function(name) {
  assert(this.isCall1(name), function() {
      return (name === undefined
              ? 'Not a 1-argument call: ' + this
              : 'Not a 1-argument call to ' + name + ': ' + this);
    });
};

/**
 * Throw an error if this is not a binary call to the named operator.
 * If no name is given, any named function will do.
 */
Expr.prototype.assertCall2 = function(name) {
  if (this.isCall2(name)) {
    return;
  }
  var map = {
    '==>': 'a conditional',
    '=': 'an equation',
    '&': 'a conjunction',
    '|': 'a disjunction'
  };
  var message;
  if (name == null) {
    message = 'Not a call to a named 2-argument function';
  } else {
    message = ('Not ' + (map[name] || 'a call to ' + name) + ': ' + this);
  }
  assert(false, message);
};

/**
 * Returns a string that identifies this expression.
 */
Expr.prototype.repr = function() {
  // Currently the same as toString.
  return this.toString();
};

/**
 * Public version of "locate", finding a subexpression
 * from its path.  Handles /main in the path.
 */
Expr.prototype.locate = function(_path) {
  return this._locate(path(_path, this));
};

/**
 * Returns true iff this expression is a proof step.
 */
Expr.prototype.isStep = function() {
  // A property only proof steps have.  Could also use "ordinal", etc..
  return !!this.ruleName;
};

/**
 * Searches for a subexpression of this that passes the test, given as
 * a boolean function of one argument.  Returns a path from this to
 * the occurrence, or null if none found.  Tests this expression
 * first, followed by the rest in top-down left-to-right order.
 * Does not search for variable bindings, use pathToBinding instead.
 * Alternatively accepts a term to be found.
 */
Expr.prototype.pathTo = function(pred) {
  if (pred instanceof Expr) {
    var target = pred;
    pred = function(term) { return target == term; };
  }
  var rpath = this._path(pred, path(''));
  return rpath ? rpath.reverse() : null;
};

/**
 * Like Expr.pathTo, but for infix calls produces a path with /left,
 * /right, or /binop rather than combinations of /fn and /arg.
 */
Expr.prototype.prettyPathTo = function(pred) {
  if (pred instanceof Expr) {
    var target = pred;
    pred = function(term) { return target == term; };
  }
  return this._prettyPath(pred, path(''));
};

/**
 * Searches in this for a variable binding that passes the test, given
 * as a boolean function of one argument.  Returns a path from this to
 * the Lambda containing the occurrence, or null if none found.  Tests
 * this expression first, followed by the rest in top-down
 * left-to-right order.  Alternatively accepts a term to be matched
 * against bound variables in this.
 */
Expr.prototype.pathToBinding = function(pred) {
  if (pred instanceof Expr) {
    var target = pred;
    pred = function(term) { return target.matches(term); };
  }
  var revPath = this._bindingPath(pred, path('/'));
  return revPath ? revPath.reverse() : null;
};

Expr.prototype.traverse = function(rpath) {
  this._traverse(rpath || path());
};

/**
 * True iff this expression is a Call with at least N arguments, where
 * N is at least 1.  Meaning to say this and N - 1 levels of calls
 * nested within its function part.
 */
Expr.prototype.hasArgs = function(n) {
  return (n < 1) ? true : this instanceof Call && this.fn.hasArgs(n - 1);
}

/**		
 * True iff this is a conjunction of expressions that are hypotheses		
 * by having a sourceStep property.		
 */		
Expr.prototype.isHypotheses = function() {
  return (this.sourceStep
          || (this.isCall2('&')
              && this.getLeft().isHypotheses()
              && this.getRight().isHypotheses()));
};

/**
 * Treating this as a chain of hypotheses hk & h(k-1) & ... h1,
 * given an expression that matches one of the hypotheses in the set,
 * builds an expression where "h" is in the position of the matched
 * hypotheses, and the rest are labeled hk ... h1 according to their
 * position from the right.  Helper for rules.extractHypothesis.
 */
Expr.prototype.hypLocater = function(hyp) {
  var h = new Atom('h');
  // Note: positions start with 1 at the right end of the chain.
  function locater(self, pos) {
    if (hyp.matches(self)) {
      return h;
    } else if (self.sourceStep || !self.isCall2('&')) {
      return new Atom('h' + pos);
    } else {
      // Self is a conjunction.
      var right = locater(self.getRight(), pos);
      assert(right instanceof Atom, function() {
          return 'Internal error, not a Atom: ' + right;
        });
      var left = (right == h
                  ? new Atom('h' + (pos + 1))
                  : locater(self.getLeft(), pos + 1));
      return infixCall(left, '&', right);
    }
  }
  return locater(this, 1);
};

/**
 * Treating this as a conjunctive chain of hypotheses, returns an
 * equation with LHS and RHS both chains.  The LHS has 'h' wherever
 * this chain has an element matching toMove, otherwise hk where k is
 * the 1-based index of the chain element in this chain.  The RHS has
 * the same variables in order, but at most one occurrence of 'h' as
 * its last chain element.
 *
 * In other words this generates a equation tautology that works with
 * rules.rewrite to deduplicate matching chain elements and put a
 * single occurrence of the given term at the right end of the chain.
 */
Expr.prototype.hypMover = function(toMove) {
  var i = 1;
  var lhs = null;
  var rhs = null;
  var found = false;
  this.eachHyp(function(term) {
      var h;
      if (term.matches(toMove)) {
        h = new Atom('h');
        found = true;
      } else {
        h = new Atom('h' + i);
        rhs = rhs ? infixCall(rhs, '&', h) : h;
      }
      lhs = lhs ? infixCall(lhs, '&', h) : h;
      i++;
    });
  if (found) {
    rhs = rhs ? infixCall(rhs, '&', new Atom('h')) : new Atom('h');
  }
  return infixCall(lhs, '=', rhs);
};

/**
 * Returns a map from step ordinal to hypothesis for all conjoined
 * hypotheses in this expression.  TODO: Test me.
 */
Expr.prototype.hypsBySource = function() {
  // The hypotheses are the conjuncts at all level that have a
  // sourceStep property.
  var map = {};
  function search(expr) {
    if (expr.sourceStep && expr.sourceStep.ordinal) {
      map[expr.sourceStep.ordinal] = expr;
    } else if (expr.isCall2('&')) {
      search(expr.getLeft());
      search(expr.getRight());
    }
  }
  search(this);
  return map;
};

/**
 * Taking this expression as a chain of hypotheses, applies the given
 * action function to each conjunct in the chain, going from left to
 * right.  Treats the chain as hypotheses, and any element with a
 * sourceStep stops further descent into the chain, regardless whether
 * it is a conjunction itself.
 *
 * If the action returns a truthy value given any hyp, that value
 * immediately becomes the value of the call.  Otherwise returns
 * the value of the last call to the action.
 */
Expr.prototype.eachHyp = function(action) {
  if (this.sourceStep) {
    return action(this);
  } else if (this.isCall2('&')) {
    return (this.getLeft().eachHyp(action) ||
            action(this.getRight()));
  } else {
    return action(this);
  }
};

/**
 * Transforms an expression that is a chain of conjuncts by applying
 * the xform function to each of its conjuncts.  To match eachHyp,
 * Descends into left-hand arguments except any that have a sourceStep
 * property. but does not descend into right-hand arguments of '&'.
 *
 * TODO: Use or remove.
 */
Expr.prototype.transformConjuncts = function(xform) {
  if (this.sourceStep) {
    return xform(this);
  } else if (this.isCall2('&')) {
    return infixCall(this.getLeft().transformConjuncts(xform),
                     '&',
                     xform(this.getRight()));
  } else {
    return xform(this);
  }
};

/**
 * Given an expression that is the conjunction of two chains of
 * hypotheses, returns an equation that is a tautology that can
 * rewrite it to one with the conjunctions merged.
 */
Expr.prototype.mergedHypotheses = function() {
  this.assertCall2('&');
  // Will be a list of all conjuncts in order from left to right.
  var conjuncts = [];
  var i = 1;
  function add(term) {
    conjuncts.push(term);
    if (!term.__var) {
      term.__var = new Atom('a' + i++);
      order = term.sourceStep && term.sourceStep.ordinal;
      if (order) {
        // Make a field of width 13 with leading zeroes.
        // Give it a leading blank to make it sort before items that
        // start with a printing character.
        order = ' ' + ('000000000000' + order).slice(-13);
      } else {
        order = term.dump();
      }
      term.__order = order;
    }
  }
  this.getLeft().eachHyp(add);
  this.getRight().eachHyp(add);

  // Will be a sorted copy of conjuncts.
  function compareTerms(a, b) {
    var a1 = a.__order;
    var b1 = b.__order;
    return a1 < b1 ? -1 : (b1 < a1 ? 1 : 0);
  }
  // A sorted copy of the conjuncts:
  var sorted = conjuncts.concat().sort(compareTerms);
  
  // Remove duplicates from the sorted conjuncts.
  var i = 0;
  while (i < sorted.length - 1) {
    if (sorted[i].matches(sorted[i + 1])) {
      // This makes the pattern show the same thing occurring in two
      // places.
      sorted[i + 1].__var = sorted[i].__var;
      // Note that conjuncts with a sourceStep come before others,
      // with lower ordinals first.  So remove the second matching
      // conjunct.
      sorted.splice(i + 1, 1);
    } else {
      i++;
    }
  }

  // Build the remaining sorted terms into a chain.
  var rhs = null;
  sorted.forEach(function(term) {
      rhs = rhs ? infixCall(rhs, '&', term.__var) : term.__var;
    });

  var left = this.getLeft()._asPattern();
  var right = this.getRight()._asPattern();
  var result = infixCall(infixCall(left, '&', right), '=', rhs);
  conjuncts.forEach(function(term) {
      delete term.__var;
      delete term.__order;
    });
  return result;
};


var _searchTermsOps = ownProperties({'+': true, '-': true, '=': true});

/**
 * Searches this Expr and then any (addition or subtraction)
 * subexpressions recursively, searching for one that passes the
 * test function.  Returns the truthy value from the test, otherwise
 * a falsy value.
 */
Expr.prototype.searchTerms = function(test, path) {
  if (!path) {
    path = Toy.path();
  }
  var op = this.isCall2() && this.getBinOp().name;
  return (test(this, path) ||
          (op && op in _searchTermsOps &&
           (this.getRight().searchTerms(test, new Path('right', path)) ||
            this.getLeft().searchTerms(test, new Path('left', path)))));
};


/**
// Expr
//
// Methods defined on expressions, but defined only in the subclasses:
//
// dump()
//
// Converts expression to a string like toString, but without special
// handling of functions of more than one argument or infix operators.
// A simple text format not dependent on styling options, usable for
// keys in maps with Expr values.
// 
//
// subst(Expr replacement, String name)
// 
// Substitutes copies of the replacement expression for all (free)
// occurrences of the given name in this expression.  For use in
// logic, this expression must not bind any variables that occur free
// in the replacement.
//
//
// _subFree(Object map)
//
// The map argument is an object mapping variable names to replacement
// expressions.  Substitutes the corresponding replacement expression
// for each free occurrence of each name in this Expr.
//
// To ensure no names are captured, also renames bound variables
// throughout this as required so the names are all unique and in the
// namespace reserved for bound variables.  (In this logic a bound
// variable can never become free, though free variables can become
// bound.)
//
//
// copy()
//
// Makes and returns a deep copy of this Expr, copying all parts
// including occurrences of Vars, so rendering can add distinct
// annotations to each occurrence.  Currently copies only logical
// structure and the sourceStep property (to help rendering of
// hypotheses).  Intended only for use in rendering.
//
//
// dup()
//
// Makes and returns a shallow copy of this Expr, with only the properties
// defined by the Atom, Lambda, and Call classes.  The result is not
// flagged as having hypotheses.
//
//
// hasFreeName(name)
// 
// True iff the given variable or constant name (string) appears free
// in this expression.  Does not match against pnames.
//
//
// asArray()
//
// Converts an expression to an array with the function first,
// followed by arguments.  If it is just a variable, returns
// an array containing just that.
//
//
// _addNames(Map result)
//
// Adds all names occurring in this expression to the Map, with value
// of true for each, both free and bound names.
//
//
// _addFreeNames(Map result, Bindings bindings)
// 
// Adds all variable names that occur free in this Expr to the result
// object, with the Atom object as the value associated with each name
// found.  Assumes that names in the Bindings object are bound in this
// expression's lexical context.  Private helper for the freeNames
// method.
//
//
// _decapture(freeNames, allNames, bindings)
//
// Returns a copy of this expression with any bound variables present
// in freeNames renamed to names not present in allNames and distinct
// from each other.  Assumes that the bindings define suitable
// renamings determined by enclosing scope, mapping from old variable
// name to new variable name.
//
// Private helper for the decapture function.
//
// TODO: Only rename bound variables that would actually capture a
// newly-introduced name.  This will help displays of hypotheses.
// 
// TODO: Map in bindings directly to a new variable, reducing object
// creation.
//
//
// _addMathVars(bindings, set)
//
// Helper for Expr.mathVars.  Traverses this expression, adding to the
// set names of all free variables that are arguments to math
// operators or an argument to "=" or "!=" that have an expression
// with a math operator as the other argument.
// 
//
// replaceAt(path, xformer)
//
// Returns a copy of this expression.  If some part matches the path,
// that part is replaced by the result of calling the xformer function
// on it.
//
//
// matches(e2, bindings)
//
// Tests whether all components of this expression and e2 are the same
// except for names of bound variables.  Names of constants and free
// variables must match in each component.  The bindings map from
// names of variables bound in expressions containing this expression
// to corresponding variable names of the expression containing e2.
//
//
// _traverse(fn, rpath)
//
// Applies the function to this expression, then recursively to
// any subexpressions.  Does not descend into the variable binding
// parts of Lambdas.
//
//
// search(test, bindings)
//
// Searches for a subexpression of this that passes the given test,
// given as a boolean function of one argument.  Returns the first
// subexpression that passes the test, with this expression itself
// tested first, followed by the rest in top-down, left-to-right
// order, or null if there is none.  The search includes
// variable bindings if bindings is truthy.
//
//
// _path(pred, revPath)
//
// Searches for a subexpression of this that passes the test and is
// NOT a variable binding.  Returns the "reverse path" to it from
// this, with the last path segment first, added to the given revPath.
// 
// _prettyPath(pred, revPath)
//
// Like _path, but for infix expressions produces /left, /right, etc.
// rather than combinations of /fn and /arg; and returns a forward
// path.
//
// _bindingPath(pred, revPath)
//
// Searches for a subexpression of this that passes the test and is
// the bound variable of a Lambda.  Returns the "reverse path" from
// this to the Lambda, with the last path segment first, followed by
// the given revPath.
// 
//
// generalizeTF(expr2, newVar, bindings)
//
// Searches through this and expr2 for subexpressions in this that are
// the constant T, and F at the same place in expr2.  Returns an
// expression similar to this, but with newVar in those locations.
// Throws an error unless this and expr2 have the same syntax tree
// structure and variable names match everywhere except the T/F cases.
// The newVar should not appear anywhere in this or expr2, to ensure
// that the result will have this and expr2 as substitution instances.
//
// The optional bindings (used in recursive calls) map from names of
// bound variables in expressions containing this, to names of
// corresponding bound variables in expressions containing expr2.
//
// 
// findAll(name, action1, expr2, action2)
//
// Apply the action function to every subexpression in this that is a
// free variable with the given name, and action2 to the
// subexpressions of expr2 at those same locations.  This method also
// does the same traversal of expr2, so it must have expressions at
// all the locations where this does.
//
//
// _matchAsSchema(expr, substitution)
//
// Checks that this expression matches the argument expression under
// the given substitution (map from names to expressions).  Returns
// true iff it does and extends the substitution to a new variable if
// needed to make this and the argument match.  "This" must not
// contain any variable bindings, but the expression can contain
// anything.  Matching here is as defined for the "matches" method.
//
//
// _asPattern()
//
// Descend into this expression returning a term of similar structure
// but with terms having __var property replaced with the value of
// that property.  Helper for code (currently mergedHypotheses) that
// tags subexpressions with __var property as part of creating a
// pattern from them.
//
//
// searchCalls(fn, path)
//
// Tree walks though this Expr and all Calls it contains, recursively,
// calling the function at each Call and passing a reverse path from
// here to that point until the function returns a truthy value.  Does
// not descend into non-Calls.  Returns the first truthy value found
// at any level.
//
*/

//// Atom -- variable bindings and references

//// A Atom object can represent a variable (free or bound) or a
//// constant (see isConstantName).

/**
 * Make a Atom with the given name.  If a non-null integer position is given,
 * use it to record the index in the input stream.  If the given name
 * is in the "aliases" map, the given name becomes the Atom's pname,
 * and the Atom's name becomes the value of the alias.  Pnames affect
 * only parsing and display, not the logic itself.  If the name
 * represents an integer, sets the "value" property to that integer, or
 * if it represents a string, sets the "value" property to the string.
 *
 * CAUTION: This constructor is for internal use by code in this file
 * and implementations of methods on Expr, Atom, Call, and Lambda
 * classes only.  Use factory functions such as varify or constify as
 * the public APIs.
 *
 * TODO: Further reduce use of this too-primitive constructor.
 */
function Atom(name, position) {
  // Expr.call(this);
  this.memos = {};
  this.name = name;
  this.pname = null;
  this._value = undefined;
  this.pos = position;
  if (aliases.hasOwnProperty(name)) {
    this.pname = name;
    this.name = aliases[name];
  } else if (isIntegerLiteral(name)) {
    this._value = parseInt(name);
  } else if (name.charAt(0) === '"') {
    this._value = parseStringContent(name);
  }
};
Toy.extends(Atom, Expr);

/**
 * If not producing Unicode, returns this Atom's pname.  If producing
 * Unicode, and if the pname has a Unicode counterpart, returns that
 * counterpart, otherwise just the pname.
 */
Atom.prototype._toString = function() {
  return (useUnicode
          ? this.toUnicode()
          : this.pname || this.name);
};

/**
 * Implementation of toUnicode for Vars.
 */
Atom.prototype.toUnicode = function() {
  var name = this.pname || this.name;
  var uname = unicodeNames[name];
  if (uname) {
    return uname;
  }
  var info = this.parseName();
  var result = info.name;
  if (info.sub) {
    var offset = 0x2080 - '0'.charCodeAt(0);
    var sub = info.sub;
    for (var i = 0; i < sub.length; i++) {
      result += String.fromCharCode(sub.charCodeAt(i) + offset);
    }
  }
  if (info.type) {
    result += ':' + info.type;
  }
  return result;
};

Atom.prototype.dump = function() {
  return this.name;
};

Atom.prototype._subFree = function(map) {
  // Note that this assumes the map has no prototype.
  return map[this.name] || this;
};

Atom.prototype.copy = function() {
  var result = new Atom(this.pname || this.name);
  result.sourceStep = this.sourceStep;
  return result;
};

Atom.prototype.dup = function() {
  return new Atom(this.pname || this.name);
};

Atom.prototype.hasFreeName = function(name) {
  return this.name == name;
};

Atom.prototype.asArray = function() {
  return [this];
};

Atom.prototype._addNames = function(map) {
  map[this.name] = true;
};

Atom.prototype._addFreeNames = function(map, bindings) {
  if (this.isVariable() && getBinding(this.name, bindings) == null) {
    map[this.name] = true;
  }
};

Atom.prototype._boundNames = function(path, bindings) {
  return path.isMatch() ? [bindings] : false;
};

Atom.prototype._decapture = function(freeNames, allNames, bindings) {
  // This does not account for pnames, but they should only be for constants.
  var newName = getBinding(this.name, bindings);
  return newName ? new Atom(newName) : this;
};

Atom.prototype._addMathVars = function(bindings, set) {
  return false;
};

Atom.prototype.replaceAt = function(path, xformer) {
  return path.isMatch() ? xformer(this) : this;
};

Atom.prototype._locate = function(path) {
  return path.isMatch() ? this : null;
};

Atom.prototype.matches = function(expr, bindings) {
  if (expr == this) {
    return true;
  }
  if (expr instanceof Atom) {
    var expectedName = getBinding(this.name, bindings) || this.name;
    return expr.name == expectedName;
  } else {
    return false;
  }
};

Atom.prototype._traverse = function(fn, rpath) {
  fn(this, rpath);
};

Atom.prototype.search = function(pred, bindings) {
  var result = pred(this) ? this : null;
  return result;
};

Atom.prototype.generalizeTF = function(expr2, newVar, bindings) {
  if (!(expr2 instanceof Atom)) {
    throw new Error('Not a variable: ' + expr2);
  }
  var name1 = this.name;
  var name2 = expr2.name;
  if (name1 === 'T' && name2 === 'F') {
    return newVar;
  } else if (name1 === name2) {
    return this;
  } else if (getBinding(name1, bindings)) {
    return this;
  } else {
    throw new Error('Mismatched names: ' + name1 + ', ' + name2);
  }
};

Atom.prototype._path = function(pred, revPath) {
  return pred(this) ? revPath : null;
};

Atom.prototype._prettyPath = function(pred, revPath) {
  return pred(this) ? revPath : null;
};

Atom.prototype._bindingPath = function(pred, revPath) {
  return null;
};

Atom.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.name == name) {
    action1(this);
    action2(expr2);
  }
};

Atom.prototype._matchAsSchema = function(expr, map) {
  // This method does not return true when matching a defined name with an
  // expression that matches its definition.  It is a stricter criterion than
  // would be treating definitions exactly as abbreviations.
  if (this.isConst()) {
    // Expr must be a Atom with the same name.
    return this.matches(expr);
  }
  // Only a true variable can match an expression that is not identical to it.
  var binding = map[this.name];
  if (binding) {
    return expr.matches(binding);
  } else {
    map[this.name] = expr;
    return true;
  }
};

Atom.prototype._asPattern = function(term) {
  return this.__var || this;
};

Atom.prototype.searchCalls = function(fn, path) {};


//// Call -- application of a function to an argument

function Call(fn, arg) {
  // Expr.call(this);
  this.memos = {};
  this.fn = fn;
  this.arg = arg;
}
Toy.extends(Call, Expr);

Call.prototype._toString = function() {
  if (this._string) {
    return this._string;
  }
  function asArg(expr) {
    if (expr instanceof Atom && isInfixDesired(expr)) {
      return '(' + expr + ')';
    } else {
      return expr.toString();
    }
  }
  if (this.fn instanceof Call && this.fn.fn instanceof Atom) {
    if (isInfixDesired(this.fn.fn)) {
      return '(' + this.fn.arg + ' ' + this.fn.fn + ' ' + this.arg + ')';
    } else {
      return '(' + this.fn.fn + ' ' + asArg(this.fn.arg) + ' ' + this.arg + ')';
    }
  } else if (this.fn instanceof Atom && isInfixDesired(this.fn)) {
    return '(' + this.arg + ' ' + this.fn + ')';
  } else {
    return '(' + this.fn + ' ' + asArg(this.arg) + ')';
  }
};

Call.prototype.dump = function() {
  return '(' + this.fn.dump() + ' ' + this.arg.dump() + ')';
};

Call.prototype._subFree = function(map) {
  var fn = this.fn._subFree(map);
  var arg = this.arg._subFree(map);
  return (fn == this.fn && arg == this.arg) ? this : new Call(fn, arg);
};

Call.prototype.copy = function() {
  var result = new Call(this.fn.copy(), this.arg.copy());
  result.sourceStep = this.sourceStep;
  return result;
};

Call.prototype.dup = function() {
  return new Call(this.fn, this.arg);
};

Call.prototype.hasFreeName = function(name) {
  return this.fn.hasFreeName(name) || this.arg.hasFreeName(name);
};

Call.prototype.asArray = function() {
  var result = this.fn.asArray();
  result.push(this.arg);
  return result;
};

Call.prototype._addNames = function(map) {
  this.fn._addNames(map);
  this.arg._addNames(map);
};

Call.prototype._addFreeNames = function(map, bindings) {
  this.fn._addFreeNames(map, bindings);
  this.arg._addFreeNames(map, bindings);
};

Call.prototype._boundNames = function(path, bindings) {
  if (path.isMatch()) {
    return [bindings];
  } else {
    var segment = path.segment;
    var rest = path._rest;
    if (this.fn instanceof Call) {
      if (segment === 'left') {
        return this.getLeft()._boundNames(rest, bindings);
      } else if (segment === 'binop') {
        return this.getBinOp()._boundNames(rest, bindings);
      } else if (segment === 'right') {
        return this.getRight()._boundNames(rest, bindings);
      }
    }
    if (segment === 'fn') {
      return this.fn._boundNames(rest, bindings);
    } else if (segment === 'arg') {
      return this.arg._boundNames(rest, bindings);
    }
    throw new Error('Path segment "' + segment +
                    '" does not match Call: ' + this);
  }
};

Call.prototype._decapture = function(freeNames, allNames, bindings) {
  var fn = this.fn._decapture(freeNames, allNames, bindings);
  var arg = this.arg._decapture(freeNames, allNames, bindings);
  return (fn == this.fn && arg == this.arg ? this : new Call(fn, arg));
};

Call.prototype._addMathVars = function(bindings, set) {
  // TODO: Consider handling defined functions.
  function isFreeVar(v) {
    return v.isVariable() && !findBinding(v.name, bindings);
  }
  if (this.isCall1()) {
    // Function "R" does not need to mark its argument as a math variable.
    var op = this.fn.name;
    var result = false;
    switch (op) {
    case 'neg':
    case 'recip':
      if (isFreeVar(this.arg)) {
        set[this.arg.name] = true;
      }
      result = true;
    }
    this.arg._addMathVars(bindings, set);
    return result;
  } else if (this.isCall2()) {
    var op = this.getBinOp().name;
    var left = this.getLeft();
    var right = this.getRight();
    function addVars() {
      if (isFreeVar(left)) {
        set[left.name] = true;
      }
      if (isFreeVar(right)) {
        set[right.name] = true;
      }
    }
    var result = false;
    switch (op) {
    case '+':
    case '-':
    case '*':
    case '/':
      addVars();
      result = true;
      break;
    case '<':
    case '<=':
    case '>':
    case '>=':
      addVars();
      break;
    }
    var isLeftReal = left._addMathVars(bindings, set);
    if (isLeftReal && isFreeVar(right)) {
      set[right.name] = true;
    }
    var isRightReal = right._addMathVars(bindings, set);
    if (isRightReal && isFreeVar(left)) {
      set[left.name] = true;
    }
    return result;
  } else {
    this.fn._addMathVars(bindings, set);
    this.arg._addMathVars(bindings, set);
    return false;
  }
};

Call.prototype.replaceAt = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else {
    var segment = path.segment;
    if (this.fn instanceof Call) {
      if (segment === 'left') {
        return infixCall(this.getLeft().replaceAt(path._rest, xformer),
                         this.getBinOp(),
                         this.getRight());
      } else if (segment === 'binop') {
        return infixCall(this.getLeft(),
                         this.getBinOp().replaceAt(path._rest, xformer),
                         this.getRight());
      } else if (segment === 'right') {
        return infixCall(this.getLeft(),
                         this.getBinOp(),
                         this.getRight().replaceAt(path._rest, xformer));
      }
    }
    if (segment === 'fn') {
      return new Call(this.fn.replaceAt(path._rest, xformer), this.arg);
    } else if (segment === 'arg') {
      return new Call(this.fn, this.arg.replaceAt(path._rest, xformer));
    }
    throw new Error('Path segment ' + segment +
                    ' does not match Call: ' + this);
  }
};

Call.prototype._locate = function(path) {
  if (path.isMatch()) {
    return this;
  } else {
    var segment = path.segment;
    var rest = path._rest;
    if (this.fn instanceof Call) {
      if (segment === 'left') {
        return this.getLeft()._locate(rest);
      } else if (segment === 'binop') {
        return this.getBinOp()._locate(rest);
      } else if (segment === 'right') {
        return this.getRight()._locate(rest);
      }
    }
    if (segment === 'fn') {
      return this.fn._locate(rest);
    } else if (segment === 'arg') {
      return this.arg._locate(rest);
    }
    throw new Error('Path segment "' + segment +
                    '" does not match Call: ' + this);
  }
};

Call.prototype.matches = function(expr, bindings) {
  if (expr == this) {
    return true;
  }
  if (expr instanceof Call) {
    return (this.fn.matches(expr.fn, bindings)
            && this.arg.matches(expr.arg, bindings));
  } else {
    return false;
  }
};

Call.prototype._traverse = function(fn, rpath) {
  fn(this, rpath);
  this.arg._traverse(fn, new Path('arg', rpath));
  this.fn._traverse(fn, new Path('fn', rpath));
};

Call.prototype.search = function(pred, bindings) {
  var result = pred(this)
    ? this
    : this.fn.search(pred, bindings) || this.arg.search(pred, bindings);
  return result;
};

Call.prototype.generalizeTF = function(expr2, newVar, bindings) {
  if (!(expr2 instanceof Call)) {
    throw new Error('Not a Call: ' + expr2);
  }
  var fn = this.fn.generalizeTF(expr2.fn, newVar, bindings);
  var arg = this.arg.generalizeTF(expr2.arg, newVar, bindings);
  return (fn == this.fn && arg == this.arg) ? this : new Call(fn, arg);
};

Call.prototype._path = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.fn._path(pred, new Path('fn', revPath))
      || this.arg._path(pred, new Path('arg', revPath));
};

Call.prototype._prettyPath = function(pred, revPath) {
  var p;
  if (pred(this)) {
    return revPath;
  } else if (this.isInfixCall()) {
    p = this.getLeft()._prettyPath(pred, revPath);
    if (p) {
      return new Path('left', p);
    }
    p = this.getBinOp()._prettyPath(pred, revPath)
    if (p) {
      return new Path('binop', p);
    }
    p = this.getRight()._prettyPath(pred, revPath);
    if (p) {
      return new Path('right', p);
    } else {
      return null;
    }
  } else {
    p = this.fn._prettyPath(pred, revPath);
    if (p) {
      return new Path('fn', p);
    }
    p = this.arg._prettyPath(pred, revPath);
    if (p) {
      return new Path('arg', p);
    }
    return null;
  }
};

Call.prototype._bindingPath = function(pred, revPath) {
  return (this.fn._bindingPath(pred, new Path('fn', revPath))
          || this.arg._bindingPath(pred, new Path('arg', revPath)));
};

Call.prototype.findAll = function(name, action1, expr2, action2) {
  this.fn.findAll(name, action1, expr2.fn, action2);
  this.arg.findAll(name, action1, expr2.arg, action2);
};

Call.prototype._matchAsSchema = function(expr, map) {
  return (expr instanceof Call
          && this.fn._matchAsSchema(expr.fn, map)
          && this.arg._matchAsSchema(expr.arg, map));
};

Call.prototype._asPattern = function(term) {
  return this.__var || new Call(this.fn._asPattern(), this.arg._asPattern());
};

Call.prototype.searchCalls = function(fn, path) {
  if (!path) {
    path = Toy.path();
  }
  return (fn(this, path) ||
          // Try the arg first to help substitutions apply toward the
          // right sides of formulas.
          this.arg.searchCalls(fn, new Path('arg', path)) ||
          this.fn.searchCalls(fn, new Path('fn', path)));
};


//// Lambda -- variable bindings

/**
 * Make a variable binding from a Atom and an Expr.  Any occurrences
 * of the same variable in the body should already be represented
 * by the same Atom.
 */
function Lambda(bound, body) {
  // Expr.call(this);
  this.memos = {};
  this.bound = bound;
  this.body = body;
}
Toy.extends(Lambda, Expr);

Lambda.prototype._toString = function() {
  if (this._string) {
    return this._string;
  }
  return '{' + this.bound + '. ' + this.body + '}';
};

Lambda.prototype.dump = function() {
  return '{' + this.bound.dump() + '. ' + this.body.dump() + '}';
};

Lambda.prototype._subFree = function(map) {
  var boundName = this.bound.name;
  if (boundName === name) {
    // Binds the name; there can be no free occurrences here.
    return this;
  } else if (this.bound.isGeneratedBound()) {
    // By contract of subFree, the replacement will have no free
    // occurrences of the bound name, so this will capture no
    // variables.
    var body = this.body._subFree(map);
    return (body === this.body) ? this : new Lambda(this.bound, body);
  } else {
    // The bound variable is not uniquely named.  Rename it and try
    // the same substitution on the resulting lambda.  This is the key
    // to preventing improper "capturing" substitution in this
    // algorithm.
    var newVar = _genBoundVar(boundName);
    var renamed =
      lambda(newVar, this.body._subFree(object0(boundName, newVar)));
    return renamed._subFree(map);
  }
};

// Etc.

Lambda.prototype.copy = function() {
  var result = lambda(this.bound.copy(), this.body.copy());
  result.sourceStep = this.sourceStep;
  return result;
};

Lambda.prototype.dup = function() {
  return new Lambda(this.bound, this.body);
};

Lambda.prototype.hasFreeName = function(name) {
  return this.bound.name != name && this.body.hasFreeName(name);
};

Lambda.prototype.asArray = function() {
  return [this];
};

Lambda.prototype._addNames = function(map) {
  map[this.bound.name] = true;
  this.body._addNames(map);
};

Lambda.prototype._addFreeNames = function(map, bindings) {
  var name = this.bound.name;
  this.body._addFreeNames(map, new Bindings(name, true, bindings));
};

Lambda.prototype._boundNames = function(path, bindings) {
  if (path.isMatch()) {
    return [bindings];
  } else {
    var newBindings = new Bindings(this.bound.name, bindings);
    return (this.bound._boundNames(path.rest('bound'), newBindings)
            || this.body._boundNames(path.rest('body'), newBindings));
  }
};

Lambda.prototype._decapture = function(freeNames, allNames, bindings) {
  // TODO: Share Vars more for efficiency.
  var oldName = this.bound.name;
  var newName = freeNames[oldName] ? genName(oldName, allNames) : oldName;
  // Add a binding only when the new name is different.
  var newBindings = ((newName == oldName)
                     ? bindings
                     : new Bindings(oldName, newName, bindings));
  var body = this.body._decapture(freeNames, allNames, newBindings);
  return (body == this.body) ? this : new Lambda(new Atom(newName), body);
};

Lambda.prototype._addMathVars = function(bindings, set) {
  this.body._addMathVars(new Bindings(this.bound.name, true, bindings), set);
  return false;
};

Lambda.prototype.replaceAt = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else {
    var body = this.body.replaceAt(path.rest('body'), xformer);
    return (body == this.body) ? this : lambda(this.bound, body);
  }
};

Lambda.prototype._locate = function(path) {
  return path.isMatch()
    ? this
    : this.bound._locate(path.rest('bound'))
        || this.body._locate(path.rest('body'));
};

Lambda.prototype.matches = function(expr, bindings) {
  if (expr == this) {
    return true;
  }
  if (expr instanceof Lambda) {
    var newBindings = new Bindings(this.bound.name, expr.bound.name, bindings);
    return this.body.matches(expr.body, newBindings);
  } else {
    return false;
  }
};

Lambda.prototype._traverse = function(fn, rpath) {
  fn(this, rpath);
  this.body._traverse(fn, new Path('body', rpath));
};

Lambda.prototype.search = function(pred, bindings) {
  var result = pred(this)
    ? this
    : ((bindings && this.bound.search(pred, bindings))
       || this.body.search(pred, bindings));
  return result;
};

Lambda.prototype.generalizeTF = function(expr2, newVar, bindings) {
  if (!(expr2 instanceof Lambda)) {
    throw new Error('Not a variable binding: ' + expr2);
  }
  var newBindings = new Bindings(this.bound, expr2.bound, bindings)
  var body = this.body.generalizeTF(expr2.body, newVar, newBindings);
  return (body == this.body) ? this : lambda(this.bound, body);
};

Lambda.prototype._path = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.body._path(pred, new Path('body', revPath));
};

Lambda.prototype._prettyPath = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.body._prettyPath(pred, new Path('body', revPath));
};

Lambda.prototype._bindingPath = function(pred, revPath) {
  return (pred(this.bound)
          ? revPath
          : this.body._bindingPath(pred, new Path('body', revPath)));
};

Lambda.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.bound.name != name) {
    this.body.findAll(name, action1, expr2.body, action2);
  }
};

Lambda.prototype._matchAsSchema = function(expr, map) {
  throw new Error('Schema expression cannot contain variable bindings.');
};

Lambda.prototype._asPattern = function(term) {
  return this.__var || lambda(this.bound, this.body._asPattern());
};

Lambda.prototype.searchCalls = function(fn, path) {};

// Private methods grouped by name.

/**
 * Returns the term found inside here, or if not found, the first
 * index not seen.
 */
Atom.prototype._nth = function(n) {
  return n == 0 ? this : 1;
};

Call.prototype._nth = function(n) {
  var here = this.fn._nth(n);
  if (here instanceof Expr) {
    return here;
  } else if (n == here) {
    return this.arg;
  } else {
    return here + 1;
  }
};

Lambda.prototype._nth = function(n) {
  assert(false, 'Nth not relevant in lambdas');
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
 * Returns the replacement for the target in the given Bindings, or
 * null if none is found.
 */
function getBinding(target, bindings) {
  var found = findBinding(target, bindings);
  return found ? found.to : null;
}


//// Path
////
//// Representing parts of expressions.

// TODO: Consider defining distinct subclases for forward and reverse
//   paths.

/**
 * Construct a Path from a segment string (fn, arg, bound, body, left,
 * right, or binop) and an optional Path, which defaults to an empty
 * path.  Thus if "rest" is null the result is a path with a single
 * segment.
 */
function Path(segment, rest) {
  this.segment = segment;
  this._rest = rest || _end;;
}

// The chain of Path objects goes on forever.
Path.none = new Path(null, null);

// This makes the chain endless.
Path.none._rest = Path.none;

// This marks the end of the path.  Past this is nothing
// interesting.
var _end = new Path(null, Path.none);

// Private to the "next" method.
var _pathSteps = {
  fn: function(o) { return o.fn; },
  arg: function(o) { return o.arg; },
  body: function(o) { return o.body; },
  binop: function(o) { return o.getBinOp(); },
  left: function(o) { return o.getLeft(); },
  right: function(o) { return o.getRight(); }
};

/**
 * Traverses into the given object by getting the property named by
 * this Path's segment.  If the value of the property is a function,
 * applies it as a method, e.g. 'getLeft'.
 */
Path.prototype.next = function(o) {
  return _pathSteps[this.segment](o);
};

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
              && this._rest
              && this._rest.segment =='arg'));
};

Path.prototype.getLeft = function() {
  assert(this.isLeft(), 'Not a leftward path');
  // TODO: Change this when changing the meaning of infix.
  return this._rest._rest;
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
  assert(this.isRight(), 'Not a rightward path');
  // TODO: Change this when changing the meaning of infix.
  return this._rest;
};

Path.prototype.tail = function() {
  return this._rest;
};

Path.prototype.rest = function(direction) {
  return this.segment === direction ? this._rest : Path.none;
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
      path = path._rest;
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
 * to whether the expr has hypotheses or not.
 *
 * A null input indicates an empty path.
 */
function path(arg, opt_expr) {
  var expr = opt_expr;

  // If the initial segment of the path is 'main', and the expression
  // is given and has hypotheses, return a path to its RHS.
  function adjust(path) {
    if (expr && path.segment == 'main') {
      path = path._rest;
      if (expr.hasHyps) {
        path = new Path('right', path);
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
  // Handle the result of splitting '/' ==> ['', '']:
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
    return new Path(this.segment, this._rest.concat(p));
  }
};

/**
 * For a forward path, expands left, right, and binop segments into
 * their primitive fn and arg components.
 */
Path.prototype.expand = function() {
  function xpand(segment, tail) {
    var xrest = tail.isEnd() ? tail : xpand(tail.segment, tail._rest);
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
          : xpand(this.segment, this._rest));
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


//// TYPE ANALYSIS

// Private to the TypeVariable constructor.
var _typeVarCounter = 1;

/**
 * Type variable constructor.  The name is optional, 't' followed by
 * digits if not given explicitly.  Names are currently required to
 * begin with 't' when parsed.
 */
function TypeVariable(name) {
  this.instance = null;
  if (name) {
    this.name = name;
  } else {
    this.name = 't' + _typeVarCounter++;
  }
}

TypeVariable.prototype.toString = function() {
  return this.instance ? this.instance.toString() : this.name;
}

/**
 * The resulting type expression has the same structure as the
 * input, but all occurrences of each "generic" type variable are
 * replaced with occurrences of a "fresh" type variable distinct
 * from all others.
 *
 * Note: with only top-level definitions, generic type variables are
 * exactly those in the types of defined constants, but definitions
 * in inner scopes can have mixed generic and non-generic type
 * variables.
 */
TypeVariable.prototype.fresh = function(mappings, nonGenerics) {
  var type = dereference(this);
  var name = type.name;
  if (!occursInList(name, nonGenerics)) {
    if (!mappings.hasOwnProperty(name)) {
      mappings[name] = new TypeVariable();
    }
    return mappings[name];
  } else {
    return type;
  }
};

/**
 * Type constant constructor.
 */
function TypeConstant(name) {
  this.name = name;
}
Toy.extends(TypeConstant, null);

TypeConstant.$ = {
  toString: function() {
    return this.name;
  },

  fresh: function(mapping, nonGenerics) {
    return this;
  }
};

/**
 * TypeOperator constructor, types is an optional array of type
 * parameters, if not given, then an empty array.
 */
function TypeOperator(name, types) {
  this.name = name;
  this.types = types || [];
}
Toy.extends(TypeOperator, null);

TypeOperator.prototype.toString = function() {
  var numTypes = this.types.length;
  return numTypes == 0
    ? this.name
    : numTypes == 2
    ? '(' + [this.types[0], this.name, this.types[1]].join(' ') + ')'
    : '(' + this.name + ' ' + this.types.join(' ') + ')';
};

TypeOperator.prototype.fresh = function(mappings, nonGenerics) {
  var ptypes = this.types;
  var freshTypes = [];
  for (var i = 0; i < ptypes.length; i++) {
    freshTypes.push(ptypes[i].fresh(mappings, nonGenerics));
  }
  return new TypeOperator(this.name, freshTypes);
};


function FunctionType(fromType, toType) {
  TypeOperator.call(this, '->', [fromType, toType]);
  this.types = [fromType, toType];
}
Toy.extends(FunctionType, TypeOperator);

FunctionType.prototype.toString = function() {
  return '(' + this.types[1] + ' ' + this.types[0] + ')';
};

FunctionType.prototype.fresh = function(mappings, nonGenerics) {
  return new FunctionType(this.types[0].fresh(mappings, nonGenerics),
                          this.types[1].fresh(mappings, nonGenerics));
};

var individual = new TypeConstant('i');
var boolean = new TypeConstant('o');
// TODO: Change this to a proper type of its own.
var realType = individual;

/**
 * Returns true iff the type of the term is Real.  Until integrating
 * findType further into the parser, treat variable names beginning
 * with t-z as real.
 */
Expr.prototype.isReal = function() {
  if (this._type) {
    return this.getType() == realType;
  } else {
    // TODO: Implement similar functionality in the parser, presumably
    //   before loosening the conditions on various laws of real numbers.
    return (type instanceof Toy.TypeVariable &&
            this instanceof Toy.Atom &&
            this.name.match(/^[t-z]/) &&
            this.isVariable());
  }
};

/**
 * Parse a type string, returning a TypeOperator (type expression).
 * Input can only be parenthesized sequences of "i", "o", a single
 * upper case letter, or "t" followed by digits, with space as the
 * separater.
 */
function parseType(input) {
  var pattern = /[()io]/g;
  // Tokens -- or whitespace -- or illegal stuff.
  var tokens = /[()]|i|o|[A-Z]|t[0-9]+|( +)|([^ ()iotA-Z]+)/g;
  var end = {name: '(end)', index: input.length};
  // Returns a list of tokens as objects with properties 'name' and 'index'.
  function tokenize(term) {
    var match;
    var result = [];
    while (match = tokens.exec(input)) {
      assert(!match[2], function() {
          return 'Bad token in ' + input + ': ' + match[2];
        });
      if (match[1]) {
        // Whitespace
        continue;
      }
      var t = {name: match[0], index: match.index};
      result.push(t);
    }
    return result;
  }
  var tokens = tokenize(input);

  // Get next token, or "end" if no more, advancing past it.
  function next() {
    return tokens.shift() || end;
  }
    
  // Return the next token without advancing, or "end" if there are no
  // more.
  function peek() {
    return tokens[0] || end;
  }

  // Consume type expressions until EOF or close paren, returning
  // a type or null if no input is consumed.
  // Do not consume a final close paren.
  function parse() {
    var left = null;
    for (var token = peek(); ; token = peek()) {
      var name = token.name;
      if (name === ')' || name === '(end)') {
        return left;
      }
      // Consume the peeked token.
      next();
      switch(name) {
      case '(':
        var type = parse();
        var tok = next();
        name = tok.name;
        assert(name === ')',
               function() {
                 return 'Unbalanced parens in ' + input + ' at: ' + name;
               });
        left = left ? new FunctionType(type, left) : type;
        break;
      case 'i':
        left = left ? new FunctionType(individual, left) : individual;
        break;
      case 'o':
        left = left ? new FunctionType(boolean, left) : boolean;
        break;
      default:
        if (name.match(/^(t[0-9]+|[A-Z])$/)) {
          var type = new TypeVariable(name);
          left = left ? new FunctionType(type, left) : type;
        } else {
          assert(false, 'Unknown token in type term: "' + name + '"');
        }
      }
    }
    // End of input:
    return left;
  }

  var result = parse();
  assert(result, 'Empty input in type term: ' + input);
  // assert(peek() != end, 'Excess input in type term: ' + input);
  return result;
}


//// TYPE INFERENCE
////
//// The type inference code is derived from the description and code
//// for Hindley-Milner style type inference at
//// http://lucacardelli.name/Papers/BasicTypechecking.pdf and from
//// Robert Smallshire's Python implementation at
//// http://www.smallshire.org.uk/sufficientlysmall/2010/04/11/
//// a-hindley-milner-type-inference-implementation-in-python/.

// TODO: More and better comments throughout the type analysis code.

/**
 * Expr method that returns any annotated type, otherwise throws
 * an error.
 */
Expr.prototype.getType = function() {
  return dereference(this._type) || err('Type not available: ' + this);
};

/**
 * Returns the type of the expression like findType, but also
 * annotates the expression and all subexpressions with type
 * information as the _type property of each.  Only appropriate for
 * expressions containing no shared structure such as rendered
 * expressions.  Variables (Atoms) must be among the structures
 * not shared.
 *
 * If this is already annotated, simply returns the annotation.
 */
Expr.prototype.annotateWithTypes = function() {
  return this._type || findType(this, true);
};

/**
 * Find and return the type of an expression (Expr).  Throws an Error
 * if type checking fails.  The error may have a "cause" property with
 * the original error (TypeCheckError).
 *
 * The second argument is private to annotateWithTypes.
 */
function findType(expr, annotate) {
  // In this code types[i] will be the type of vars[i].
  // The vars are names of variables.  Bound variables and their types
  // are pushed onto the lists, and on exit from a scope the
  // information is popped off the lists.  Type lookups search from
  // the end toward the beginning thus finding the type of the
  // variable visible in the current scope.
  var vars = [];
  var types = [];
  // A list of TypeVariable objects that are not generic in the
  // current scope.  Type variables in the types of variables appear
  // here when their variable is in scope.
  //
  // Note: Generic type variables reflect the fact that different
  // occurrences of the same defined or primitive constant can have
  // different types.
  var nonGenerics = [];

  var analyze =
    (annotate
     ? function(expr) { return expr._type = analyze1(expr); }
     : analyze1);

  // This is the core of the type inference algorithm.
  function analyze1(expr) {
    if (expr instanceof Atom) {
      return typeFromName(expr.name);
    } else if (expr instanceof Call) {
      var fnType = analyze(expr.fn);
      var argType = analyze(expr.arg);
      var resultType = new TypeVariable();
      unifyTypes(new FunctionType(argType, resultType), fnType);
      return resultType;
    } else if (expr instanceof Lambda) {
      vars.push(expr.bound.name);
      // TODO: Handle explicit type info on the bound variable.
      var argType = new TypeVariable();
      types.push(argType);
      nonGenerics.push(argType);
      var resultType = analyze(expr.body);
      vars.pop();
      types.pop();
      nonGenerics.pop();
      return new FunctionType(argType, resultType);
    }
    throw new TypeCheckError('Expression of unknown type: ' + expr);
  }

  function typeFromName(name) {
    if (isIntegerLiteral(name)) {
      // I say integers are individuals.
      return individual;
    }
    // Is it a bound or (already-seen) free variable?
    for (var i = vars.length - 1; i >= 0; --i) {
      if (vars[i] == name) {
        var type = types[i];
        // Return a fresh instance of the variable's type.
        return type.fresh({}, nonGenerics);
      }
    }
    if (isConstantName(name)) {
      return lookupType(name).fresh({}, nonGenerics);
    } else {
      // Free variable: not constant, not defined.
      // Like handling of a variable binding, but scope is the remainder
      // of the expression, and bound variables get searched first.
      var varType = new TypeVariable();
      vars.unshift(name);
      types.unshift(varType);
      nonGenerics.unshift(varType);
      return varType;
    }
  }

  /**
   * Look up the type of a primitive or defined constant.  Result is
   * not fresh.
   */
  function lookupType(name) {
    if (constantTypes.hasOwnProperty(name)) {
      return constantTypes[name];
    } else if (isDefinedByCases(name)) {
      return definedTypes[name];
    } else if (isDefined(name)) {
      return findType(getDefinition(name).getRight());
    } else {
      throw new TypeCheckError('Cannot find type for: ' + name);
    }
  }

  function isGeneric(v) {
    return !occursInList(v, nonGenerics);
  }

  try {
    return dereference(analyze(expr));
  } catch(e) {
    if (e instanceof TypeCheckError) {
      var message = 'Cannot find type for ' + expr.toUnicode();
      err({message: message, cause: e},
          TypeCheckError);
    } else {
      throw e;
    }
  }
}

/**
 * Assumes "type" is dereferenced.
 */
function occursInList(type, types) {
  for (var i = 0; i < types.length; i++) {
    if (occursInType(type, types[i])) {
      return true;
    }
  }
  return false;
}

/**
 *
 * Assumes type1 is dereferenced.
 */
function occursInType(type1, type2) {
  var type2 = dereference(type2);
  if (type2 == type1) {
    return true;
  } else if (type2 instanceof TypeOperator) {
    return occursInList(type1, type2.types);
  }
}

function unifyTypes(t1, t2) {
  var a = dereference(t1);
  var b = dereference(t2);
  if (a instanceof TypeVariable) {
    if (a != b) {
      if (occursInType(a, b)) {
        throw new TypeCheckError('recursive unification');
      }
      a.instance = b;
    }
  } else if (b instanceof TypeVariable) {
    unifyTypes(b, a);
  } else if (a instanceof TypeConstant) {
    if (a !== b) {
      // Note that this does not permit multiple copies of a constant.
      throw new TypeCheckError('Type mismatch: ' + a + ' != ' + b);
    }
  } else if (a instanceof TypeOperator && b instanceof TypeOperator) {
    if (a.name != b.name || a.types.length != b.types.length) {
      throw new TypeCheckError('Type mismatch: ' + a + ' != ' + b);
    }
    for (var i = 0; i < a.types.length; i++) {
      unifyTypes(a.types[i], b.types[i]);
    }
  } else {
    throw new TypeCheckError('Not unifiable');
  }
}

function dereference(type) {
  if (type instanceof TypeVariable) {
    if (type.instance) {
      type.instance = dereference(type.instance);
      return type.instance;
    }
  }
  return type;
}


//// CONSTANTS AND DEFINITIONS
////
//// The only primitive constants currently are the built-in T, F, =,
//// "the", but others may be defined.

function booleanBinOpType() {
  return new FunctionType(boolean, new FunctionType(boolean, boolean));
}

function equalityType() {
  var v = new TypeVariable();
  return new FunctionType(v, new FunctionType(v, boolean));
}

function funType() {
  var v = new TypeVariable();
  return new FunctionType(v, v);
}

function fun2Type() {
  var v = new TypeVariable();
  return new FunctionType(v, new FunctionType(v, v));
}

function theType() {
  var v = new TypeVariable();
  return new FunctionType(new FunctionType(v, boolean), v);
}

// Types of _primitive_ constants only here.
var constantTypes = {
  T: boolean,
  F: boolean,
  '=': equalityType(),
  the: theType(),
  // The real numbers.
  R: new FunctionType(individual, boolean),
  '>': equalityType(),
  '>=': equalityType(),
  '<': equalityType(),
  '<=': equalityType(),
  '!=': equalityType(),
  '+': fun2Type(),
  '-': fun2Type(),
  '*': fun2Type(),
  '/': fun2Type(),
  '**': fun2Type(),
  neg: funType(),
  recip: funType(),
  sqrt: funType(),
  // Absolute value
  abs: funType(),
  // Reciprocal
  recip: funType(),
  // Trigonometry:
  pi: individual,
  sin: funType(),
  cos: funType(),
  tan: funType(),
  arcsin: funType(),
  arccos: funType(),
  arctan: funType(),
  // Exponentials
  ee: individual,               // "e"
  ln: funType(),
  log10: funType()
};

// Types of operations defined by cases.
// TODO: Consider inferring these instead from the definitions.
var definedTypes = {
  '&': booleanBinOpType(),
  '|': booleanBinOpType(),
  '==>': booleanBinOpType()
};

// Indexed by the name defined.  Value is an expression if
// the definition is simple.  If by cases, the value is a
// map from 'T' and 'F' to the definition for each case.
//
// Primitive constants are here, but the definitions are truthy fakes.
// This prevents them from being defined later.
var definitions = {
  T: true,
  F: true,
  '=': true,
  the: true
};

/**
 * Add a simple abbreviation-like definition, e.g.
 * define('forall', equal(lambda(x, T))).  Returns the equation.
 */
function define(name, definition) {
  assert(isConstantName(name), 'Not a constant name: ' + name);
  definition = typeof definition == 'string' ? parse(definition) : definition;
  assert(definition instanceof Expr,
         'Definition must be a term: ' + definition);
  if (isDefined(name)) {
    assert(definition.matches(getDefinition(name)),
           'Already defined: ' + name);
    // Benign redefinition, do nothing.
    return;
  }
  for (var n in definition.freeNames()) {
    assert(false, 'Definition has free variables: ' + name);
  }
  return definitions[name] = equal(name, definition);
}

/**
 * Add a simple definition with true/false cases.  A call could
 * be something like defineCases('not', F, T).
 */
function defineCases(name, ifTrue, ifFalse) {
  assert(isConstantName(name), 'Not a constant name: ' + name);
  assert(!definitions.hasOwnProperty(name), 'Already defined: ' + name);
  for (var n in ifTrue.freeNames()) {
    assert(false, 'Definition has free variables: ' + name);
  }
  for (var n in ifFalse.freeNames()) {
    assert(false, 'Definition has free variables: ' + name);
  }
  definitions[name] = {T: equal(call(name, 'T'), ifTrue),
                       F: equal(call(name, 'F'), ifFalse)};
}

/**
 * Returns whether the name (or Atom) currently has a simple
 * definition.
 */
function isDefined(name) {
  if (name instanceof Atom) {
    name = name.name;
  }
  assert(typeof name == 'string', function() {
      return 'Non-string name: ' + name;
    });
  return definitions[name] instanceof Expr;
}

/**
 * Returns whether the name (or Atom) currently has a definition by
 * cases.
 */
function isDefinedByCases(name) {
  if (name instanceof Atom) {
    name = name.name;
  }
  assert(typeof name == 'string', function() {
      return 'Non-string name: ' + name;
    });
  return (definitions.hasOwnProperty(name)
	  && !!definitions[name].T);
}

/**
 * Fetch a simple or by-cases definition from the definitions
 * database.  Throws an exception if an appropriate definition is not
 * found.  Pass true or false or T or F or 'T' or 'F' to get the
 * appropriate part of a definition by cases.
 *
 * TODO: See findDefinition for more information on this.
 */
function getDefinition(name, tOrF) {
  var defn = findDefinition(name, tOrF);
  assert(defn, 'Not defined: ' + name);
  return defn;
}

/**
 * Finds a definition or by-cases definition in the definitions
 * database.  Returns null if there is no definition; throws an error
 * if there is a definition, but wrong type.  If the tOrF argument is
 * present, the definition must be by cases, otherwise simple.  Also
 * accepts a Atom.
 *
 * TODO: Somehow avoid the unsafeness of this; consider eliminating
 * this and moving getDefinition functionality into rules.definition.
 * Problem is that the result is not officially justified.
 */
function findDefinition(name, tOrF) {
  name = name instanceof Atom ? name.name : name;
  var defn = definitions[name];
  assert(defn, function() { return 'Not defined: ' + name; });
  if (!tOrF) {
    assert(defn instanceof Expr, 'Definition is not simple: ' + name);
    return defn;
  } else {
    if (tOrF == true || (tOrF instanceof Atom && tOrF.name == 'T')) {
      tOrF = 'T';
    } else if (tOrF == false || (tOrF instanceof Atom && tOrF.name == 'F')) {
      tOrF = 'F';
    }
    assert(!(defn instanceof Expr),
             'Definition is not by cases: ' + name);
    var defnCase = defn[tOrF];
    assert(defnCase, 'Not defined: ' + name + ' ' + tOrF);
    return defnCase;
  }
}


// Atom (and constants) naming etc.

// String that matches identifiers, used in the tokenizer and
// identifierRegex.
var identifierPattern = '[_a-zA-Z][_a-zA-Z0-9]*';

// Names matching this regex are identifiers.
// The trailing "$" ensures that the entire name is matched
// up to any extensions for unique ID and/or type information.
var identifierRegex = new RegExp('^' + identifierPattern + '([.:]|$)');

// Variables in particular, not including identifiers for constants.
// The "." and ":" provide for extension with bound variable unique
// identifiers and type signatures.
//
// TODO: Make variable naming and subscripting consistent and
// rational!  Currently variable names of a single alphabetic
// character are pretty good, but ones beginning with underscore
// are probably nonsensical.
var variableRegex = /^[a-z][0-9_]*([.:]|$)|^_/;

// Numeric literals.
var numeralRegex = /^-?[0-9]+$/;

/**
 * Is the given string a legal variable name?  Only names with a
 * single lower-case letter and then a sequences of digits and/or
 * underscores, or beginning with an underscore are variables, the
 * rest are considered constants whether defined or not.
 *
 * Use the Expr.isVariable method where possible, as it may be
 * implemented for higher performance.
 */
function isVariableName(name) {
  assert(typeof name == 'string', function() {
    return 'isVariable - name must be a string: ' + name;
  });
  return name.match(variableRegex);
}

/**
 * Any (legal) name that is not a variable is considered a constant.
 */
function isConstantName(name) {
  return !isVariableName(name);
}

/**
 * Returns the name given if it is not in existingNames, a set with
 * name strings as keys.  Otherwise returns a generated name with the
 * same "base" as the one given, and not in existingNames.  The base
 * is the name with any "_N" suffix removed.  The generated suffix
 * will be the lowest-numbered one not yet in use, starting with "_1".
 * Adds the returned name to the existingNames set.
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
 * Returns a new Atom with a name generated by genName.
 */
function genVar(name, existingNames) {
  return new Atom(genName(name, existingNames));
}

// Last value used to uniquely (re!)name a bound variable.
// Private to _genBoundVar
var _boundVarCounter = 1;

/**
 * Generates a new bound variable with new name; private to
 * Expr.subFree, which guarantees that the variable will never
 * appear free.  Private to Expr.subFree.
 */
function _genBoundVar(name) {
  // Use only the first letter of the previous name to
  // avoid names with multiple numeric parts.
  return new Atom(name[0] + '.' + _boundVarCounter++);
}

/**
 * True iff this variable was generated specifically as a bound
 * variable.
 */
Atom.prototype.isGeneratedBound = function() {
  return this.name.indexOf('.') > -1;
};

/**
 * Parses the Atom's name into the base name (e.g. "x"), subscript if
 * any (digits), and a type expression, returning information as an
 * object with properties "name", "sub", and "type", which are
 * undefined if not present.  The subscript is the part following and
 * underscore or dot, if any, for names generated by genVar or
 * _genBoundVar.
 */
Atom.prototype.parseName = function() {
  var match = this.name.match(/^(.+?)([_.](.*?))?([:](.*))?$/);
  return {name: match[1], sub: match[3], type: match[5]};
};


//// PARSING

// Notes on internal representation of Vars created by parsing
//
// The equal sign can be input as either "=" or "==".  The parser
// retains the form in which it was entered as its pname, and printing
// displays it accordingly as well, though inference rules look only at
// the standard name ("=").
//
// Some common Vars are commonly displayed with non-ASCII characters.
// These also have ASCII input syntax, which is the form the parser
// expects.  The internal form retains the input syntax, but the Unicode-
// oriented displays both text and HTML show them as Unicode.

// Tokens pattern, private to tokenize.
var _tokens = new RegExp(['[(){}\\[\\]]',
                           // Identifiers: variables and named constants
                           identifierPattern,
                           // Numeric constants.  The parser glues together
                           // negative numerals later.
                           '[0-9]+',
                           // Strings
                           '"(?:\\\\.|[^"])*"',
                           // Other operators (constants)
                           // TODO: Narrow this to graphic nonalphabetic
                           //   characters.
                           '[^_:a-zA-Z0-9(){}\\s]+'].join('|'),
                         'g');

/**
 * A token is a parenthesis or brace, or a sequence of characters
 * starting with an alphabetic (possibly preceded by an underscore
 * ("_"), followed by zero or more characters that are alphanumeric or
 * ":", or a sequence containing none of these and no whitespace.
 * 
 * This returns an array of tokens in the input string, followed by an
 * "(end)" token, omitting whitespace.  All tokens are Atom objects
 * with the text of the token as its name and its index in the input
 * as its "pos" property.
 */
function tokenize(str) {
  var match;
  var result = [];
  while (match = _tokens.exec(str)) {
    result.push(new Atom(match[0], match.index));
  }
  result.push(new Atom('(end)', str.length));
  return result;
}

// Map from input strings to their parsed values.  Used for
// memoization of user inputs.  Only stores inputs for which
// a type can be found.
var _parsed = {};

/**
 * Parses a string or array of token strings into an expression
 * (Expr).  Removes tokens parsed from the tokens list.  Throws an
 * Error if parsing fails or if findType cannot determine a type
 * for the expression.
 */
function parse(input) {
  if (typeof input == 'string' &&
      _parsed.hasOwnProperty(input)) {
    return _parsed[input];
  }
  var result = justParse(input);
  findType(result);
  if (typeof input == 'string') {
    _parsed[input] = result;
  }
  return result;
}

/**
 * Same as "parse", but does not try to find a type for the
 * expression and does not memoize in _parsed.
 */ 
function justParse(input) {
  try {
    return justParse1(input);
  } catch(e) {
    err({cause: e, message: 'Could not parse "' + input + '"'});
  }
}

/**
 * Same as justParse, but throws errors with low-level messages.
 */
function justParse1(input) {
  var tokens = input;

  /**
   * Consumes and returns the next token, or the end token if there
   * are no more.
   */
  function next() {
    return tokens.shift() || end;
  }

  /**
   * Returns the next token without consuming it, or the end token
   * if no tokens remain.
   */
  function peek() {
    return tokens[0] || end;
  }

  /**
   * Consumes the next token as returned by next(), throwing an Error
   * if it is not euqal to the one expected.
   */
  function expect(expected) {
    var token = next();
    if (token.name != expected) {
      // Report somehow.
      var error = new Error('Expected ' + expected + ', got ' + token.name);
      error.position = token.pos;
      throw error;
    }
  }

  /**
   * Add this to the power of the next token to break
   * ties with right associativity.
   *
   * TODO: Support right-associative binary operators here.
   *
   */
  function rightBoost(power) {
    return (power === unaryPower) ? 1 : 0;
  }

  /**
   * True iff the given precedence indicates a binary operator.
   */
  function isBinaryPower(power) {
    return 0 < power && power < namePower;
  }

  /**
   * Keep reducing leading parts into subtrees until the next token is
   * an infix operator with precedence not greater than lastPower (or
   * equal with right precedence), returning the parse tree built from
   * everything up to that operator and leaving it in the tokens list.
   * Returns null if it consumes no input.  ("Above" here means
   * numerically greater.)  This is a top-down operator precedence
   * parser.
   *
   * This function is responsible for parsing a subexpression that was
   * preceded by an infix operator or opening "bracket".
   *
   * The lastPower will be 0 or 1 if there is no left context, or some
   * binary operator precedence, or unaryPower - 1 in case the next
   * operand is for a unary operator.
   */
  function parseAbove(lastPower) {
    // A "left" expression is context for continued parsing.  It will
    // either be the function part of a function call or the left
    // operand of a binary operator, or null if neither of these
    // is present.
    var left = null;
    while (true) {
      var token = peek();
      var name = token.name;
      var nextPower = getPrecedence(token);
      if (nextPower + rightBoost(nextPower) <= lastPower) {
        // Return the parse tree from the prior tokens.
        return left;
      }
      // Consume the token.
      next();
      var expr = null;
      // If an atomic expression or unary/nullary expression is
      // next, expr will get its parse: the right or only side
      // of this operator or function.
      if (name === '(') {
        // The 1 indicates that the parser just saw "(".
        expr = mustParseAbove(1);
        expect(')');
      } else if (name === '{') {
        var id = next();
        assert(id.isVariable(), 'Expected identifier, got ' + id.name);
        expect('.');
        var body = mustParseAbove(0);
        expr = lambda(id, body);
        expect('}');
      } else if (nextPower === namePower) {
        // Even if lastPower indicates an operator take the token as
        // the next expression, e.g. x + f y, where lastPower comes
        // from "+" and "f" is the current token.
        expr = token;
      } else if (!left && lastPower === 1 && peek().name === ')') {
        // Accept a unary or binary operator as an expression
        // if directly enclosed in parentheses.
        expr = token;
      } else if (left && isBinaryPower(nextPower)) {
        var right = parseAbove(nextPower);
        left = right
          ? infixCall(left, token, right)
          : new Call(token, left);
        // Binops are a special case that does not set expr
        // and use it as an argument to "left".
        continue;
      } else if (nextPower === unaryPower) {
        // Build a parse with the parse tree for all unary
        // and nullary operators upcoming.
        expr = new Call(token, parseUnaryArg());
      } else if (name === '-') {
        // If the token is '-', but does not parse as infix,
        // treat it as 'neg', or even as part of a negative
        // number.
        var peeked = peek();
        if (peeked.pos === token.pos + 1 && peeked.isNumeral()) {
          // If the "-" is directly adjacent, treat the whole thing
          // as a negative numeral.  The tokenizer will not build
          // a numeral with a leading "-".
          next();
          expr = new Atom('-' + peeked.name, token.pos);
        } else {
          expr = new Call(new Atom('neg'),  parseUnaryArg());
        }
      } else {
        throw new Error('Unexpected token "' + token.name +
                        '" at ' + token.pos);
      }
      left = left ? new Call(left, expr) : expr;
    }
  }

  /**
   * Like parseAbove, but throws an Error if it consumes no input.
   */
  function mustParseAbove(lastPower) {
    var result = parseAbove(lastPower);
    if (!result) {
      throw new Error('Empty expression at ' + peek().pos);
    }
    return result;
  }

  /**
   * Parses the argument of a unary operator, throwing an error
   * if the upcoming tokens are not suitable.  Returns an Expr.
   */
  function parseUnaryArg() {
    var token = peek();
    var power = getPrecedence(token);
    if (power < unaryPower) {
      next();
      return token;
    } else if (power === unaryPower || token.name === '-') {
      next();
      return new Call(token, parseUnaryArg());
    } else if (power > unaryPower) {
      // An opening bracket of some kind.
      return mustParseAbove(power - 1);
    } else {
      throw new Error('Unexpected token "' + token.name +
                      '" at ' + token.pos);
    }
  }

  // Do the parse!

  if (typeof input == 'string') {
    tokens = tokenize(input);
  }
  // The ending token.
  var end = tokens.pop();
  if (tokens.length < 1) {
    // There should be at least one real token.
    throw new Error('No parser input');
  }
  var result = parseAbove(0);
  if (tokens.length) {
    throw new Error('Extra input: "', + tokens[0] + '"');
  }
  return result;
}

/**
 * Returns the number of entries in the parser lookup table.
 */
function nParsed() {
  var i = 0;
  for (var key in _parsed) { i++; }
  return i;
};

/**
 * Extracts and returns the actual string content
 * from the external representation of a string.
 */
function parseStringContent(name) {
  var content = name.substring(1, name.length - 1);
  return content.replace(/\\(.)/g, '$1');
}

/**
 * Creates and returns a parseable external representation for a
 * string.
 */
function unparseString(content) {
  var s1 = content.replace(/["\\]/g, '\\$&');  // For emacs: "]);
  var s2 = s1.replace(/\n/g, '\\n');
  return '"' + s2 + '"';
}

/**
 * Parse the given string.  If it contains any apparent math variables
 * (as by calling Expr.mathVars), and is not already a conditional
 * with real number conditions on variables, adds assumptions that all
 * of those "math variables" are real numbers.
 *
 * If string begins with "@", simply parses the rest.
 */
function mathParse(str) {
  if (str[0] === '@') {
    return parse(str.slice(1));
  }
  var expr = parse(str);
  var assume = expr.mathVarConditions();
  if (assume) {
    var explicit = false;
    if (expr.isCall2('==>')) {
      expr.getLeft().eachHyp(function (hyp) {
          if (hyp.isCall1('R') && hyp.arg instanceof Atom) {
            // The expression has at least one explicit real
            // number condition.
            explicit = true;
          }
        });
    }
    if (explicit) {
      return expr;
    } else if (expr.isCall2('==>')) {
      // Any type assumptions follow the LHS.
      var result = infixCall(expr.getLeft().concat(assume, '&'),
                             '==>',
                             expr.getRight());
      return result;
    } else {
      var result = infixCall(assume, '==>', expr);
      result.hasHyps = true;
      return result;
    }
  } else {
    return expr;
  }
}

/**
 * Get a precedence value: 100 for identifiers, defaults to same as
 * multiplication for unknown non-symbols.
 *
 * TODO: Include context in the computation, specifically prefix
 *   versus infix context.
 */
function getPrecedence(token) {
  var name = token.pname || token.name;
  if (precedence.hasOwnProperty(name)) {
    return precedence[name];
  } else {
    return (!token.isLiteral() && !isIdentifier(name)
            // It's written as an operator, give it the default precedence.
            ? 40
            : 100);
  }
}

// Unary operators should all be the same.
var unaryPower = 200;

// Alphanumeric names have this power unless specified otherwise.
var namePower = 100;

// Precedence table for infix operators.
var precedence = {
  // Closing tokens have power 0 to make infix parsing return.
  '(end)': 0,
  ')': 0,
  '}': 0,
  // Value of 1 is reserved in parseAbove and mustParseAbove to indicate
  // that the preceding token was "(".
  // 
  // Alias for '=', with lower precedence.
  '==': 2,
  '==>': 11,
  '|': 13,
  '&': 15,
  // Unlike the book, equality binds tighter than implication.  This
  // way makes more sense when working with numbers for example.
  '=': 20,
  '!=': 20,
  '<': 20,
  '<=': 20,
  '>': 20,
  '>=': 20,
  '+': 30,
  '-': 30,
  '*': 40,
  '/': 40,
  '**': 50,
  forall: unaryPower,
  exists: unaryPower,
  not: unaryPower,
  neg: unaryPower,
  // Specials
  '(': 1000,
  '{': 1000
};

// Translations of names, applied during conversion to Unicode.
// (When generating HTML and/or Unicode text.)
var unicodeNames = {
  '==': '\u21d4',     // Two-headed horizontal double arrow.
  '==>': '\u21d2',    // &rArr;
  '!=': '\u2260',     // &ne;
  '<=': '\u2264',     // &le;
  '>=': '\u2265',     // &ge;
  '*': '\u22c5',      // &sdot;
  '-': '\u2212',      // &minus;
  '/': '\u2215',      // division slash
  neg: '-',
  forall: '\u2200',
  exists: '\u2203'
};

function unicodify(text) {
  var pattern =
    /==>|==|!=|<=|>=|\*|-|\/|\bforall\b|\bexists\b/g;
  return text.replace(pattern, function(symbol) {
      return unicodeNames[symbol];
    });
}

// Defines aliases that affect both printing and parsing.
var aliases = {
  // Note that limiting '==' to boolean inputs would make it more than
  // just an alias as currently defined.
  '==': '=',
};


//// Refresher class and deferred actions

/**
 * Creates an object that will run the given function, if activated,
 * the next time the event system becomes idle.  When the function
 * runs, the Refresher becomes ready for another activation.
 */
function Refresher(fn) {
  this.fn = fn;
  this._timer = null;
  this.active = false;
}

/**
 * Activates this Refresher to run the next time the event system
 * becomes idle.
 *
 * Commonly used to receive notifications that an object has changed
 * or needs to change.
 */
Refresher.prototype.activate = function() {
  var self = this;
  var fn = this.fn;
  function action() {
    self._timer = null;
    self.active = false;
    fn();
  }
  if (this._timer === null) {
    this.active = true;
    this._timer = soonDo(action);
  }
};

/**
 * Do the action as soon as the event handling system becomes idle.
 * It will run after the current initialization or event handler
 * completes.
 */
function soonDo(action) {
  return window.setTimeout(action, 0);
}

/**
 * Do the action as soon as possible after giving the page a chance to
 * repaint.  Sometimes Webkit needs a small delay to trigger a
 * repaint, regardless of some of the claims made on
 * stackoverflow.com.
 */
function afterRepaint(action) {
  return window.setTimeout(action, 10);
}


//// UTILITY FUNCTIONS

/**
 * Is the given object empty, i.e. has it any enumerable properties?
 */
function isEmpty(o) {
  for (var key in o) {
    return false;
  }
  return true;
}

/**
 * Converts an Expr or plain token string to Unicode.
 */
function toUnicode(o) {
  if (typeof o === 'string') {
    return unicodeNames[o] || o;
  } else {
    return o.toUnicode();
  }
} 

/**
 * Return the Atom v, or if the argument is a string, create a new
 * variable from it.  The name must be legal for a user-created
 * variable.
 */
function varify(v) {
  var v = (typeof v == 'string') ? new Atom(v) : v;
  if (!v.isVariable() || v.isGeneratedBound()) {
    throw new Error('Bad variable name: ' + v.name);
  }
  return v;
};

/**
 * Return the Atom c, or if the argument is a string, create a new
 * constant from it, checking that the name is legal for a constant.
 */
function constify(c) {
  var c = (typeof c == 'string') ? new Atom(c) : c;
  if (!c.isConst()) {
    throw new Error('Bad constant name: ' + c.name);
  }
  return c;
}

/**
 * Coerce the given Expr or string to an Expr by parsing it
 * if not an Expr.
 */
function termify(x) {
  return (x instanceof Expr) ? x : parse(x);
}

/**
 * Calls a function given as a constant or name of a constant, passing
 * one or more arguments.
 */
// TODO: Eliminate use fo binops in favor of infixCall.  This will
// be problematic for some infix operators.
function call(fn, arg) {
  // TODO: Allow fn to be a variable name.
  fn = fn instanceof Expr ? fn : constify(fn);
  if ((typeof arg) == 'string') {
    arg = new Atom(arg);
  }
  var result = new Call(fn, arg);
  // Skip fn and the first "arg" after that.
  for (var i = 2; i < arguments.length; i++) {
    result = call(result, arguments[i]);
  }
  return result;
}

/**
 * Returns a call with the two operands and the given op (middle
 * argument) as the binary operator between them.  The op must be a
 * constant or a name suitable for one.
 */
function infixCall(arg1, op, arg2) {
  // TODO: Change this when redefining meaning of infix operators.
  op = constify(op);
  return new Call(new Call(op, arg1), arg2);
}

/**
 * Builds an expression [lhs = rhs] if RHS is present,
 * otherwise just [= lhs].
 * TODO: Order of args changes when infix changes.  Similarly for
 * implies and other infix operators.
 */
function equal(lhs, rhs) {
  if (rhs) {
    return call('=', lhs, rhs);
  } else {
    return call('=', lhs);
  }
}

/**
 * Builds an expression [lhs ==> rhs].
 */
function implies(lhs, rhs) {
  return call('==>', lhs, rhs);
}

/**
 * Builds a Lambda.
 */
function lambda(bound, body) {
  return new Lambda(bound, body);
}

/**
 * This controls the policy over which function names are
 * to be rendered as infix.
 */
function isInfixDesired(vbl) {
  if (!(vbl instanceof Atom)) {
    return false;
  }
  var p = getPrecedence(vbl);
  return 0 < p && p < 100;
}

/**
 * True iff the given Atom is a unary operator.  Method that applies
 * only to Vars.
 */
Atom.prototype.isUnary = function() {
  return getPrecedence(this) === 300;
}

/**
 * True iff the source step of expr1 is less than the source step of
 * expr2, otherwise true iff dump(expr1) is lexicographically less
 * than dump(expr2).  Useful for ordering deduplicated hypotheses.
 */
function sourceStepLess(e1, e2) {
  if (e1.sourceStep) {
    if (e2.sourceStep) {
      return e1.sourceStep.ordinal < e2.sourceStep.ordinal;
    } else {
      return true;
    }
  } else if (e2.sourceStep) {
    return false;
  } else {
    // Neither has a source step.
    return e1.dump() < e2.dump();
  }
}

/**
 * True iff dump(expr1) is lexicographically less than dump(expr2),
 * otherwise true iff the source step of expr1 is less than the source
 * step of expr2.  Expressions with no source step compare greater
 * than expressions with a source step.
 *
 * In use this is used in sorting of expressions, so it must bring
 * equal expressions together so simplifications can see them.
 */
function hypIsLess(e1, e2) {
  if (e1.dump() < e2.dump()) {
    return true;
  } else if (e1.sourceStep) {
    if (e2.sourceStep) {
      return e1.sourceStep.ordinal < e2.sourceStep.ordinal;
    } else {
      return true;
    }
  } else if (e2.sourceStep) {
    return false;
  }
}

/**
 * Comparator for Array.sort corresponding to sourceStepLess.
 * Expressions from assumptions (steps) come before others, and others
 * sort lexicographically using "dump".
 */
function sourceStepComparator(e1, e2) {
  if (e1.sourceStep) {
    if (e2.sourceStep) {
      return e1.sourceStep.ordinal - e2.sourceStep.ordinal;
    } else {
      return -1;
    }
  } else if (e2.sourceStep) {
    return 1;
  } else {
    var s1 = e1.dump();
    var s2 = e2.dump();
    return (s1 === s2
            ? 0
            : (s1 < s2 ? -1 : 1));
  }
}

/**
 * Generates an expression containing only variables and the given
 * operator, where the variables are named x<indices[n]>, where n is
 * the nth element of indices, an array of nonnegative integers.  The
 * operator is a string or Atom.  The indices must contain at least one
 * element.
 *
 * Useful for rearranging expressions containing operators that are
 * commutative and associative.
 */
function repeatedCall(operator, indices) {
  var op = (typeof operator == 'string') ? new Atom(operator) : operator;
  function x(n) {
    return new Atom('x' + indices[n]);
  }
  assert(indices.length, 'Empty indices in repeatedExpr');
  if (indices.length == 1) {
    return x(0);
  } else {
    var expr = infixCall(x(0), op, x(1));
    for (var next = 2; next < indices.length; next++) {
      expr = infixCall(expr, op, x(next));
    }
  }
  return expr;
}

/**
 * Logs an error; the message if that is truthy, otherwise
 * the argument itself.
 */
function logError(err) {
  if (window.console) {
    window.console.log('Error: ' + (err.message || err));
  }
}

/**
 * Call the given function passing no arguments.  Report any errors to
 * the user and to the console, then rethrow.
 */
function withErrorReporting(fn) {
  try {
    return fn();
  } catch(err) {
    logError(err);
    window.alert(err.message);
    throw err;
  }
}

// Accumulation of assertion failures and potentially information
// about other errors that have occurred.
var errors = [];

/**
 * Asserts that the condition is true, throwing an exception if it is
 * not.  The message may be either a string or a function of no
 * arguments that returns something that can be logged.  If the
 * optional step is supplied it should be the most recent available
 * completed proof step.
 *
 * Logs the message and step into the errors list by appending an
 * object with properties 'message' and 'step'.
 */
function assertTrue(condition, message, step) {
  if (!condition) {
    if (typeof message == 'function') {
      message = message();
    }
    errors.push({message: message, step: step});
    var e = new Error(message);
    e.step = step;
    throw e;
  }
}

// Use the application's assertTrue function for assertions.
var assert = assertTrue;

/**
 * Asserts that the expression is an equation (must have
 * both left and right sides.
 */
function assertEqn(expr) {
  assert(expr instanceof Call
         && expr.fn instanceof Call
         && expr.fn.fn instanceof Atom
         && expr.fn.fn.name == '=',
         'Must be an equation: ' + expr);
}

/**
 * Removes from the first map all entries having keys enumerable in
 * the second map
 */
function removeAll(map1, map2) {
  for (var k in map2) {
    delete map1[k];
  }
}

/**
 * Removes from the first map all entries that are not "own" properties
 * of the second map.
 */
function removeExcept(map1, map2) {
  for (var k in map1) {
    if (!map2.hasOwnProperty(k)) {
      delete map1[k];
    }
  }
}

/**
 * Returns a string showing the top-level properties
 * of an object, and their values.  If "specials" is
 * given, it should be a map from key name to a function
 * for presenting the value of any key with that name.
 */
function debugString(o, specials) {
  if (typeof o == 'object') {
    var result = '{';
    var keys = [];
    for (var key in o) { keys.push(key); }
    keys.sort();
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i];
      if (o.hasOwnProperty(key)) {
        if (result.length > 1) {
          result += ', ';
        }
        result += key + ': ';
        var value = o[key];
        var f = specials && specials[key];
        if (f) {
          result += f(value);
        } else if (typeof value == 'string') {
          result += '"' + o[key] + '"';
        } else if ($.isArray(value)) {
          // Array-like value.
          vString = o[key].toString();
          if (vString.length > 40) {
            result += '[\n';
            for (var i = 0; i < value.length; i++) {
              result += value[i] + '\n';
            }
            result += ']\n';
          } else {
            result += '[' + o[key] + ']';
          }
        } else {
          result += '' + o[key];
        }
      }
    }
    return result + '}';
  } else {
    return o.toString();
  }
}

/**
 * Compute and return a string representing the given proof steps,
 * which may be either rendered or originals.  Treating expressions
 * with "multiple arguments" as lists, the format is an expression
 * starting with "steps", followed list of proof steps, each
 * represented as a list having first, the step's index, then the rule
 * name followed by all of the arguments.
 *
 * Each rule argument is represented as a list or string.  If a list,
 * the first element is "t" for a term (followed by the term itself),
 * "path" for a path (followed by the path as a string), or "s" for a
 * reference to another step (followed by the index of the referenced
 * step).
 */
function encodeSteps(steps_arg) {
  function rep(step) {
    var index = step.__index;
    var result = [];
    result.push(index);
    result.push(step.ruleName);
    var args = step.ruleArgs;
    for (var i = 0; i < args.length; i++) {
      var arg = args[i];
      if (arg instanceof Path) {
        result.push('(path "' + arg + '")');
      } else if (typeof arg === 'string') {
        result.push(unparseString(arg));
      } else if (arg instanceof Expr) {
        if (arg.__index) {
          result.push('(s ' + arg.__index + ')');
        } else {
          result.push('(t ' + arg + ')');
        }
      } else {
        result.push(arg.toString());
      }
    }
    return '(' + result.join(' ') + ')';
  }

  // Use the original steps throughout, so the ruleArgs refer
  // to the actual steps.
  var steps = steps_arg.map(function(step) {
      return step.original || step;
    });
  var reps = ['(steps'];
  for (var i = 0; i < steps.length; i++) {
    var step = steps[i];
    // Indexes are 1-based.
    step.__index = i + 1;
    reps.push(rep(step));
  }
  for (var i = 0; i < steps.length; i++) {
    delete steps[i].__index;
  }
  reps.push(')\n');
  return reps.join('\n');
}

/**
 * From the given input expression or string to be parsed,
 * computes and returns an array of steps.
 */
function decodeSteps(input) {
  input = typeof input == 'string' ? justParse(input) : input;
  var descriptions = input.asArray();
  var outSteps = [];
  descriptions.forEach(function(stepTerm, i) {
      if (i == 0) {
        // Like a "continue" ...
        return;
      }
      var stepInfo = stepTerm.asArray();
      assert(stepInfo.shift().getNumValue() == i, function() {
          return 'Mismatched step number in: ' + stepInfo;
        });
      var ruleName = stepInfo.shift();
      // The remainder of the array is arguments to the rule.
      var args = [];
      stepInfo.forEach(function(info) {
          args.push(decodeArg(info, outSteps));
        });
      outSteps.push(Toy.rules[ruleName].apply(Toy.rules, args));
    });
  return outSteps;
}

/**
 * Decodes an argument info Expr into an argument for a rule.
 * Argument info Exprs have one of the forms: (s <n>) for a step
 * number; (t <expr>) for a term; or (path <string>) for a path.
 */
function decodeArg(info, steps) {
  if (info.isString()) {
    return (info._value);
  } else {
    var key = info.nth(0).name;
    var value = info.nth(1);
    switch(key) {
      case 's':
        // Step indexes are 1-based.
        return (steps[value.getNumValue() - 1]);
        break;
      case 't':
        return (value);
        break;
      case 'path':
        return (Toy.path(value._value));
        break;
      default:
        assert(false, 'Unknown encoding key: ' + key);
      }
  }
}


//// Export public names.

Toy.memo = memo;
Toy.format = format;
Toy.configure = configure;
Toy.ownProperties = ownProperties;
Toy.object0 = object0;
Toy.err = err;
Toy.isEmpty = isEmpty;
Toy.each = each;
Toy.emptySet = emptySet;
Toy.tracked = tracked;
Toy.track = track;
Toy.trackingData = trackingData;

Toy.Result = Result;
Toy.catchResult = catchResult;
Toy.normalReturn = normalReturn;
Toy.Error = ErrorInfo;
Toy.TypeCheckError = TypeCheckError;
Toy.NestedTimer = NestedTimer;
Toy.Set = Set;
Toy.Map = Map;
Toy.TermSet = TermSet;
Toy.TermMap = TermMap;

Toy.Expr = Expr;
Toy.Atom = Atom;
Toy.Call = Call;
Toy.Lambda = Lambda;
Toy.Path = Path;

Toy.genVar = genVar;
Toy.decapture = decapture;
Toy.path = path;
Toy.findBinding = findBinding;
Toy.getBinding = getBinding;
Toy.sourceStepLess = sourceStepLess;
Toy.hypIsLess = hypIsLess;
Toy.sourceStepComparator = sourceStepComparator;
Toy.repeatedCall = repeatedCall;

Toy.define = define;
Toy.defineCases = defineCases;
Toy.findDefinition = findDefinition;
Toy.getDefinition = getDefinition;
// For testing:
Toy.definitions = definitions;

Toy.varify = varify;
Toy.constify = constify;
Toy.termify = termify;
Toy.isConstantName = isConstantName;
Toy.isVariableName = isVariableName;
Toy.isIdentifier = isIdentifier;
Toy.checkRange = checkRange;
Toy.isDefined = isDefined;
Toy.isInfixDesired = isInfixDesired;

Toy.getStepCounter = getStepCounter;
Toy.infixCall = infixCall;
Toy.call = call;
Toy.equal = equal;
Toy.implies = implies;
Toy.lambda = lambda;
Toy.withErrorReporting = withErrorReporting;
Toy.assertTrue = assertTrue;
Toy.assertEqn = assertEqn;
Toy.removeAll = removeAll;
Toy.removeExcept = removeExcept;

Toy.encodeSteps = encodeSteps;
Toy.decodeSteps = decodeSteps;

Toy.toUnicode = toUnicode;
Toy.unicodify = unicodify;
Toy.debugString = debugString;

Toy.Refresher = Refresher;
Toy.soonDo = soonDo;
Toy.afterRepaint = afterRepaint;

// Error analysis
Toy.errors = errors;

// Types

Toy.boolean = boolean;
Toy.individual = individual;
Toy.realType = realType;
Toy.TypeVariable = TypeVariable;
Toy.TypeOperator = TypeOperator;
Toy.FunctionType = FunctionType;
Toy.parseType = parseType;
Toy.findType = findType;

// For testing:
Toy._equalityType = equalityType;
Toy._parseStringContent = parseStringContent;
Toy.unparseString = unparseString;
Toy._decodeArg = decodeArg;

Toy.unaryPower = unaryPower;
Toy.namePower = namePower;
Toy.getPrecedence = getPrecedence;
Toy.tokenize = tokenize;
Toy.parse = parse;
Toy.justParse = justParse;
Toy.mathParse = mathParse;

Toy.logError = logError;

// For debugging
Toy.nParsed = nParsed;

})();
