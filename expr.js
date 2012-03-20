// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('expr', function(Y) {


//// GENERAL UTILITIES

// SET

function Set(stringifier) {
  this.map = {};
  this.stringifier = stringifier || String;
}

/**
 * Add an element.
 */
Set.prototype.add = function(value) {
  this.map[this.stringifier(value)] = value;
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

function identifyTerm(term) {
  return term.dump();
};

function TermSet(term) {
  TermSet.superclass.constructor.call(this, identifyTerm);
  if (term) {
    this.add(term);
  }
}  
Y.extend(TermSet, Set);

/**
 * A Map from terms to variables.  Use TermMap.addTerm to set up
 * values, never TermMap.set.  The "subst" field maintains a
 * corresponding substitution from names to terms.
 */
function TermMap() {
  TermMap.superclass.constructor.call(this, identifyTerm);
  this.counter = 1;
  this.subst = {};
}
Y.extend(TermMap, Map);

/**
 * Ensure the term is in this map.  If not already present, assign it
 * a new variable as its value.  In all cases return the map value.
 * Maintains the "subst" field as well.
 */
TermMap.prototype.addTerm = function(term) {
  if (!this.has(term)) {
    var name = 'a' + this.counter++
    this.set(term, new Y.Var(name));
    this.subst[name] = term;
  }
  return this.get(term);
};


// Utilities

/**
 * Is the given string a legal variable name?  Only names with a
 * single lower-case letter and then a sequences of digits and/or
 * underscores, or beginning with an underscore are variables, the
 * rest are considered constants whether defined or not.
 */
function isVariable(name) {
  assert(typeof name == 'string', function() {
    return 'isVariable - name must be a string: ' + name;
  });
  return name.match(/^[a-z][0-9_]*$|^_/);
}

/**
 * Any (legal) name that is not a variable is considered a constant.
 */
function isConstant(name) {
  return !isVariable(name);
}

// Used to order execution of proof steps so they can display
// in order of execution in an automatically-generated proof.
// This increments on every call to "justify".
// Conceptually it could be incremented just by rule R.
var stepCounter = 1;

function getStepCounter() {
  return stepCounter;
}

/**
 * Converts text symbols to HTML for display.
 */
var entities = {
  // Do not use nonbreaking hyphens in case the end user wants to copy and
  // paste displayed text.  Instead consider CSS hyphenation options.
  // '-->': '&#8209;&#8209&gt;',   // &rArr; looks lousy in fixed-width font.
  '>=': '&ge;',
  '<=': '&le;',
  '!=': '&ne;',
  '==': '&equiv;'
};

/**
 * Returns a new expression resulting from substitution of copies of
 * the replacement expression for all free occurrences of the given
 * name (or variable) in the target expression.  Used by Axiom 4
 * (lambda conversion).  Also renames bound variables in the target to
 * prevent them from capturing variables in the replacement.
 */
function subFree(replacement_arg, v, target) {
  var name = v instanceof Var ? v.name : v;
  if (replacement_arg instanceof Var && replacement_arg.name == name) {
    // No changes required.
    return target;
  }
  // Always replace with a new object so we can detect it as different
  // from parts of the original expression, for example replacing x
  // with (f x) in an expression containing an (f x).  Used in
  // avoiding capture of free variables.
  //
  // TODO: Instead of duplicating this bit of structure, note
  // replacement sites and 
  var replacement = replacement_arg.dup();
  var allNames = {};
  replacement._addNames(allNames);
  target._addNames(allNames);
  var result =
    target._subFree(replacement, name, replacement.freeNames(), allNames);
  // Now put back the original structure wherever it has been replaced.
  if (result == replacement) {
    return replacement_arg;
  } else {
    result._smashAll(replacement, replacement_arg);
    return result;
  }
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
 * Returns a new Var with a name generated by genName.
 */
function genVar(name, existingNames) {
  return new Var(genName(name, existingNames));
}

/**
 * Returns a copy of the target, renaming any bound variables in it
 * that have the same name as a free variable of the replacement.  It
 * makes them distinct from all variables appearing in either
 * expression.  After decapturing, straightforward substitution is
 * safe from capturing.
 */
function decapture(target, replacement) {
  var freeNames = replacement.freeNames();
  var allNames = {};
  replacement._addNames(allNames);
  target._addNames(allNames);
  // Now allNames contains every name occurring anywhere in either expression.
  return target._decapture(freeNames, allNames, null);
}

/**
 * Returns an equivalent expression with normalized names for bound
 * variables.
 */
function normalized(expr) {
  return expr.normalized(new Counter(1), null);
}


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
function matchAsSchema(schema, expr) {
  var substitution = {};
  var result = schema._matchAsSchema(expr, substitution);
  return result ? substitution : null;
}

/**
 * Packages up the "right way" to append a SPAN to a DOM node.
 */
function appendSpan(node) {
  return node.appendChild('<span class=expr></span>');
}

/**
 * Build and return a Node of class "expr".
 */
function exprNode() {
  return Y.Node.create('<span class=expr></span>');
}

/**
 * Create and return a text node containing a space.  YUI (and IE)
 * trim whitespace if you put in text in other ways.
 */
function space() {
  return document.createTextNode(' ');
}

function textNode(text) {
  return document.createTextNode(text);
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
 * Instantiated only for templates.  An instance of this class
 * in a replacement template indicates the place in the larger
 * expression where the replacement is to occur.
 */
function Expr() {
  this.sort = Expr.expr;
  // Type analysis adds a "type" property.
  // 
  // If part of a proof, has properties set by the "justify" method.
  // If has a rendered copy, has "rendering" property.
  //
  // If rendered, has a "node" property for an associated
  // DOM node (refers to a YUI Node).
  //
  // If rendered as a proof step, has:
  //   stepNode property with the YUI node of the entire step.
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

// The different sorts of expressions:
Expr.expr = 'expr';
Expr.var = 'var';
Expr.call = 'call';
Expr.lambda = 'lambda';

// This counts up to supply a unique name for bound variables renamed
// to avoid capturing.
Expr.counter = 1;

// Controls prefixing Calls and Lambdas with sourceStep info.
// A debugging and perhaps proof development aid when turned on.
Y.trackSourceSteps = false;

Expr.prototype.toString = function() {
  if (this instanceof Var) {
    return this._toString();
  }
  var prefix = '';
  if (Y.trackSourceSteps) {
    if (this.sourceStep) {
      prefix = '$';
      var stepNum =
        this.sourceStep.rendering && this.sourceStep.rendering.stepNumber;
      if (stepNum) {
        prefix += stepNum;
      }
    }
  }
  if (Y.trackSourceSteps
      && this.hasHyps
      && this.isCall2('-->')
      && isInfixDesired(this.fn.fn)) {
    var imply = new Var('|-');
    return (prefix + '(' + this.fn.arg._toString() + ' ' + imply + ' '
            + this.arg._toString() + ')');
  } else {
    return prefix + this._toString();
  }
};

/**
 * True iff this is a Var named as a variable.
 */
Expr.prototype.isVariable = function() {
  return this instanceof Var && isVariable(this.name);
};

/**
 * True iff this is a Var named as a constant.
 */
Expr.prototype.isConst = function() {
  return this instanceof Var && isConstant(this.name);
};

/**
 * Is this a numeric literal?
 */
Expr.prototype.isNumeral = function() {
  return this instanceof Var && typeof this.value == 'number';
};

/**
 * This is a constant T or F.
 */
Expr.prototype.isBoolConst = function() {
  return (this instanceof Var &&
          (this.name == 'T' || this.name == 'F'));
};

/**
 * Returns a new expression like this implication, but marked as
 * having hypotheses.  Useful in tests, perhaps other contexts also.
 */
Expr.prototype.asHyps = function() {
  this.assertCall2('-->');
  var result = this.dup();
  result.hasHyps = true;
  return result;
};

/**
 * Returns true iff this is a call that would display in infix (a Call
 * internally of the form ((op arg1) arg2), where op is a symbol
 * defined to display as infix.
 */
Expr.prototype.isInfixCall = function() {
  return (this instanceof Call
          && this.fn instanceof Call
          && this.fn.fn instanceof Var
          && isInfixDesired(this.fn.fn));
};

/**
 * Returns true iff the given name appears free in this.
 */
Expr.prototype.hasFreeName = function(name) {
  assert(typeof name == 'string', 'Not a name: ' + name);
  return this.freeNames().hasOwnProperty(name);
}

/**
 * Returns a shallow copy of this, annotating the copy with the rule
 * name, rule arguments, hasHyps flag, and dependencies (ruleName,
 * ruleArgs, ruleDeps).  "This" becomes the "details" property if it
 * already has a justification.  (Axioms, definitions and assertions
 * are not generated by rules, though theorems are.)  The ruleArgs and
 * ruleDeps arrays are both optional, and empty if not given.
 *
 * Calculates and records a hasHyps property for the result unless
 * this already has a hasHyps property.
 */
Expr.prototype.justify = function(ruleName, ruleArgs, ruleDeps) {
  var expr = this.dup();
  if (this.ruleName) {
    expr.details = this;
  }
  // Carry hypotheses forward.
  expr.hasHyps = this.hasHyps;
  expr.ruleName = ruleName;
  expr.ruleArgs = Y.Array(ruleArgs || []);
  expr.ruleDeps = Y.Array(ruleDeps || []);
  expr.ordinal = stepCounter++;
  return expr;
};

/**
 * Match this expr against a schema, which may be given as a string.
 * See function matchAsSchema.
 */
Expr.prototype.matchSchema = function(schema) {
  if (typeof schema == 'string') {
    schema = Y.parse(schema);
  }
  return matchAsSchema(schema, this);
};

/**
 * Alternate name for Expr.matchSchema.
 */
Expr.prototype.findSubst = Expr.prototype.matchSchema;

/**
 * Subfree function as a method on the target.
 */
Expr.prototype.subFree = function(replacement, vbl) {
  return subFree(replacement, vbl, this);
};

var _assertionCounter = 1;

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
 * proof steps.  Makes only a shallow copy of the step-related parts.
 */
Expr.prototype.copyStep = function() {
  var expr = this.copy();
  expr.details = this.details;
  expr.ruleName = this.ruleName;
  // Some elements of ruleArgs may refer to originals of other steps.
  expr.ruleArgs = this.ruleArgs;
  // ruleDeps refers to originals of other steps.
  expr.ruleDeps = this.ruleDeps;
  expr.ordinal = this.ordinal;
  expr.hasHyps = this.hasHyps;
  return expr;
};

/**
 * Finds and returns a Map of free names in this expression, from name
 * to true.
 */
Expr.prototype.freeNames = function() {
  var byName = {};
  this._addFreeNames(byName, null);
  return byName;
};

/**
 * Finds and returns a Map of the free variable names in this
 * expression, from the name to "true".  Uses the fact that variables
 * are distinguished from constants by their names.
 */
Expr.prototype.freeVars = function() {
  var byName = this.freeNames();
  for (var name in byName) {
    if (isConstant(name)) {
      delete byName[name];
    }
  }
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
 * Finds and returns a set of all the names bound in this expression
 * at the location given by the path, represented by a Map from names
 * to true.
 */
Expr.prototype.boundNames = function(path) {
  path = Y.path(path);
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
  if (this instanceof Y.Call) {
    return (this.fn instanceof Y.Var &&
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
  if (this instanceof Y.Call) {
    var left = this.fn;
    return left instanceof Y.Call
      && left.fn instanceof Y.Var
      && (name == null || left.fn.name == name);
  } else {
    return false;
  }
}

/**
 * True iff this is a call to a lambda expression.
 */
Expr.prototype.isOpenCall = function() {
  return this instanceof Call && this.fn instanceof Lambda;
};

/**
 * Throw an error with message if this is not a call to the named
 * function.  If no name is given, any named function will do.
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
    '-->': 'an implication',
    '=': 'an equation',
    '&&': 'a conjunction',
    '||': 'a disjunction'
  };
  var message;
  if (name == null) {
    message = 'Not a call to a a named 2-argument function';
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
  // A property only proof steps have.
  return !!this.ruleName;
};

/**
 * Renders this (renderable copy of an original) expression into a new
 * YUI node, returning the node.  The optional boolean "omit" argument
 * if true no parentheses are rendered if expr is a Call.
 *
 * TODO: Consider fleshing out the concept of display with fewer
 * parentheses.
 *
 * TODO: When displaying hypotheses, somehow properly distinguish
 * hypotheses that come from within the current subproof versus those
 * that come from outside.
 */
Expr.prototype.render = function(omit) {
  var step = this;
  if (this.hasHyps) {
    // Note that only top-level expressions can have hypotheses.
    var wffNode = step.node = exprNode();
    // Walk through the _original_ LHS.  This code might mirror the
    // intent a bit more closely by specifically walking down through
    // calls to '&&' rather than all subexpressions.
    function renderHyps(expr) {
      if (expr.sourceStep) {
        var source = expr.sourceStep;
        var node = expr.node = exprNode();
        if (source == step) {
          // This step does not yet have its rendering set.
          node.append(step.stepNumber);
        } else {
          node.append(expr.sourceStep.rendering.stepNumber);
        }
        wffNode.append(node);
      } else if (expr.isCall2('&&')) {
        renderHyps(expr.getLeft());
        wffNode.append(textNode(', '));
        var rhs = expr.getRight();
        if (rhs.isCall2('&&')) {
          wffNode.append(textNode('('));
          renderHyps(rhs);
          wffNode.append(textNode(')'));
        } else {
          renderHyps(rhs);
        }
      } else {
        wffNode.append(expr._render(true));
      }
    }
    renderHyps(step.getLeft());
    wffNode.append(textNode(' ' + _turnstile + ' '));
    wffNode.append(step.getRight()._render(true));
    return wffNode;
  } else {
    return this._render(omit);
  }
};

// String containing just the turnstile math character.  See
// http://tlt.its.psu.edu/suggestions/international/bylanguage/mathchart.html
var _turnstile = Y.Node.create('&#8870;').get('text');

/**
 * Searches for a subexpression of this that passes the test, given as
 * a boolean function of one argument.  Returns a path from this to
 * the occurrence, or null if none found.  Tests this expression
 * first, followed by the rest in top-down left-to-right order.
 * Does not search for variable bindings, use pathToBinding instead.
 * Alternatively accepts a term to be matched.
 */
Expr.prototype.pathTo = function(pred) {
  if (pred instanceof Expr) {
    var target = pred;
    pred = function(term) { return target.matches(term); };
  }
  var revPath = this._path(pred, path('/'));
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

/**
 * Searches in this for a variable binding that passes the test, given
 * as a boolean function of one argument.  Returns a path from this to
 * the Lambda containing the occurrence, or null if none found.  Tests
 * this expression first, followed by the rest in top-down
 * left-to-right order.
 * Alternatively accepts a term to be matched.
 */
Expr.prototype.pathToBinding = function(pred) {
  if (pred instanceof Expr) {
    var target = pred;
    pred = function(term) { return target.matches(term); };
  }
  var revPath = this._bindingPath(pred, path('/'));
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
          || (this.isCall2('&&')
              && this.getLeft().isHypotheses()
              && this.getRight().isHypotheses()));
};

/**
 * Treating this as a chain of hypotheses hk && h(k-1) && ... h1,
 * given an expression that matches one of the hypotheses in the set,
 * builds an expression where "h" is in the position of the matched
 * hypotheses, and the rest are labeled hk ... h1 according to their
 * position from the right.  Helper for rules.extractHypothesis.
 */
Expr.prototype.hypLocater = function(hyp) {
  var h = new Var('h');
  // Note: positions start with 1 at the right end of the chain.
  function locater(self, pos) {
    if (hyp.matches(self)) {
      return h;
    } else if (self.sourceStep || !self.isCall2('&&')) {
      return new Var('h' + pos);
    } else {
      // Self is a conjunction.
      var right = locater(self.getRight(), pos);
      assert(right instanceof Var, function() {
          return 'Internal error, not a Var: ' + right;
        });
      var left = (right == h
                  ? new Var('h' + (pos + 1))
                  : locater(self.getLeft(), pos + 1));
      return new Y.infixCall(left, '&&', right);
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
 * In other words this generates a tautology that works with
 * rules.rewrite to merge chain elements matching toMove and put an
 * occurrence of toMove at the right end of the chain.
 */
Expr.prototype.hypMover = function(toMove) {
  var i = 1;
  var lhs = null;
  var rhs = null;
  var found = false;
  this.eachHyp(function(term) {
      var h;
      if (term.matches(toMove)) {
        h = new Var('h');
        found = true;
      } else {
        h = new Var('h' + i);
        rhs = rhs ? Y.infixCall(rhs, '&&', h) : h;
      }
      lhs = lhs ? Y.infixCall(lhs, '&&', h) : h;
      i++;
    });
  if (found) {
    rhs = rhs ? Y.infixCall(rhs, '&&', new Var('h')) : new Var('h');
  }
  return Y.infixCall(lhs, '=', rhs);
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
    } else if (expr.isCall2('&&')) {
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
 */
Expr.prototype.eachHyp = function(action) {
  if (this.sourceStep) {
    action(this);
  } else if (this.isCall2('&&')) {
    this.getLeft().eachHyp(action);
    action(this.getRight());
  } else {
    action(this);
  }
};

/**
 * Given an expression that is the conjunction of two chains of
 * hypotheses, returns an equation that is a tautology that can
 * rewrite it to one with the conjunctions merged.
 */
Expr.prototype.mergedHypotheses = function() {
  this.assertCall2('&&');
  // Will be a list of all conjuncts in order from left to right.
  var conjuncts = [];
  var i = 1;
  function add(term) {
    conjuncts.push(term);
    if (!term.__var) {
      term.__var = new Var('a' + i++);
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
  Y.Array.each(sorted, function(term) {
      rhs = rhs ? Y.infixCall(rhs, '&&', term.__var) : term.__var;
    });

  var left = this.getLeft()._asPattern();
  var right = this.getRight()._asPattern();
  var result = Y.infixCall(Y.infixCall(left, '&&', right), '=', rhs);
  Y.Array.each(conjuncts, function(term) {
      delete term.__var;
      delete term.__order;
    });
  return result;
};


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
// _subFree(Expr replacement, String name, Map freeNames, Map allNames)
//
// Substitutes the replacement expression for all free occurrences of
// name in this Expr, renaming bound variables in just the locations
// where a binding would capture a free variable of the replacement.
//
// Assumes freeNames is a Set (Object) of all the names free in the
// replacement, that allNames contains all names occurring anywhere in
// this and the replacement.
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
// defined by the Var, Lambda, and Call classes.  The result is not
// flagged as having hypotheses.
//
//
// hasFree(name)
// 
// True iff the given name (string) appears free in this expression.
// Does not match against pnames.
//
//
// _addNames(Map result)
//
// Adds all names occurring in this expression to the Map, with value
// of true for each, both free and bound names.  Private.
//
//
// _addFreeNames(Map result, Bindings bindings)
// 
// Adds all names that occur free in this Expr to the result object,
// with the Var object as the value associated with each name found.
// Assumes that names in the Bindings object are bound in this
// expression's lexical context.  Private helper for the freeNames
// method.  Does not add names of constants, as they will never be
// bound anywhere.  TODO: Consider including constants.
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
// Furthermore there is only one binding with any given name within
// the normalized expression, and none of these names clashes with the
// name of any free variable.
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
// Tests whether all components of this expression and e2 are the same
// except for names of bound variables.  Names of constants and free
// variables must match in each component.  The bindings map from
// names of variables bound in expressions containing this expression
// to corresponding variable names of the expression containing e2.
// Type of this and type of e2 and all corresponding components much
// match, as determined by instanceof.
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
//
// _bindingPath(pred, revPath)
//
// Searches for a subexpression of this that passes the test and is a
// variable binding.  Returns the "reverse path" from this to its
// containing Lambda, with the last path segment first, added to the
// given revPath.
// 
//
// generalizeTF(expr2, newVar)
//
// Searches through this and expr2 for subexpressions in this that are
// the constant T, and F at the same place in expr2.  Returns an
// expression similar to this, but with newVar in those locations.
// Throws an error unless this and expr2 have the same syntax tree
// structure and variable names match everywhere except the T/F cases.
// The newVar should not appear anywhere in this or expr2, to ensure
// that the result will have this and expr2 as substitution instances.
//
// 
// _render(omit)
//
// Render this expression into a new YUI node, returning the node.
// Sets the expression's "node" property to refer to the node created
// to enclose this expression.  Should be done only once to any given
// expression.  Helper for the render method.  (Not public)
//
// If the optional "omit" argument is true and this is a Call, omit
// the enclosing parentheses.
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


//// Var -- variable bindings and references

//// A Var object can represent a variable (free or bound) or a
//// constant (see isConstant).

/**
 * Make a Var with the given name.  If a non-null integer position is given,
 * use it to record the index in the input stream.  If the given name
 * is in the "aliases" map, the given name becomes the Var's pname,
 * and the Var's name becomes the value of the alias.  Pnames affect
 * only parsing and display, not the logic itself.  If the name
 * represents an integer, sets the "value" property to that integer.
 */
function Var(name, position) {
  this.sort = Expr.var;
  if (aliases.hasOwnProperty(name)) {
    this.pname = name;
    this.name = aliases[name];
  } else {
    this.name = name;
    if (isIntegerLiteral(name)) {
      this.value = parseInt(name);
    }
  }
  if (position != null) {
    this.pos = position;
  }
};
Y.extend(Var, Expr);

Y.displayVarTypes = false;

Var.prototype._toString = function() {
  if (Y.displayVarTypes && this.type) {
    return (this.pname || this.name) + ':' + this.type;
  } else {
    return (this.pname || this.name);
  }
};

Var.prototype.dump = function() {
  return this.pname || this.name;
}

Var.prototype.subst = function(replacement, name) {
  return (name == this.name ? replacement : this);
};

Var.prototype._subFree = function(replacement, name, freeNames, allNames) {
  return (name == this.name ? replacement : this);
};

Var.prototype.copy = function() {
  var result = new Var(this.pname || this.name);
  result.sourceStep = this.sourceStep;
  return result;
};

Var.prototype.dup = function() {
  return new Var(this.pname || this.name);
};

Var.prototype.hasFree = function(name) {
  return this.name == name;
};

Var.prototype._addNames = function(map) {
  map[this.name] = true;
};

Var.prototype._addFreeNames = function(map, bindings) {
  if (this.isVariable() && getBinding(this.name, bindings) == null) {
    map[this.name] = true;
  }
};

Var.prototype._boundNames = function(path, bindings) {
  return path.isMatch() ? [bindings] : false;
};

Var.prototype._decapture = function(freeNames, allNames, bindings) {
  // This does not account for pnames, but they should only be for constants.
  var newName = getBinding(this.name, bindings);
  return newName ? new Var(newName) : this;
};

Var.prototype._addMathVars = function(bindings, set) {
  return false;
};

Var.prototype.normalized = function(counter, bindings) {
  return new Var(getBinding(this.name, bindings) || this.name);
};

Var.prototype.replace = function(path, xformer) {
  return path.isMatch() ? xformer(this) : this;
};

Var.prototype._locate = function(path) {
  return path.isMatch() ? this : null;
};

Var.prototype.matches = function(expr, bindings) {
  if (expr == this) {
    return true;
  }
  if (expr instanceof Var) {
    var expectedName = getBinding(this.name, bindings) || this.name;
    return expr.name == expectedName;
  } else {
    return false;
  }
};

Var.prototype.search = function(pred, bindings) {
  var result = pred(this) ? this : null;
  return result;
};

Var.prototype.generalizeTF = function(expr2, newVar) {
  if (!(expr2 instanceof Var)) {
    throw new Error('Not a variable: ' + expr2);
  }
  var name1 = this.name;
  var name2 = expr2.name;
  if (name1 == 'T' && name2 == 'F') {
    return newVar;
  } else if (name1 == name2) {
    return this;
  } else {
    throw new Error('Mismatched names: ' + name1 + ', ' + name2);
  }
};

Var.prototype._path = function(pred, revPath) {
  return pred(this) ? revPath : null;
};

Var.prototype._bindingPath = function(pred, revPath) {
  return null;
};

Var.prototype._render = function(omit) {
  var node = this.node = exprNode();
  var name = this.pname || this.name;
  node.append(entities[name] || name);
  return node;
};

Var.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.name == name) {
    action1(this);
    action2(expr2);
  }
};

Var.prototype._matchAsSchema = function(expr, map) {
  // This method does not return true when matching a defined name with an
  // expression that matches its definition.  It is a stricter criterion than
  // would be treating definitions exactly as abbreviations.
  if (this.isConst()) {
    // Expr must be a Var with the same name.
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

Var.prototype._asPattern = function(term) {
  return this.__var || this;
};


//// Call -- application of a function to an argument

function Call(fn, arg) {
  this.sort = Expr.call;
  this.fn = fn;
  this.arg = arg;
}
Y.extend(Call, Expr);

Call.prototype._toString = function() {
  if (this._string) {
    return this._string;
  }
  function asArg(expr) {
    if (expr instanceof Y.Var && isInfixDesired(expr)) {
      return '(' + expr + ')';
    } else {
      return expr.toString();
    }
  }
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    if (isInfixDesired(this.fn.fn)) {
      return '(' + this.fn.arg + ' ' + this.fn.fn + ' ' + this.arg + ')';
    } else {
      return '(' + this.fn.fn + ' ' + asArg(this.fn.arg) + ' ' + this.arg + ')';
    }
  } else if (this.fn instanceof Var && isInfixDesired(this.fn)) {
    return '(' + this.arg + ' ' + this.fn + ')';
  } else {
    return '(' + this.fn + ' ' + asArg(this.arg) + ')';
  }
};

Call.prototype.dump = function() {
  return '(' + this.fn.dump() + ' ' + this.arg.dump() + ')';
};

Call.prototype.subst = function(replacement, name) {
  var fn = this.fn.subst(replacement, name);
  var arg = this.arg.subst(replacement, name);
  return (fn == this.fn && arg == this.arg
          ? this
          : new Call(fn, arg));
};

Call.prototype._subFree = function(replacement, name, freeNames, allNames) {
  var fn = this.fn._subFree(replacement, name, freeNames, allNames);
  var arg = this.arg._subFree(replacement, name, freeNames, allNames);
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

Call.prototype.hasFree = function(name) {
  return this.fn.hasFree(name) || this.arg.hasFree(name);
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
    return (this.fn._boundNames(path.rest('fn'), bindings)
            || this.arg._boundNames(path.rest('arg'), bindings));
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

Call.prototype.normalized = function(counter, bindings) {
  return new Call(this.fn.normalized(counter, bindings),
                  this.arg.normalized(counter, bindings));
};

Call.prototype.replace = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else if (path.segment) {
    // Traversing down to a subexpression of this.
    var fn = this.fn.replace(path.rest('fn'), xformer);
    var arg = this.arg.replace(path.rest('arg'), xformer);
    return (fn == this.fn && arg == this.arg) ? this : new Call(fn, arg);
  } else {
    return this;
  }
};

Call.prototype._locate = function(path) {
  if (path.isMatch()) {
    return this;
  } else {
    return (this.fn._locate(path.rest('fn'))
            || this.arg._locate(path.rest('arg')));
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

Call.prototype.search = function(pred, bindings) {
  var result = pred(this)
    ? this
    : this.fn.search(pred, bindings) || this.arg.search(pred, bindings);
  return result;
};

Call.prototype.generalizeTF = function(expr2, newVar) {
  if (!(expr2 instanceof Call)) {
    throw new Error('Not a Call: ' + expr2);
  }
  var fn = this.fn.generalizeTF(expr2.fn, newVar);
  var arg = this.arg.generalizeTF(expr2.arg, newVar);
  return (fn == this.fn && arg == this.arg) ? this : new Call(fn, arg);
};

Call.prototype._path = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.fn._path(pred, new Path('fn', revPath))
      || this.arg._path(pred, new Path('arg', revPath));
};

Call.prototype._bindingPath = function(pred, revPath) {
  return (this.fn._bindingPath(pred, new Path('fn', revPath))
          || this.arg._bindingPath(pred, new Path('arg', revPath)));
};

Call.prototype._render = function(omit) {
  var node = this.node = exprNode();
  var stepNum = (Y.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  omit = omit && !stepNum;
  if (!omit) {
    if (Y.trackSourceSteps) {
      if (this.sourceStep) {
        node.append('$');
      }
      if (stepNum) {
        node.append(stepNum);
      }
    }
    node.append('(');
  }
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    // This is a call on a named function of two arguments.
    if (isInfixDesired(this.fn.fn)) {
      // Non-alphabetic characters: use infix: "x + y"
      var fnNode = this.fn.node = exprNode();
      fnNode.append(this.fn.arg._render());
      fnNode.append(space());
      fnNode.append(this.fn.fn._render());
      node.append(fnNode);
      node.append(space());
      node.append(this.arg._render());
    } else {
      // Alphabetic characters: function comes first.
      var fnNode = this.fn.node = exprNode();
      fnNode.append(this.fn.fn._render());
      fnNode.append(space());
      fnNode.append(this.fn.arg._render());
      node.append(fnNode);
      node.append(space());
      node.append(this.arg._render());
    }
  } else if (this.fn instanceof Var && isInfixDesired(this.fn)) {
    // Infix operator, but only one argument: "x +"
    node.append(this.arg._render());
    node.append(space());
    node.append(this.fn._render());
  } else {
    // Normal function call: "f x"
    node.append(this.fn._render());
    node.append(space());
    node.append(this.arg._render());
  }
  if (!omit) {
    node.append(')');
  }
  return node;
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

Lambda.prototype._toString = function() {
  if (this._string) {
    return this._string;
  }
  return '{' + this.bound + '. ' + this.body + '}';
};

Lambda.prototype.dump = function() {
  return '{' + this.bound.dump() + '. ' + this.body.dump() + '}';
};

Lambda.prototype.subst = function(replacement, name) {
  if (this.bound.name != name) {
    var body = this.body.subst(replacement, name);
    return (body == this.body
            ? this
            : new Lambda(this.bound, body));
  } else {
    return this;
  }
};

Lambda.prototype._subFree = function(replacement, name, freeNames, allNames) {
  if (this.bound.name == name) {
    // Binds the name; there can be no free occurrences here.
    return this;
  } else {
    var newVar = genVar(name, allNames);
    var body = this.body._subFree(replacement, name, freeNames, allNames);
    if (body == this.body) {
      return this;
    } else if (freeNames.hasOwnProperty(this.bound.name)) {
      // Consider decapturing.
      // 
      // Decapturing is only needed when the bound name is among the
      // free variables of the replacement _and_ the name to be replaced
      // occurs in this.
      // 
      // Note that bound.name is known to be different than the name
      // to be replaced, see above.  So the new body has all of the
      // original free occurrences of bound.name.  It may have some
      // more, but they are inside occurrences of the replacement and
      // we can detect occurrences of the replacement, so we can go
      // back now and decapture after doing the substitution, renaming
      // except inside the replacement.
      body = body._renameFree(this.bound.name, newVar, replacement);
      return (body == this.body) ? this : new Lambda(newVar, body);
    } else {
      // Not a binding of a free variable, just return with the body
      // already computed.
      return new Lambda(this.bound, body);
    }
  }
};

// Etc.

Lambda.prototype.copy = function() {
  var result = new Lambda(this.bound.copy(), this.body.copy());
  result.sourcestep = this.sourceStep;
  return result;
};

Lambda.prototype.dup = function() {
  return new Lambda(this.bound, this.body);
};

Lambda.prototype.hasFree = function(name) {
  return this.bound.name != name && this.body.hasFree(name);
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
  return (body == this.body) ? this : new Lambda(new Var(newName), body);
};

Lambda.prototype._addMathVars = function(bindings, set) {
  this.body._addMathVars(new Bindings(this.bound.name, true, bindings), set);
  return false;
};

Lambda.prototype.normalized = function(counter, bindings) {
  var newVar = new Var('$' + counter.next());
  var newBindings = new Bindings(this.bound.name, newVar.name, bindings);
  return new Lambda(newVar, this.body.normalized(counter, newBindings));
};

Lambda.prototype.replace = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else {
    var body = this.body.replace(path.rest('body'), xformer);
    return (body == this.body) ? this : new Lambda(this.bound, body);
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

Lambda.prototype.search = function(pred, bindings) {
  var result = pred(this)
    ? this
    : ((bindings && this.bound.search(pred, bindings))
       || this.body.search(pred, bindings));
  return result;
};

Lambda.prototype.generalizeTF = function(expr2, newVar) {
  if (!(expr2 instanceof Lambda)) {
    throw new Error('Not a variable binding: ' + expr2);
  }
  if (this.bound.name != expr2.bound.name) {
    throw new Error('Differing bindings: ' + this.bound.name
                    + ', ' + expr2.bound.name);
  }
  var body = this.body.generalizeTF(expr2.body, newVar);
  return (body == this.body) ? this : new Lambda(this.bound, body);
};

Lambda.prototype._path = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.body._path(pred, new Path('body', revPath));
};

Lambda.prototype._bindingPath = function(pred, revPath) {
  return (pred(this.bound)
          ? revPath
          : this.body._bindingPath(pred, new Path('body', revPath)));
};

Lambda.prototype._render = function(omit) {
  var node = this.node = exprNode();
  var stepNum = (Y.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  if (stepNum) {
    node.append('$' + stepNum);
  }
  node.append('{');
  node.append(this.bound._render());
  node.append(textNode('. '));
  node.append(this.body._render(true));
  node.append('}');
  return node;
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
  return this.__var || new Lambda(this.bound, this.body._asPattern());
};

// Private methods grouped by name.

// Traverse this, replacing occurrences of target with replacement.
// (As used they are duplicates anyway.)
//
// Private to subFree.
Var.prototype._smashAll = function(target, replacement) {
};

Call.prototype._smashAll = function(target, replacement) {
  if (this.fn == target) {
    this.fn = replacement;
  } else {
    this.fn._smashAll(target, replacement);
  }
  if (this.arg == target) {
    this.arg = replacement;
  } else {
    this.arg._smashAll(target, replacement);
  }
};

Lambda.prototype._smashAll = function(target, replacement) {
  if (this.body == target) {
    this.body = replacement;
  } else {
    this.body._smashAll(target, replacement);
  }
};

// Rename all free occurrences of variables having the given name,
// replacing each of them with variable newVar, but do not rename
// within occurrences expressions identical to "replacement", which is
// already a substitution result.  So this relies on the substitution
// to _not_ copy the replacement expression.  Helper method for
// _subFree.
Var.prototype._renameFree = function(name, newVar, replacement) {
  return (this == replacement
          ? this
          : (this.name == name ? newVar : this));
};

Call.prototype._renameFree = function(name, newVar, replacement) {
  if (this == replacement) {
    return this;
  }
  var fn = this.fn._renameFree(name, newVar, replacement);
  var arg = this.arg._renameFree(name, newVar, replacement);
  return (fn == this.fn && arg == this.arg) ? this : new Call(fn, arg);
};

Lambda.prototype._renameFree = function(name, newVar, replacement) {
  if (this == replacement || this.bound.name == name) {
    return this;
  }
  var body = this.body._renameFree(name, newVar, replacement);
  return (body == this.body) ? this : new Lambda(this.bound, body);
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
 * or an array of strings, or a Bindings.  The parts become the
 * segments of the path.  Some segments serve as macros that expand
 * into a list of other segments, currently 'left', 'right', and
 * 'binop'.
 *
 * If the optional expr is supplied, adjust any /main path according
 * to whether the expr has hypotheses or not.
 *
 * A null input is treated as '/'.
 */
function path(arg, opt_expr) {
  var expr = opt_expr;
  // If the initial segment of the path is 'main', and the expression
  // is given and has hypotheses, return a path to its RHS.
  function adjust(path) {
    if (!expr) {
      return path;
    }
    if (path.segment == 'main') {
      path = path._rest;
      if (expr.hasHyps) {
        // TODO: Modify this when infix changes.
        path = new Path('arg', path);
      }
    }
    return path;
  }
  if (arg instanceof Path) {
    return adjust(arg);
  }
  if (arg == null) {
    arg = '/';
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
  // Handle the result of splitting '/' --> ['', '']:
  if (segments.length == 1 && segments[0] == '') {
    segments = [];
  }
  // TODO: Intrepret these directly rather than making them macros.
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
  result = adjust(result);
  return result;
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


//// TYPES

var _counter = 1;

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
    this.name = 't' + _counter++;
  }
}

TypeVariable.prototype.copy = function() {
  var tp = dereference(this);
  if (tp instanceof TypeVariable) {
    return tp;
  } else if (tp instanceof TypeOperator) {
    return tp.copy();
  } else {
    throw new Error('Not a type expression: ' + tp);
  }
}

TypeVariable.prototype.toString = function() {
  return this.instance ? this.instance.toString() : this.name;
}

/**
 * TypeOperator constructor, types is an optional array of type
 * parameters, if not given, then an empty array.
 */
function TypeOperator(name, types) {
  this.name = name;
  this.types = types || [];
}

TypeOperator.prototype.copy = function() {
    var list = [];
    for (var i = 0; i < this.types.length; i++) {
      list.push(this.types[i].copy());
    }
    return new TypeOperator(this.name, list);
}

TypeOperator.prototype.toString = function() {
  var numTypes = this.types.length;
  return numTypes == 0
    ? this.name
    : numTypes == 2
    ? '(' + [this.types[0], this.name, this.types[1]].join(' ') + ')'
    : '(' + this.name + ' ' + this.types.join(' ') + ')';
}

function FunctionType(fromType, toType) {
  TypeOperator.call(this, '->', [fromType, toType]);
  this.types = [fromType, toType];
}
Y.extend(FunctionType, TypeOperator);

FunctionType.prototype.copy = function() {
  var list = [];
  for (var i = 0; i < this.types.length; i++) {
    list.push(this.types[i].copy());
  }
  return new FunctionType(this.name, list);
};

FunctionType.prototype.toString = function() {
  return '(' + this.types[1] + ' ' + this.types[0] + ')';
};

var individual = new TypeOperator('i');
var boolean = new TypeOperator('o');

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
  '&&': booleanBinOpType(),
  '||': booleanBinOpType(),
  '-->': booleanBinOpType()
};

// Indexed by the name defined.  Value is an expression if
// the definition is simple.  If by cases, the value is a
// map from 'T' and 'F' to the definition for each case.
//
// Primitive constants are here, but the definitions are truthy fakes.
var definitions = {
  T: true,
  F: true,
  '=': true,
  the: true
};

/**
 * Check that the given value is numeric, raise an error if not,
 * return the value if it is.
 */
function checkNumber(number) {
  assert(typeof number === 'number', function() {
      return 'Not a number: ' + number;
    });
  return number;
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
 * Add a simple abbreviation-like definition, e.g.
 * define('forall', equal(lambda(x, T))).  Returns the equation.
 */
function define(name, definition) {
  assert(isConstant(name), 'Not a constant name: ' + name);
  definition = typeof definition == 'string' ? Y.parse(definition) : definition;
  assert(definition instanceof Expr,
         'Definition must be a term: ' + definition);
  if (isDefined(name)) {
    assert(definition.matches(getDefinition(name)),
           'Already defined: ' + name);
    // Benign redefinition, do nothing.
    return;
  }
  for (var n in definition.freeNames()) {
    assert(isDefined(n), 'Definition has free variables: ' + name);
  }
  return definitions[name] = equal(name, definition);
}

/**
 * Add a simple definition with true/false cases.  A call could
 * be something like defineCases('not', F, T).
 */
function defineCases(name, ifTrue, ifFalse) {
  assert(isConstant(name), 'Not a constant name: ' + name);
  assert(!definitions.hasOwnProperty(name), 'Already defined: ' + name);
  for (var n in ifTrue.freeNames()) {
    assert(isDefined(n), 'Definition has free variables: ' + name);
  }
  for (var n in ifFalse.freeNames()) {
    assert(isDefined(n), 'Definition has free variables: ' + name);
    // Assumes constants do not appear in freeNames.
  }
  definitions[name] = {T: equal(call(name, T), ifTrue),
                       F: equal(call(name, F), ifFalse)};
}

/**
 * Returns whether the name (or Var) currently has a definition.
 */
function isDefined(name) {
  if (name instanceof Y.Var) {
    name = name.name;
  }
  assert(typeof name == 'string', function() {
      return 'Non-string name: ' + name;
    });
  return definitions.hasOwnProperty(name);
}

/**
 * Returns whether the name (or Var) currently has a definition by
 * cases.
 */
function isDefinedByCases(name) {
  if (name instanceof Y.Var) {
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
 * accepts a Var.
 */
function findDefinition(name, tOrF) {
  name = name instanceof Var ? name.name : name;
  var defn = definitions[name];
  if (!tOrF) {
    assert(defn instanceof Y.Expr, 'Definition is not simple: ' + name);
    return defn;
  } else {
    if (tOrF == true || (tOrF instanceof Y.Var && tOrF.name == 'T')) {
      tOrF = 'T';
    } else if (tOrF == false || (tOrF instanceof Y.Var && tOrF.name == 'F')) {
      tOrF = 'F';
    }
    assert(!(defn instanceof Y.Expr),
             'Definition is not by cases: ' + name);
    var defnCase = defn[tOrF];
    assert(defnCase, 'Not defined: ' + name + ' ' + tOrF);
    return defnCase;
  }
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
 * Find and return the type of an expression (Expr).  As a side effect
 * this also records the type of every subexpression as its "type"
 * property.
 */
function findType(expr) {
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

  // This is the core of the type inference algorithm.
  function analyze1(expr) {
    if (expr.type) {
      return expr.type;
    } else if (expr instanceof Var) {
      return getType(expr.name);
    } else if (expr instanceof Call) {
      var fnType = analyze1(expr.fn);
      var argType = analyze1(expr.arg);
      var resultType = new TypeVariable();
      unifyTypes(new FunctionType(argType, resultType), fnType);
      return resultType;
    } else if (expr instanceof Lambda) {
      vars.push(expr.bound.name);
      // TODO: Handle explicit type info on the bound variable.
      var argType = new TypeVariable();
      types.push(argType);
      nonGenerics.push(argType);
      var resultType = analyze1(expr.body);
      vars.pop();
      types.pop();
      nonGenerics.pop();
      return new FunctionType(argType, resultType);
    }
    throw new Error('Expression of unknown type: ' + expr);
  }

  function getType(name) {
    if (isIntegerLiteral(name)) {
      // I say integers are individuals.
      return individual;
    }
    // Is it a bound or (already-seen) free variable?
    for (var i = vars.length - 1; i >= 0; --i) {
      if (vars[i] == name) {
        var type = types[i];
        // Return a fresh instance of the variable's type.
        return fresh(type);
      }
    }
    if (isConstant(name)) {
      return fresh(lookupType(name));
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
  function fresh(type) {
    // Maps TypeVariable names to TypeVariables.
    var mappings = {};

    function fresh1(tp) {
      var type = dereference(tp);
      if (type instanceof TypeVariable) {
        var name = type.name;
        if (isGeneric(name)) {
          if (!mappings.hasOwnProperty(name)) {
            mappings[name] = new TypeVariable();
          }
          return mappings[name];
        } else {
          return type;
        }
      } else if (type instanceof TypeOperator) {
        var ptypes = type.types;
        var freshTypes = [];
        for (var i = 0; i < ptypes.length; i++) {
          freshTypes.push(fresh1(ptypes[i]));
        }
        if (type instanceof FunctionType) {
          return new FunctionType(freshTypes[0], freshTypes[1]);
        } else {
          // Implementation note: this does not specialize by type.
          // TODO: Make "fresh" into a method.
          return new TypeOperator(type.name, freshTypes);
        }
      } else {
        throw new Error('Bad type: ' + type);
      }
    }

    return fresh1(type);
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
      throw new Error('Cannot find type for: ' + name);
    }
  }

  function isGeneric(v) {
    return !occursInList(v, nonGenerics);
  }

  return analyze1(expr);
}

function isIntegerLiteral(name) {
  return name.match(/^-?[0-9]+$/);
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
        throw new TypeError('recursive unification');
      }
      a.instance = b;
    }
  } else if (a instanceof TypeOperator && b instanceof TypeVariable) {
    unifyTypes(b, a);
  } else if (a instanceof TypeOperator && b instanceof TypeOperator) {
    if (a.name != b.name || a.types.length != b.types.length) {
      throw new TypeError('Type mismatch: ' + a + ' != ' + b);
    }
    for (var i = 0; i < a.types.length; i++) {
      unifyTypes(a.types[i], b.types[i]);
    }
  } else {
    throw new Error('Not unifieable');
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


//// PARSING

// Tokens pattern, private to tokenize.
  var _tokens = new RegExp(['[(){}\\[\\]]',
                          '_?[:a-zA-Z][:a-zA-Z0-9]*',
                          '-?[0-9]+',
                          '[^_:a-zA-Z0-9(){}\\s]+'].join('|'),
                         'g');

/**
 * A token is a parenthesis or brace, or a sequence of characters
 * starting with an alphabetic (possibly preceded by an underscore
 * ("_"), followed by zero or more characters that are alphanumeric or
 * ":", or a sequence containing none of these and no whitespace.
 * 
 * This returns an array of tokens in the input string, followed by an
 * "(end)" token, omitting whitespace.  All tokens are Var objects
 * with the text of the token as its name and its index in the input
 * as its "pos" property.
 */
function tokenize(str) {
  var match;
  var result = [];
  while (match = _tokens.exec(str)) {
    result.push(new Y.Var(match[0], match.index));
  }
  result.push(new Y.Var('(end)', str.length));
  return result;
}

// Map from input strings to their parsed values.  Used for
// memoization of user inputs.
var _parsed = {};

/**
 * Parses a string or array of token strings into an expression
 * (Expr).  Removes tokens parsed from the tokens list.  Throws an
 * Error if parsing fails.
 */
function parse(input) {

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
   * Keep reducing leading parts into subtrees until the next token is
   * an infix operator with precedence not greater than lastPower.
   * Returns null if it consumes no input.  "Above" here means
   * numerically greater.
   */
  function parseAbove(lastPower) {
    // This is a top-down operator precedence parser.
    var left = null;
    while (true) {
      var token = peek();
      var nextPower = getPrecedence(token);
      if (nextPower != null && nextPower <= lastPower) {
        return left;
      }
      next();
      // If an atomic expression or unary/nullary expression is
      // next, this will have it.
      var expr = null;
      if (token.name == '(') {
        expr = mustParseAbove(0);
        expect(')');
      } else if (token.name == '{') {
        var id = next();
        assert(id.isVariable(), 'Expected identifier, got ' + id.name);
        expect('.');
        var body = mustParseAbove(0);
        expr = new Y.Lambda(id, body);
        expect('}');
      } else if (!left || nextPower == null) {
        // Treat the token as an atomic expression.
        expr = token;
      }
      // At this point expr and left are not both null.
      if (expr) {
        left = left ? new Y.Call(left, expr) : expr;
      } else {
        // Token is an infix operator of higher precedence than the last.
        // At this point there is always an expression in "left".
        left = new Y.Call(token, left);
        var right = parseAbove(nextPower);
        if (right) {
          left = new Y.Call(left, right);
        }
      }
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

  // Do the parse!

  if (typeof input == 'string') {
    if (_parsed.hasOwnProperty(input)) {
      return _parsed[input];
    }
    tokens = tokenize(input);
  }
  // The ending token.
  var end = tokens.pop();
  if (tokens.length < 1) {
    // There should be at least one real token.
    throw new Error('No parser input');
  }
  var result = parseAbove(0);
  if (typeof input == 'string') {
    _parsed[input] = result;
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
 * Is it an identifier or constant?  Currently Id or number as digits
 * with optional leading "-".
 */
function isIdOrLiteral(token) {
  return token instanceof Y.Var
    && !!token.name.match(/^-?[A-Za-z0-9$]+$/);
}

/**
 * Get a precedence value: null for symbols, defaults to 100 for
 * unknown non-symbols, greater than the usual math operators but less
 * than identifiers (i.e. ordinary function calls).
 *
 * Infix operators have precedence 0 < p < 1000.
 */
function getPrecedence(token) {
  var name = token.pname || token.name;
  if (precedence.hasOwnProperty(name)) {
    return precedence[name];
  } else {
    return isIdOrLiteral(token) ? null : 100;
  }
}

// Precedence table for infix operators.
var precedence = {
  // Closing tokens have power 0 to make infix parsing return.
  '(end)': 0,
  ')': 0,
  '}': 0,
  // Alias for '=', with lower precedence.
  '==': 2,
  // Default precedence for non-identifiers is 5.
  '-->': 11,
  '||': 13,
  '&&': 14,
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
  // Specials
  '(': 1000,
  '{': 1000
};

// Defines aliases that only affect printing and parsing.
var aliases = {
  // Note that limiting '==' to boolean inputs would make it more than
  // just an alias as currently defined.
  '==': '=',
};


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
 * Return the Var v, or if the argument is a string, create a new Var
 * from it.
 */
function varify(v) {
  return (typeof v == 'string') ? new Var(v) : v;
};

/**
 * Returns a call with the two operands and the given op (middle
 * argument) as the binary operator between them.  The op must be an
 * Expr, e.g. Var.
 */
function infixCall(arg1, op, arg2) {
  // TODO: Change this when redefining meaning of infix operators.
  op = varify(op);
  return new Call(new Call(op, arg1), arg2);
}

/**
 * This controls the policy over which function names are
 * to be rendered as infix.
 */
function isInfixDesired(vbl) {
  var name = vbl.pname || vbl.name;
  var p = getPrecedence(vbl);
  return typeof p == 'number' && 0 < p && p < 1000;
}

/**
 * True iff the source step of expr1 is less than the source step of
 * expr2, otherwise true iff dump(expr1) is lexicographically less
 * than dump(expr2).
 *
 * In use this is used in sorting of expressions, so it must bring
 * equal expressions together so simplifications can see them.
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
 * Comparator for Array.sort corresponding to sourceStepLess.
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
 * operator is a string or Var.  The indices must contain at least one
 * element.
 *
 * Useful for rearranging expressions containing operators that are
 * commutative and associative.
 */
function repeatedCall(operator, indices) {
  var op = (typeof operator == 'string') ? new Var(operator) : operator;
  function x(n) {
    return new Var('x' + indices[n]);
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
 * 
 * Caution: YUI already has a Y.assert function.
 */
function assertTrue(condition, message, step) {
  if (!condition) {
    if (typeof message == 'function') {
      message = message();
    }
    console.log(message);
    errors.push({message: message, step: step});
    throw new Error(message);
  }
}

// Use the application's assertTrue function for assertions.
var assert = assertTrue;

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


//// Convenience utilities

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

  // Converts a variable name into a new Var instance with
  // that name.  If "name" is already a Var returns it.
  _var: function(name) {
    return (name instanceof Var) ? name : new Y.Var(name);
  },

  // This calls a function with any number of arguments.
  // TODO: Eliminate in favor of infixCall.  This will be problematic
  // for some infix operators.
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
   * TODO: Order of args changes when infix changes.  Similarly for
   * implies and other infix operators.
   */
  equal: function(lhs, rhs) {
    if (rhs) {
      return call('=', lhs, rhs);
    } else {
      return call('=', lhs);
    }
  },

  /**
   * Builds an expression [lhs --> rhs].
   */
  implies: function(lhs, rhs) {
    return call('-->', lhs, rhs);
  },

  lambda: function(bound, body) {
    return new Y.Lambda(bound, body);
  },

  a: new Var('a'),
  b: new Var('b'),
  c: new Var('c'),
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

Y.textNode = textNode;

Y.Set = Set;
Y.Map = Map;
Y.TermSet = TermSet;
Y.TermMap = TermMap;

Y.Expr = Expr;
Y.Var = Var;
Y.Call = Call;
Y.Lambda = Lambda;
Y.Path = Path;

Y.subFree = subFree;
Y.genVar = genVar;
Y.normalized = normalized
Y.decapture = decapture;
Y.path = path;
Y.findBinding = findBinding;
Y.getBinding = getBinding;
Y.matchAsSchema = matchAsSchema;
Y.sourceStepLess = sourceStepLess;
Y.sourceStepComparator = sourceStepComparator;
Y.repeatedCall = repeatedCall;

Y.define = define;
Y.defineCases = defineCases;
Y.findDefinition = findDefinition;
Y.getDefinition = getDefinition;
// For testing:
Y.definitions = definitions;

Y.isConstant = isConstant;
Y.isVariable = isVariable;
Y.checkNumber = checkNumber;
Y.checkRange = checkRange;
Y.isDefined = isDefined;

Y.getStepCounter = getStepCounter;
Y.varify = varify;
Y.infixCall = infixCall;
Y.assertTrue = assertTrue;
Y.assertEqn = assertEqn;
Y.removeAll = removeAll;
Y.removeExcept = removeExcept;

// Error analysis
Y.errors = errors;

// Types

// Y.displayVarTypes -- a variable, declared previously.
Y.boolean = boolean;
Y.individual = individual;
Y.TypeVariable = TypeVariable;
Y.TypeOperator = TypeOperator;
Y.FunctionType = FunctionType;
Y.parseType = parseType;
Y.findType = findType;

// For testing:
Y._equalityType = equalityType;

Y.exprNode = exprNode;
Y.tokenize = tokenize;
Y.parse = parse;

Y.Expr.utils = utils;

// For debugging
Y.nParsed = nParsed;

}, '0.1', {requires: ['node', 'array-extras']});
