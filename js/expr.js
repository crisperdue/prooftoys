// Copyright 2011, 2012, 2013, 2014, 2015 Crispin Perdue.
// All rights reserved.

// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

var Path = Toy.Path;
var path = Toy.path;
var Bindings = Toy.Bindings;
var getBinding = Toy.getBinding;
var assert = Toy.assertTrue;
var Set = Toy.Set;
var Map = Toy.Map;

// Code in this file may reference xutil.js, but handle forward
// references properly.

// Forward references to xutil.js.
var termify;
var isInfixDesired;
var infixCall;
var parse;
var lambda;

// Resolve forward references after all code is loaded.  Note that
// jQuery handlers fire deterministically in order of attachment,
// which is important for our initializations.
$(function() {
    termify = Toy.termify;
    isInfixDesired = Toy.isInfixDesired;
    infixCall = Toy.infixCall;
    parse = Toy.parse;
    lambda = Toy.lambda;
  });


//// Assertions

/**
 * Asserts that the expression is an equation (must have
 * both left and right sides.
 */
function assertEqn(expr) {
  assert(expr instanceof Call
         && expr.fn instanceof Call
         && expr.fn.fn instanceof Atom
         && expr.fn.fn.name == '=',
         'Must be an equation: {1}', expr);
}

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
  var freeVars = replacement.freeVars();
  var allNames = {};
  replacement._addNames(allNames);
  target._addNames(allNames);
  // Now allNames contains every variable name occurring anywhere in
  // either expression.
  return target._decapture(freeVars, allNames, null);
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
// The current solution is that all transformations on expressions
// that leave a given subexpression the same return the identical
// subexpression object they were given.  This means that all
// operations that transform expressions must avoid copying except
// when necessary.  (Rendered copies are not relied on to maintain the
// sourceStep property.)
//
// Rules.appendStepHyps and rules.prependStepHyps also copy sourceStep
// properties down to resulting steps from their inputs where they
// match an input hypothesis and are not already flagged.
// 

/**
 * Superclass for terms of all kinds: Atom, Call, Lambda.
 * See internal comments for details.
 */
function Expr() {
  // Extensible set of remembered information, especially useful
  // since the result is conceptually immutable.
  // Duplicated in subclass constructors for speed.
  //
  this.sourceStep = null;
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
      && this.isCall2('==>')) {
    return (prefix + '(' + this.getLeft()._toString() + ' |- '
            + this.getRight()._toString() + ')');
  } else {
    return prefix + this._toString();
  }
};

/**
 * Converts this Expr to a string of Unicode and/or HTML.  The display
 * is currently just the same as plain text display except
 * names (or pnames) that have Unicode counterparts are presented as
 * Unicode and some cases of exponentiation use HTML.
 *
 * This is a bit of a misnomer right now.
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
 * Like toUnicode, but allows HTML output.  Currently
 * these are one and the same; toUnicode may disappear.
 */
Expr.prototype.toHtml = Expr.prototype.toUnicode;

/**
 * Tests if this is an Atom with name in the given list of strings.
 */
Expr.prototype.in = function(list) {
  return this instanceof Atom && list.indexOf(this.name) >= 0;
};

/**
 * Returns true iff this term is atomic (a variable or constant).
 */
Expr.prototype.isAtomic = function() {
  return this instanceof Atom;
};

/**
 * Truthy iff the given Expr (or step) is not only renderable,
 * but has a rendering.
 */
Expr.prototype.isRendered = function() {
  return !!this.node;
};

// Categorization of Atoms:
//
// Identifiers
//   Variables (start with a single lowercase ASCII letter)
//   Consts (such as sin, cos, forall, exists)
// Literals (numeric, string, etc)
// OpSyntax (+, -, etc)

// All "opSyntax" Vars are operators, plus some designated
// identifers, currently "forall" and "exists".

// Pattern that matches identifiers, used in the tokenizer and
// identifierRegex.  The tokenizer recognizes exactly things matching
// this as being identifiers.  The system can create identifers not
// matching this expression, but parses only these.  This in itself is
// not a regex.
var identifierPattern = '[_$a-zA-Z][_a-zA-Z0-9]*';

// Names matching this regex are identifiers.
// The trailing "$" ensures that the entire name is matched
// up to any extensions for unique ID and/or type information.
// Note that not all identifiers can be entered through the parser,
// in particular ones with "." (generated bound names) or ":"
// (for type information).
var identifierRegex = new RegExp('^' + identifierPattern + '([.:]|$)');

// Variables in particular, not including identifiers for constants.
// The "." and ":" provide for extension with bound variable unique
// identifiers and type signatures.
//
// TODO: Make variable naming and subscripting consistent and
// rational!  Currently variable names of a single alphabetic
// character are pretty good, but ones beginning with underscore
// are probably nonsensical.
var variableRegex = /^[$a-z][0-9_]*([.:]|$)|^_/;

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
  assert(typeof name == 'string', 
         'isVariable - name must be a string: {1}', name);
  return name.match(variableRegex);
}

/**
 * Any (legal) name that is not a variable is considered a constant, which
 * can be a named constant or literal constant.
 */
function isConstantName(name) {
  return !isVariableName(name);
}

/**
 * True iff this is an Atom named as a variable.
 */
Expr.prototype.isVariable = function() {
  return this instanceof Atom && this._value === undefined;
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
  if (!(this instanceof Atom) || this._value === undefined) {
    return false;
  }
  return opt_name ? this.name === opt_name : true;
};

// True iff the expression is a literal constant.
Expr.prototype.isLiteral = function() {
  // Value must be neither null nor undefined.
  return this instanceof Atom && this._value != null;
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
  var self = this;
  Toy.check(this.isNumeral(), function() {
      return 'Not a numeral: ' + self;
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
  Toy.check(Math.abs(number) <= MAX_INT,
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
  assert(this.isString(), 'Not a string literal: {1}', this);
  return this._value;
};

/**
 * This is a constant T or F.
 */
Expr.prototype.isBoolConst = function() {
  return (this instanceof Atom &&
          (this.name == 'T' || this.name == 'F'));
};


// Other Expr methods.

/**
 * Does this Expr have any variable(s)?
 */
Expr.prototype.hasVars = function() {
  var map = this.freeVars();
  return !Toy.isEmpty(map);
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
  return genVar(name, this.freeVars());
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
 * If this is identical to one of its ruleDeps, returns this unchanged
 * unless "retain" is true, making the step a no-op.  (The purpose is
 * to reduce clutter for readers of the proof.)
 *
 * TODO: Make a Step class for proof steps, and have this method
 * return a new one.
 *
 * TODO: Consider always recording the step, but skipping the display
 * in proof.jsc.  Some steps, especially simplifications, do this
 * same thing internally by skipping the call to "justify".
 */
Expr.prototype.justify = function(ruleName, ruleArgs, ruleDeps, retain) {
  // Note: when splitting Step and Expr, make a version of this just
  // for rules.assert, and use that in any primitive inference rules.
  var ruleDeps = jQuery.makeArray(ruleDeps || []);
  if (!retain) {
    for (var i = 0; i < ruleDeps.length; i++) {
      if (ruleDeps[i] == this) {
        // If the step returns an input step, return it as-is.
        // TODO: Consider eliminating this "optimization" and rely instead
        //   on eliding no-op steps from display.  (There is already an
        //   implementation.)
        return this;
      }
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
 * Matches the given "schematic" expression against this. Returns a
 * substitution that yields this expression when given the schema, or
 * null if there is none.  Assumes that the schema contains no
 * variable bindings.  The substitution maps from names to
 * expressions.  Tautologies for example qualify as schemas.
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
 * Attempts to match the given schema to a part of this, so the
 * variable in the schema with the given name matches the part of this
 * at the given path.
 *
 * If successful, returns a substitution with an extra "path" property
 * containing the path to the part of this that matches the entire
 * schema.  The rest of the substitution maps from names of schema
 * variables to subexpressions of this that match them.
 *
 * Assumes that the name only occurs once within the schema.
 *
 * The implementation idea is that the path to the part of this
 * matching the entire schema must be a prefix of the given path to
 * the part of this matching the schema variable.  If there is such a
 * path this method finds it, locates part of this expression using
 * it, and matches that subexpression with the schema.
 */
Expr.prototype.matchSchemaPart = function(path_arg, schema_arg, name) {
  var schema = termify(schema_arg);
  var targetPath = this.prettifyPath(Toy.path(path_arg));
  function matchName(expr) {
    return expr instanceof Atom && expr.name == name;
  }
  var schemaPath = schema.prettyPathTo(matchName);
  var prefix = targetPath.upTo(schemaPath);
  if (!prefix) {
    return null;
  }
  var target = this.get(prefix);
  var subst = target.matchSchema(schema);
  if (subst) {
    subst.path = prefix;
    return subst;
  }
  return null;
}

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
 *
 * Note also that we only seem to need to specify the name of a
 * newly-introduced bound variable in the implementation of bindEqn.
 * If this is so, the implementation of bindEqn could automatically
 * rename the new occurrences of bound variables, and it would never
 * be necessary to rename bound variables in the implementation of
 * subFree, simplifying its specification and possibly increasing its
 * performance.
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
  return Toy.isEmpty(map) ? this : this._subFree(map);
};

/**
 * Substitutes the replacement for a single name, which can be
 * a string or Atom as done by Expr.subFree.
 */
Expr.prototype.subFree1 = function(replacement, name) {
  return this.subFree(Toy.object0(name, replacement));
};

// TODO: Eliminate the "consider" rule, allowing instead introduction
// of new names if there is a proof that such a thing exists.  In this
// case "exists an x such that x = <expr>", which is always true for
// any expr, though in some cases x might be null.  (The name must be
// "new" to the proof.)

/**
 * For a non-rendered step, returns a path to the equation RHS if the
 * rule was "consider" or the step hasLeftElision; else the main part
 * if there are hypotheses; else the whole wff.  When eliminating the
 * "consider" rule, eliminate this and its uses also.
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
  var freeVars = this.freeVars();
  var bindings = null;
  for (key in freeVars) {
      bindings = new Bindings(key, key, bindings);
  }
  var expr = deeply ? this.copyForRendering(bindings) : this.dup();
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
 * Finds and returns a plain object/map of free variable names in this
 * expression, from name to true.
 */
Expr.prototype.freeVars = function() {
  var byName = {};
  this._addFreeNames(byName, null);
  return byName;
};

/**
 * Finds all occurrences of free variables in this expression that are
 * used as inputs to known math operators, or compared for equality
 * with the result of a math operator that returns a number.  The math
 * operators are currently the basic 4, exponentiation, and the
 * ordering relationals.  This is a convenience rather than a type
 * analysis.
 *
 * Returns the result as a set (map from name to true).
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
        expr = Toy.infixCall(expr, '&', Toy.call(real, name));
      } else {
        expr = Toy.call(real, name);
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
  var map = {};
  for (var more = bindings; more; more = more.more) {
    map[more.from] = true;
  }
  return map;
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
  assert(result instanceof Expr, 'Expr {1} has no position {2}', result, n);
  return result;
};

/**
 * Returns the RHS of the step if it has hypotheses, otherwise the
 * expression itself.
 * 
 * TODO: Use Step class.
 */
Expr.prototype.unHyp = function() {
  return this.hasHyps ? this.getRight() : this;
};

/**
 * Get the hypotheses of this step if it has any, else null.
 * 
 * TODO: Use Step class.
 */
Expr.prototype.getHyps = function() {
  return this.isCall2('==>') ? this.getLeft() : null;
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
   * Returns true iff this is a call to a function of two arguments that
   * is normally rendered and parsed as an infix binary operator.
   */
  isBinOpCall: function() {
    return this.isCall2() && isInfixDesired(this.getBinOp());
  },

  /**
   * Returns an equivalent path that uses "left", "right", and "binop"
   * to indicate subexpressions of binary operators where possible.
   */
  prettifyPath: function(p) {
    if (p.isEnd()) {
      return p;
    }
    var segment = p.segment;
    var rest = p._rest;
    if (this.isCall2() && isInfixDesired(this.getBinOp())) {
      if (segment === 'arg') {
        return new Path('right', this.getRight().prettifyPath(rest));
      } else if (segment === 'fn') {
        var seg2 = rest.segment;
        if (seg2 === 'fn') {
          return new Path('binop', this.getBinOp().prettifyPath(rest._rest));
        } else if (seg2 === 'arg') {
          return new Path('left', this.getLeft().prettifyPath(rest._rest));
        }
      }
    }
    // This expression and path segment are not a special case.
    // Prettify the subexpression and path at the next level down.
    var next = this.get(new Path(segment));
    // Return a path with this segment and the prettified tail
    // of this path.
    return new Path(segment, next.prettifyPath(rest));
  },

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
  assert(this.isCall1(name),
         (name === undefined
          ? 'Not a 1-argument call: {1}'
          : 'Not a 1-argument call to {2}: {1}'),
         this, name);
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
 * Public version of "get", finding a subexpression
 * from its path.  Handles /main in the path.
 */
Expr.prototype.get = function(_path) {
  return this._get(path(_path, this));
};

/**
 * Returns true iff this expression is a proof step.
 */
Expr.prototype.isStep = function() {
  // A property only proof steps have.  Could also use "ordinal", etc..
  return !!this.ruleName;
};

/**
 * Returns a truthy value iff the argument is a proof step.
 */
function isStep(x) {
  return x instanceof Expr && x.ruleName;
}

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
 * If the expression referenced by the given path from this expression
 * is the right operand of one of the given operators, this returns a
 * path to its "left neighbor" in the usual presentation of
 * expressions with operators such as +/- and times/divide.  The
 * operators are given as an Array of string names, and are assumed to
 * be binary.  This is assumed to be a "pretty" path with a parent.
 *
 * The path may be given as a string.  Returns null if there is no
 * such left neighbor.
 */
Expr.prototype.leftNeighborPath = function(path_arg, operators) {
  var path = Toy.path(path_arg);
  if (path.isEnd()) {
    return null;
  }
  if (path.last() != 'right') {
    return null;
  }
  var parentPath = path.parent();
  var parent = this.get(parentPath);
  if (!(parent.isCall2() && parent.getBinOp().in(operators))) {
    return null;
  }
  var left = parent.getLeft();
  if (left.isCall2() && left.getBinOp().in(operators)) {
    // Left operand is a call to another binop.
    return parentPath.concat(Toy.path('/left/right'));
  } else {
    // Left operand is something else.
    return parentPath.concat(Toy.path('/left'));
  }
};

/**
 * Like leftNeighborPath, but gets a right neighbor expression if
 * there is one, or null if not.
 */
Expr.prototype.rightNeighborPath = function(path_arg, operators) {
  var path = Toy.path(path_arg);
  if (path.isEnd()) {
    return null;
  }
  // First check if this is a left operand.
  var parentPath = path.parent();
  var parent = this.get(parentPath);
  if (!(parent.isCall2() && parent.getBinOp().in(operators))) {
    return null;
  }
  if (path.last() == 'left') {
    return parentPath.concat('/right');
  }
  // Then check if this is a right operand with grandparent
  // a suitable binary expression.
  if (parentPath.isEnd()) {
    return null;
  }
  if (parentPath.last() != 'left') {
    return null;
  }
  var parentPath2 = parentPath.parent();
  var parent2 = this.get(parentPath2);
  if (parent2.isCall2() && parent2.getBinOp().in(operators)) {
    // Grandparent expression is a call to another binop.
    // Return a path to its right operand.
    return parentPath2.concat(Toy.path('/right'));
  }
  return null;
};

/**
 * Returns an array of the "ancestor" expressions of the subexpression
 * of this referenced by the path, starting with this and including
 * the one at the end of the path.  Returns exactly one ancestor per
 * segment in the path, plus this.  Note that the expression at the end
 * of the path is ancestors[ancestors.length - 1].
 */
Expr.prototype.ancestors = function(path) {
  var result = [];
  this._ancestors(path, result);
  return result;
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
      assert(right instanceof Atom,
             'Internal error, not an Atom: {1}', right);
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


var _searchTermsOps = Toy.ownProperties({'+': true, '-': true, '=': true});

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
 * Searches for a pattern that matches this.  If it finds one, calls
 * any action function for each schema variable at each of the
 * variable's occurrences in the matching schema, passing it the
 * subexpression of this that matches and reverse path to the
 * occurrence.
 *
 * The patternInfo is a plain object with property "match" having the
 * schema to match, and properties with names of schema variables
 * having values that are the action function for the schema variable
 * with that name.
 */
Expr.prototype.walkPatterns = function(patternInfos) {
  var self = this;
  function handleTerm(schemaTerm, revPath) {
    // Note this is defined outside the loop, but it uses patternInfo
    // and map, which are in scope in JavaScript.
    if (schemaTerm.isVariable()) {
      var name = schemaTerm.name;
      if (name && patternInfo[name]) {
        // Call the function associated with the name of this
        // variable in the schema.
        patternInfo[name].call(null, map[name], revPath);
      }
    }
  }
  for (var i = 0; i < patternInfos.length; i++) {
    var patternInfo = patternInfos[i];
    var schema = termify(patternInfo.match);
    var map = this.matchSchema(schema);
    if (map) {
      schema.traverse(handleTerm);
      break;
    }
  }
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
// copyForRendering()
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
// expression's lexical context.  Private helper for the freeVars
// method.
//
//
// _boundNames(path, bindings)
//
// Returns a Bindings object (or null if no bindings) representing the
// set of bindings in effect at the given path within this Expr, plus
// the given bindings.
//
//
// _decapture(freeVars, allNames, bindings)
//
// Returns a copy of this expression with any bound variables present
// in freeVars renamed to names not present in allNames and distinct
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
// sameAs(expr)
//
// True iff all parts of this expression are identical to the
// corresponding parts of the argument.  This compares atoms by their
// "pname" properties, so constants that are aliases are not sameAs
// each other.
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
//
// _prettyPath(pred, revPath)
//
// Like _path, but for infix expressions produces /left, /right, etc.
// rather than combinations of /fn and /arg; and returns a forward
// path.
//
//
// _ancestors(path, array)
//
// Adds this to the array and descends further if the path has
// more segments.
//
//
// _bindingPath(pred, revPath)
//
// Searches for a subexpression of this that passes the test and is
// the bound variable of a Lambda.  Returns the "reverse path" from
// this to the Lambda, with the last path segment first, followed by
// the given revPath.
// 
//
// _checkSegment(path)
//
// Throws an error if the next segment of the path is not appropriate
// to this type of Expr.
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
*/

//// Atom -- variable bindings and references

//// A Atom object can represent a variable (free or bound) or a
//// constant (see isConstantName).

/**
 * Make a Atom with the given name.  If a non-null integer position is given,
 * use it to record the index in the input stream.  If the given name
 * is in the "aliases" map, the given name becomes the Atom's pname,
 * and the Atom's name becomes the value of the alias.  Pnames affect
 * only parsing and display, not the logic itself.
 *
 * CAUTION: This constructor is for internal use by code in this file
 * and implementations of methods on Expr, Atom, Call, and Lambda
 * classes only.  Use factory functions such as varify or constify as
 * the public APIs.
 *
 * TODO: Further reduce use of this too-primitive constructor.
 *
 * TODO: Make a separate type for tokens.
 */
function Atom(name, position) {
  // Expr.call(this);
  this.memos = {};
  this.pname = this.name = name;
  this._value = undefined;
  if (isConstantName(name))
  this.pos = position;
  if (aliases.hasOwnProperty(name)) {
    this.name = aliases[name];
  }
  // If the name represents an integer, sets the _value property to
  // that integer, or if it represents a string, sets the _value
  // property to the string.
  //
  // Variables have _value of "undefined" and named constants have
  // _value of null.
  this._value = isVariableName(name)
    ? undefined
    : isIntegerLiteral(name)
    ? parseInt(name)
    : name.charAt(0) === '"'
    ? Toy.parseStringContent(name)
    // Named constants:
    : null;
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
          : this.pname);
};

/**
 * Implementation of toUnicode for Atoms.
 */
Atom.prototype.toUnicode = function() {
  var name = this.pname;
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

// Translations of names, applied during conversion to Unicode.
// (When generating HTML and/or Unicode text.)
var unicodeNames = {
  '==': '\u21d4',     // Two-headed horizontal double arrow.
  '==>': '\u21d2',    // &rArr;
  '!=': '\u2260',     // &ne;
  '<=': '\u2264',     // &le;
  '>=': '\u2265',     // &ge;
  '**': '**',         // Dont change to sdots.
  '*': '\u22c5',      // &sdot;
  '-': '\u2212',      // &minus;
  '</': '</',         // Treat this as HTML.
  '/': '\u2215',      // division slash
  neg: '-',
  forall: '\u2200',
  exists: '\u2203'
};

// Defines aliases that affect both printing and parsing.
var aliases = {
  // Note that limiting '==' to boolean inputs would make it more than
  // just an alias as currently defined.
  '==': '=',
};

Atom.prototype.toHtml = Atom.prototype.toUnicode;

Atom.prototype.dump = function() {
  return this.name;
};

Atom.prototype._subFree = function(map) {
  // Note that this assumes the map has no prototype.
  return map[this.name] || this;
};

Atom.prototype.copyForRendering = function(bindings) {
  var name = getBinding(this.name, bindings) || this.pname;
  var result = new Atom(name);
  result.sourceStep = this.sourceStep;
  return result;
};

Atom.prototype.dup = function() {
  return new Atom(this.pname);
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
  if (path.isMatch()) {
    return bindings;
  } else {
    this._checkSegment(path);
  }
};

Atom.prototype._decapture = function(freeVars, allNames, bindings) {
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

Atom.prototype._get = function(path) {
  return path.isMatch() ? this : null;
};

Atom.prototype.sameAs = function(expr) {
  return expr instanceof Atom && this.pname === expr.pname;
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

Atom.prototype._ancestors = function(path, result) {
  result.push(this);
  this._checkSegment(path);
};

Atom.prototype._bindingPath = function(pred, revPath) {
  return null;
};

Atom.prototype._checkSegment = function(path) {
  if (!path.isMatch()) {
    throw new Error('Path ' + path +
                    ' is not applicable to an Atom; in ' + this);
  }
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

//// Utilities on Atoms

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
 * Returns the name given if it is not in existingNames, a set with
 * name strings as keys.  Otherwise returns a generated name with the
 * same "base" as the one given, and not in existingNames.  The base
 * is the name with any trailing digits removed.  The generated suffix
 * will be the lowest-numbered one not yet in use, starting with "1".
 * Adds the returned name to the existingNames set.
 */
function genName(name, existingNames) {
  var base = name.replace(/[0-9]+$/, '');
  var candidate = name;
  for (var i = 1; existingNames[candidate]; i++) {
    candidate = base + i;
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
    var op = this.fn.fn;
    if (isInfixDesired(op)) {
      if (useUnicode && op.name == '**') {
        // Use HTML for exponentiation.  So "Unicode" here is
        // currently a misnomer.
        return this.getLeft() + '<sup>' + this.getRight() + '</sup>';
      } else {
        return '(' + this.getLeft() + ' ' + op + ' ' + this.getRight() + ')';
      }
    } else {
      return '(' + op + ' ' + asArg(this.getLeft()) + ' ' + this.getRight() + ')';
    }
  } else if (this.fn instanceof Atom && Toy.isInfixDesired(this.fn)) {
    // TODO: Modify this output to be parseable -- ((op) arg)
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

Call.prototype.copyForRendering = function(bindings) {
  var result = new Call(this.fn.copyForRendering(bindings),
                        this.arg.copyForRendering(bindings));
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
    return bindings;
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
    this._checkSegment(path);
  }
};

Call.prototype._decapture = function(freeVars, allNames, bindings) {
  var fn = this.fn._decapture(freeVars, allNames, bindings);
  var arg = this.arg._decapture(freeVars, allNames, bindings);
  return (fn == this.fn && arg == this.arg ? this : new Call(fn, arg));
};

Call.prototype._addMathVars = function(bindings, set) {
  var findBinding = Toy.findBinding;
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
    case '**':
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
    // TODO: Check here for op is "=" or "!=".
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
    this._checkSegment(path);
  }
};

Call.prototype._get = function(path) {
  if (path.isMatch()) {
    return this;
  } else {
    var segment = path.segment;
    var rest = path._rest;
    if (this.fn instanceof Call) {
      if (segment === 'left') {
        return this.getLeft()._get(rest);
      } else if (segment === 'binop') {
        return this.getBinOp()._get(rest);
      } else if (segment === 'right') {
        return this.getRight()._get(rest);
      }
    }
    if (segment === 'fn') {
      return this.fn._get(rest);
    } else if (segment === 'arg') {
      return this.arg._get(rest);
    }
    this._checkSegment(path);
  }
};

Call.prototype.sameAs = function(expr) {
  return (expr instanceof Call &&
          this.fn.sameAs(expr.fn) &&
          this.arg.sameAs(expr.arg));
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
    p = this.getBinOp()._prettyPath(pred, revPath);
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

Call.prototype._ancestors = function(path, result) {
  result.push(this);
  var segment = path.segment;
  var rest = path._rest;
  switch (segment) {
  case 'left':
    return this.getLeft()._ancestors(rest, result);
  case 'right':
    return this.getRight()._ancestors(rest, result);
  case 'binop':
    return this.getBinOp()._ancestors(rest, result);
  case 'fn':
    return this.fn._ancestors(rest, result);
  case 'arg':
    return this.arg._ancestors(rest, result);
  }
  this._checkSegment(path);
};

Call.prototype._bindingPath = function(pred, revPath) {
  return (this.fn._bindingPath(pred, new Path('fn', revPath))
          || this.arg._bindingPath(pred, new Path('arg', revPath)));
};

// Keys in this object are legitimate paths to apply to a Call.
var _callSegmentNames = {fn: true, arg: true};

var _binopSegmentNames = {left: true, right: true, binop: true};

Call.prototype._checkSegment = function(path) {
  var error = false;
  if (path.segment in _binopSegmentNames && !this.isCall2()) {
    error = true;
  } else if (!(path.segment in _callSegmentNames)) {
    error = true;
  }
  if (error) {
    throw new Error('Path segment ' + path.segment +
                    'is not applicable to a Call; in ' + this);
  }
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
      lambda(newVar, this.body._subFree(Toy.object0(boundName, newVar)));
    return renamed._subFree(map);
  }
};

// Etc.

Lambda.prototype.copyForRendering = function(bindings) {
  var findBinding = Toy.findBinding;
  var bound = this.bound;
  var name = this.bound.name;
  var origName = name;
  if (this.bound.isGeneratedBound()) {
    // When copying a binding of the generatedBound kind, the copy
    // tries to replace it with a variable that has a simpler name
    // different than any name bound in this context (or free in the
    // entire wff).  It retains the base part (with no numeric suffix),
    // trying first just the base, then successive suffixes until finding
    // one with no binding in this scope.
    var base = bound.parseName().name;
    name = base;
    var counter = 0;
    while (true) {
      if (!Toy.findBindingValue(name, bindings)) {
        break;
      }
      counter++;
      name = base + '_' + counter;
    }   
  }
  
  var newBindings = (name == origName
                     ? bindings
                     : new Bindings(origName, name, bindings));
  var result = lambda(varify(name), this.body.copyForRendering(newBindings));
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
    return bindings;
  } else {
    var newBindings = new Bindings(this.bound.name, bindings);
    var segment = path.segment;
    var rest = path._rest;
    if (segment === 'bound') {
      return this.bound._boundNames(rest, newBindings);
    } else if (segment === 'body') {
      return this.body._boundNames(rest, newBindings);
    }
    throw new Error('Path segment "' + segment +
                    '" is not applicable to a Lambda; in ' + this);
 
  }
};

Lambda.prototype._decapture = function(freeVars, allNames, bindings) {
  // TODO: Share Vars more for efficiency.
  var oldName = this.bound.name;
  var newName = freeVars[oldName] ? genName(oldName, allNames) : oldName;
  // Add a binding only when the new name is different.
  var newBindings = ((newName == oldName)
                     ? bindings
                     : new Bindings(oldName, newName, bindings));
  var body = this.body._decapture(freeVars, allNames, newBindings);
  return (body == this.body) ? this : new Lambda(new Atom(newName), body);
};

Lambda.prototype._addMathVars = function(bindings, set) {
  this.body._addMathVars(new Bindings(this.bound.name, true, bindings), set);
  return false;
};

Lambda.prototype.replaceAt = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else if (path.segment === 'body') {
    var body = this.body.replaceAt(path._rest, xformer);
    return (body == this.body) ? this : lambda(this.bound, body);
  }
  this._checkSegment(path);
};

Lambda.prototype._get = function(path) {
  if (path.isMatch()) {
    return this;
  }
  var segment = path.segment;
  if (segment === 'bound') {
    return this.bound._get(path._rest);
  } else {
    return this.body._get(path._rest);
  }
  this._checkSegment(path);
};

Lambda.prototype.sameAs = function(expr) {
  return (expr instanceof Lambda &&
          this.bound.sameAs(expr.bound) &&
          this.body.sameAs(expr.body));
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
  var newBindings = new Bindings(this.bound, expr2.bound, bindings);
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

Lambda.prototype._ancestors = function(path, result) {
  result.push(this);
  var segment = path.segment;
  var rest = path._rest;
  if (segment === 'bound') {
    return this.bound._ancestors(rest, result);
  } else if (segment === 'body') {
    return this.body._ancestors(rest, result);
  }
  this._checkSegment(path);
};

Lambda.prototype._bindingPath = function(pred, revPath) {
  return (pred(this.bound)
          ? revPath
          : this.body._bindingPath(pred, new Path('body', revPath)));
};

Lambda.prototype._checkSegment = function(path) {
  var segment = path.segment;
  if (segment !== 'bound' && segment !== 'body') {
    throw new Error('Path segment ' + segment +
                    ' is not applicable to a Lambda; in ' + this);
  }
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


//// Export public names.

Toy.assertEqn = assertEqn;

Toy.TermSet = TermSet;
Toy.TermMap = TermMap;

Toy.Expr = Expr;
Toy.Atom = Atom;
Toy.Call = Call;
Toy.Lambda = Lambda;

Toy.varify = varify;
Toy.constify = constify;
Toy.isConstantName = isConstantName;
Toy.isVariableName = isVariableName;
Toy.isIdentifier = isIdentifier;
Toy.isIntegerLiteral = isIntegerLiteral;
Toy.checkRange = checkRange;
Toy.isStep = isStep;

Toy.getStepCounter = getStepCounter;

Toy.unicodeNames = unicodeNames;

Toy.genVar = genVar;
Toy.decapture = decapture;

// Private to xutil.js:
Toy._identifierPattern = identifierPattern;

})();
