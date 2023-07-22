// Copyright Crispin Perdue.  All rights reserved.

// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

'use strict';

var Path = Toy.Path;
var Bindings = Toy.Bindings;
var getBinding = Toy.getBinding;
var assert = Toy.assertTrue;
var abort = Toy.abort;
var check = Toy.check;
var ToySet = Toy.ToySet;
var ToyMap = Toy.ToyMap;

// Code in this file may reference xutil.js, but handle forward
// references properly.

// Forward references to xutil.js.
var termify;
var isInfixDesired;
var infixCall;
var parse;
var lambda;

// Resolve variables defined in xutil.js.  In loaded modules, here
// xutil.js, the call to "trigger" invokes handlers immediately.
//
// When using ES6 modules this initialization will no longer be
// needed.
//
// TODO: Replace top-level usage of $(function ... ) with ordinary
//   top-level execution except where we need the DOM available.
Toy.loaded.on('xutil', function() {
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
 *
 * TODO: Dump does not distinguish terms by type.
 *   Consider making it do so.
 */
function identifyTerm(term) {
  // TODO: Eliminate term.memos in favor of a WeakMap.
  var ident = term.memos.ident;
  if (ident) {
    return ident;
  }
  window.idCount = (window.idCount || 0) + 1
  // TODO: Make this function memoize dumps.
  ident = term.dump();
  term.memos.ident = ident;
  return ident;
};

/**
 * A TermSet is simply a set of terms distinguished by their "dump"s
 * as strings.  Variable scoping is not accounted for.
 */
function TermSet(term) {
  ToySet.call(this, identifyTerm);
  if (term) {
    this.add(term);
  }
}  
Toy.extends(TermSet, ToySet);


/**
 * A map from terms to a set of variables with standard names.  The
 * names are chosen so their lexical order matches the order in which
 * their terms were added to the map.  Use TermMap.addTerm to set up
 * values, never TermMap.set.  The "subst" field maintains a
 * corresponding substitution from names of free variables to terms.
 *
 * A TermMap can be made to track different binding scopes by calling
 * bindVar and unbind on entry and exit from each scope.  Probably
 * only useful for helping to convert a wff to standard variable
 * names.
 */
function TermMap() {
  ToyMap.call(this, identifyTerm);
  this.counter = 1;
  this.subst = {};
  // Array of current bound variables, outermost first.
  this.boundVars = [];
  // Arrays of variables and terms shadowed by currently bound variables,
  // in the same order as boundVars.  The vars are ones already generated
  // for this TermMap.  If a bound variable does not shadow an existing
  // mapping, the entries here are null.
  this.shadowVars = [];
  this.shadowTerms = [];
}
Toy.extends(TermMap, ToyMap);

/**
 * Ensure the term is in this map.  If not already present, assign it
 * a new variable as its value.  In all cases return the Atom assigned
 * to the term.  Maintains the "subst" field as well.
 */
TermMap.prototype.addTerm = function(term) {
  if (!this.has(term)) {
    var name = 'a' + this.counter++;
    this._set(term, new Atom(name));
    this.subst[name] = term;
  }
  return this.get(term);
};

/**
 * Adds a new variable to the map for an inner binding and returns it.
 * The argument is the variable in the original Lambda.
 */
TermMap.prototype.bindVar = function(vbl) {
  var name = 'a' + this.counter++
  var newVar = new Atom(name);
  this.boundVars.push(newVar);
  var outer = this.get(vbl);
  this._set(vbl, newVar);
  if (outer) {
    this.shadowVars.push(outer);
    this.shadowTerms.push(vbl);
  } else {
    this.shadowVars.push(null);
    this.shadowTerms.push(null);
  }
  return newVar;
};

/**
 * Handles the end of a scope by popping off information about the
 * binding.  Restores the shadowed binding if there was one, ie. in
 * the original expression, the bound variable had the same name as
 * one in an outer scope.
 */
TermMap.prototype.unbind = function() {
  var term = this.shadowTerms.pop();
  var v = this.shadowVars.pop();
  this.boundVars.pop();
  if (v) {
    this._set(term, v);
  }
};

// Make TermMap.set private.
TermMap.prototype._set = ToyMap.prototype.set;

TermMap.prototype.set = function(term, name) {
  throw new Error('Unsupported: TermMap.set', term, name);
};


//// Expr -- the base class

// Note: Transformations on expressions that leave a given
// subexpression the same return the identical subexpression object
// they were given.  This means that all operations that transform
// expressions must avoid copying except when necessary.

/**
 * Superclass for terms of all kinds: Atom, Call, Lambda.
 * See internal comments for details.
 */
class Expr {
  constructor() {
    this.__type = null;
    // Extensible set of remembered information, especially useful
    // since the result is conceptually immutable.
    // Duplicated in subclass constructors for speed.
    //
    // TODO: Consider whether rendered copies should share memos with
    //   the originals.
    this.__memos = {};
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
  }
  // Type accessor.  The _type property is set directly in very few
  // cases for system performance.  If null, it can be set by _withType
  // or _typeFrom.
  get type() {
    return this.__type;
  }
  get memos() {
    return this.__memos;
  }
  set memos(v) {
    abort('Readonly: memos');
  }
}

/**
 * Sets the type of this term, returning this. Only valid if no type
 * has been previously set.  Use with caution (in type inference
 * code).
 */
Expr.prototype._withType = function(type) {
  assert(!this.type, 'Type of {1} is already set', this);
  this.__type = type;
  return this;
};
  
/**
 * Sets the type of this from another term, returning this. Only valid
 * if no type has been previously set.  Use with caution (in type
 * inference code).
 */
Expr.prototype._typeFrom = function(expr) {
  assert(!this.type, 'Type of {1} is already set', this);
  this.__type = expr.type;
  return this;
};


/**
 * TODO: Make Step into a whole new class.  For now, it is just an
 * alias.  There will be some convenience methods such as getMain and
 * asmPart, but access to Expr properties and most methods will be
 * through the "wff" property.
 *
 * Step objects have a "wff" property, but an Expr will not.
 */
var Step = Expr;

/**
 * Make an Atom with the given name.  If a non-null integer position
 * is given, use it to record the index in the input stream.  If the
 * given name is in the "aliases" map, the given name becomes the
 * Atom's pname, and the Atom's name becomes the value of the alias.
 * Pnames affect only parsing and display, not the logic itself.
 *
 * An Atom object can represent a variable (free or bound) or a
 * constant, either literal or named (see isConstantName).
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
class Atom extends Expr {
  constructor(name, position) {
    super();
    this.__pname = this.__name = name;
    if (isConstantName(name))
      this.pos = position;
    if (aliases.hasOwnProperty(name)) {
      this.__name = aliases[name];
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
  }
  get name() {
    return this.__name;
  }
  set name(nm) {
    abort('Readonly: name');
  }
  get pname() {
    return this.__pname;
  }
  set pname(pnm) {
    abort('Readonly: pname');
  }
}


/**
 * Constructor for Call expressions.
 */
class Call extends Expr {
  constructor(fn, arg) {
    super();
    this._fn = fn;
    this._arg = arg;
  }
  get fn() {
    return this._fn;
  }
  set fn(v) {
    abort('Readonly: fn');
  }
  get arg() {
    return this._arg;
  }
  set arg(v) {
    abort('Readonly: arg');
  }
}

/**
 * Make a variable binding from a Atom and an Expr.  Any occurrences
 * of the same variable in the body should already be represented
 * by the same Atom.
 */
class Lambda extends Expr {
  constructor(bound, body) {
    super();
    this.__bound = bound;
    this.__body = body;
  }
  get bound() {
    return this.__bound;
  }
  set bound(v) {
    abort('Readonly: bound');
  }
  get body() {
    return this.__body;
  }
  set body(term) {
    abort('Readonly: body');
  }
}


//// Methods for Expr-related objects

// Controls generation of Unicode vs. ASCII strings, internal
// to Expr.toString and Expr.toUnicode.
var useUnicode = false;

/**
 * Converts to a string.  If "simply", even operators
 * are presented without parentheses.
 */
Expr.prototype.toString = function(simply) {
  const str = this._toString();
  if (simply) {
    return str;
  }
  // Parsing is generally strict about use of infix operators in other
  // contexts, so be sure to display them in parentheses by default.
  // Calls to functions that are infix operators can display as infix.
  const isInfix = Toy.isInfixDesired(this);
  return isInfix ? '(' + str + ')' : str;
};

// Used with Toy.showTypes level 'testing'.  The map keys are type
// variables and the values are integers starting at 1 to enable a
// canonical presentation for testing.
Toy._typeNums = new Map();

/**
 * Returns a string presenting this Expr or Step, including
 * type information for variables and potentially more.
 * Level defaults to 'vars', but can be 'atoms' or 'testing'.
 */
Expr.prototype.show = function (level) {
  try {
    Toy.showTypes = level || 'testing';
    return this.toString();
  } finally {
    Toy.showTypes = false;
    Toy._typeNums.clear();
  }
};

/**
 * Converts this Expr to a string of Unicode and/or HTML.  The display
 * is currently just the same as plain text display except names (or
 * pnames) that have Unicode counterparts are presented as Unicode and
 * some cases of exponentiation use HTML.  With the optional "simply"
 * argument, this renders operators without parentheses.
 *
 * This is a bit of a misnomer right now.
 */
Expr.prototype.toUnicode = function(simply) {
  const saved = useUnicode;
  useUnicode = true;
  try {
    return this.toString(simply);
  } finally {
    useUnicode = saved;
  }
}

/**
 * Like toUnicode, but allows HTML output.  Currently
 * these are one and the same; toUnicode may disappear.
 * If trimmed output is requested and there is a leading
 * open parenthesis, trim it and the closing one.
 */
Expr.prototype.toHtml = function(trimmed) {
  // Really toUnicode does produce marked-up HTML for
  // e.g. exponentiation.  Since <, >, and & are separated by spaces,
  // this is adequate in practice.
  const html = this.toUnicode();
  const result = (trimmed && html[0] === '(') ? html.slice(1, -1) : html;
  return result;
};

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

/**
 * Find all free occurrences of the given variable name and return
 * reverse paths to all of them as an Array.  The result paths
 * segments are all "fn", "arg", or "body", i.e. not prettified.
 */
Expr.prototype.locateFree = function(name) {
  var paths = [];
  this._locateFree(name, Path.empty, paths);
  return paths;
}

Expr.prototype._locateFree = function(name, path, paths) {
  if (this instanceof Atom) {
    if (this.name === name) {
      paths.push(path);
    }
  } else if (this instanceof Call) {
    this.fn._locateFree(name, new Path('fn', path), paths);
    this.arg._locateFree(name, new Path('arg', path), paths);
  } else if (this instanceof Lambda) {
    if (this.bound.name !== name) {
      this.body._locateFree(name, new Path('body', path), paths);
    }
  }
};

/**
 * Returns true iff this term is "exactly" the same as the given one,
 * including use of the same names throughout.  With a truthy value
 * for the optional "andTypes" argument, if both are fully typed, this
 * also checks that the types are the same.  Since the user has very
 * little control over type variable names, these may differ provided
 * that the types are equivalent.  If the further optional argument
 * is truthy, the types must be identical, as when the compared terms
 * are parts of the same top-level wff.
 */
Expr.prototype.sameAs = function(other, andTypes=false, exact=false) {
  // Based on the assumption that typed inputs are properly typed,
  // this only checks types of Atoms, because the types of the Atoms
  // determines all other types in the term.
  const map = new Map();
  const same = (a, b) => {
    const c = a.constructor;
    if (b.constructor !== c) {
      return false;
    } else if (c === Atom) {
      if (a.pname !== b.pname) {
        return false;
      } else {
        // If an Atom lacks type information, the type is deemed to
        // match.  This satisfies the specification.
        const t1 = a.hasType();
        const t2 = b.hasType();
        return (!andTypes || !t1 || !t2 ||
                (exact ? t1.equal(t2) : t1.equiv(t2, map)));
      }
    } else if (c === Call) {
      return same(a.fn, b.fn) && same(a.arg, b.arg);
    } else if (c === Lambda) {
      return same(a.bound, b.bound) && same(a.body, b.body);
    }
  };
  return same(this, other);
};

/**
 * Finds free occurrences of the given set of names in this Expr,
 * returning a Set of Atoms within this structure that represent free
 * occurrences of the names.
 */
Expr.prototype.occurrences = function(names) {
  const result = new Set();
  const search = term => {
    const c = term.constructor;
    if (c === Atom) {
      if (names.has(term.name)) {
        result.add(term.name);
      }
    } else if (c === Call) {
      search(term.fn);
      search(term.arg);
    } else if (c === Lambda) {
      if (!names.has(term.bound.name)) {
        search(term.body);
      }
    } else {
      abort('bad input');
    }
  };
  search(this);
  return result;
};

/**
 * Returns a Map object with the names of all free variables as keys,
 * and the value of each key being an Atom where that name occurs
 * free.  Order is "left to right", actually each function in a Call
 * before its arg, and the occurrence is the first in the order.
 */
Expr.prototype.freeVarsMap = function() {
  const byName = new Map();
  const boundNames = [];
  const traverse = term => {
    const ct = term.constructor;
    if (ct === Atom) {
      if (term.isVariable() && !boundNames.includes(term.name)) {
        byName.set(term.name, term);
      }
    } else if (ct === Call) {
      traverse(term.arg);
      traverse(term.fn);
    } else {
      const nm = term.bound.name;
      boundNames.push(nm);
      traverse(term.body);
      boundNames.pop();
    }
  }
  traverse(this);
  return byName;
};


//// Atoms -- functions

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
// character.
var variableRegex = /^[a-zA-Z$][0-9_]*([.:]|$)|^_/;

// Numeric literals.
var numeralRegex = /^-?[0-9]+$/;

// Constant names having the same form as a usual variable name.
// TODO: Consider handling of other constants such as C, Q, Z, N,
//   pi, and the imaginary unit.  Perhaps in context, R and
//   potentially "i" can be treated as parse-level abbreviations
//   for constants such as RR and ii with normal constant names.
const specialConsts = new Set(['T', 'F', 'R', 'e']);

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
  return !specialConsts.has(name) && name.match(variableRegex);
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
  // this._value set in constructor.
  return this instanceof Atom && this._value === undefined;
};

/**
 * Returns boolean indicating if this is a named constant, an Atom
 * that is not a variable, but not a literal except for 0, 1, or the
 * empty string.  (With complex numbers, "i" becomes another named
 * constant that is also a literal.)
 */
Expr.prototype.isNamedConst = function() {
  // In some sense this check is optional:
  if (!(this instanceof Atom)) {
    return false;
  }
  // If not an Atom or is a variable, _value is "undefined"
  // and this is not a named constant.
  var v = this._value;
  return v === null || v === 0 || v === 1 || v === '';
};

/**
 * True iff this is a var with the given name.
 */
Expr.prototype.hasName = function(name) {
  return this instanceof Atom && this.name === name;
};

/**
 * Returns a set of the names of named constants found within this
 * term.
 */
Expr.prototype.constantNames = function() {
  const result = new Set();
  const traverse = term => {
    const ct = term.constructor;
    if (ct === Atom) {
      if (term.isNamedConst()) {
        result.add(term.name);
      }
    } else if (ct === Call) {
      traverse(term.fn);
      traverse(term.arg);
    } else if (ct === Lambda) {
      traverse(term.body);
    } else {
      abort('Not an Expr: {1}', term);
    }
  };
  traverse(this);
  return result;
};

/**
 * True iff this is a Atom that is a constant.  If the optional name
 * is given, this constant must have the given name.
 */
Expr.prototype.isConst = function(opt_name) {
  if (!(this instanceof Atom) || this._value === undefined) {
    return false;
  }
  return opt_name ? this.name === opt_name : true;
};

// True iff the expression is a literal constant.
// Currently includes 0 and 1, though that probably
// should change.
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
 * Returns a truthy value iff the given term is a numeral, or it is
 * the quotient of two numerals.
 */
function isFraction(expr) {
  return (expr.isNumeral() ||
          (expr.isCall2('/') &&
           expr.getLeft().isNumeral() &&
           expr.getRight().isNumeral()));
}

/**
 * Double struck C N Q P R Z.
 */
var moreLettersRegex = /^[\u2102\u2115\u2119\u211a\u211d\u2124]$/;

/**
 * True iff this is a Atom that displays as an identifier.  This is
 * based on Unicode display, which may be a non-identifier in cases such
 * as "forall" and "exists", even when the internal name is an identifier.
 * Currently includes double-struck letters for common numerical types.
 * TODO: Consider simply special-casing quantifier symbols instead of this.
 */
Expr.prototype.displaysIdentifier = function() {
  if (this instanceof Atom) {
    var uni = this.toUnicode();
    return (uni.match(identifierRegex) ||
            uni.match(moreLettersRegex));
  }
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
  assert(this.isNumeral(), 'Not a numeral: {1}', self);
  return this._value;
}

/**
 * Check that the given number is within the range where integer
 * arithmetic is exact, returning it if so, raising an Error if not.
 */
function checkRange(number) {
  assert(Math.abs(number) <= Toy.MAX_INT,
         'Number out of range: {1}', number);
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

/**
 * Truthy iff the given term is a type condition on a variable.
 * Currently this means just a call on R, but extension to other
 * types is intended.
 */
Expr.prototype.isTypeCond = function() {
  return this.isCall1('R') && this.arg.isVariable();
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
 * Returns a new variable Atom with a name that does not occur free in
 * this expression.  If a name is given, uses that name as the
 * starting point for the name of the new variable, otherwise "x".
 */
Expr.prototype.freshVar = function(name) {
  name = name || 'x';
  return genVar(name, this.freeVars());
};

/**
 * Returns a new expression that "concatenates" this expression with
 * zero or more expressions joined by the named binary operator.  This
 * becomes the first operand of a chain of expressions connected by
 * the operator.  A null value indicates zero expressions, otherwise
 * the result has the form (((this op e1) op e2) ... ), where e1
 * ... are the operands of the expr argument taken as a chain.
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
 * Match this term with the given pattern, which may be a string or
 * Expr.  The result is an object/map or null.  If there is a purely
 * syntactic substitution that transforms the pattern into this, the
 * result is that substitution, which may be empty.  If there is no
 * such substitution, the result is null.
 *
 * The resulting substitution disregards scopes of variables, so
 * applying it via rules of inference such as instVar or Axiom 4 may
 * not yield a term equal to this as its result, even modulo changes
 * of bound variable names.  This is only for matching of syntactic
 * templates, as for example in rules.eRule.
 *
 * Beyond purely syntactic matching, a pattern variable bound to a
 * term also matches terms that differ from the first binding by
 * change of bound variable names.
 */
Expr.prototype.matchPattern = function(pattern_arg) {
  var pattern = termify(pattern_arg);
  var subst = {};
  var ok = pattern._matchAsPattern(this, subst, null);
  return ok ? subst : null;
};

/**
 * Treats this as a wff serving as a rewrite rule, and returns a path
 * to the part that is the part that will need to match when finding a
 * substitution into this.  Specifically, if this is an equation,
 * use its LHS.  Otherwise if it is a conditional, apply the policy
 * to its consequent.  If neither, use the whole term.
 *
 * This embodies a policy for rewriting.
 */
Expr.prototype.pathToSchema = function() {
  const self = this;
  const p = Toy.asPath;
  if (self.implies()) {
    return self.getRight().isCall2('=') ?  p('/right/left') : p('/right');
  } else {
    return self.isCall2('=') ? p('/left') : Path.empty;
  }
};
  

/**
 * Matches the given "schematic" expression against this. Returns a
 * substitution that yields this expression when given the schema, or
 * null if there is none.  The substitution maps from names to
 * expressions.  The matching here is only first-order.  In the current
 * system implementation, to guarantee correct typing it is best to
 * attempt actual substitution with the result.
 *
 * This is a form of unification of expressions.  This and the schema
 * can be arbitrary terms.
 *
 * In case of substitutions into contexts with bound variables, this
 * may return a substitution that yields a result that is
 * equivalent to the input only after some beta reductions.
 * Information about the number of expansions introduced per variable
 * is in the WeakMap Toy.betaExpansions.
 *
 * TODO: Consider how to ensure that higher-order matching is not done
 *   when not appropriate.  Perhaps review code that uses this.  The
 *   current assumption seems to be that if the schema may need
 *   higher-order matching and then substitution, it is used within a
 *   rewrite, and rewrites do any reductions that may be needed
 *   following the substitution.
 *
 *   Perhaps a better option would be to include the reductions as
 *   part of the substitution operation, as indicated by the extended
 *   information associated with the computed substitution.
 */
Expr.prototype.matchSchema = function(schema_arg) {
  const schema = schema_arg instanceof Expr ? schema_arg : parse(schema_arg);
  var substitution = {};
  var result = schema._matchAsSchema(this, substitution, null);
  return result ? substitution : null;
};

/**
 * Returns a list (Array) of the names of the free variables of this
 * Expr whose names are not keys in the given map (plain object), in
 * lexicographic order.
 */
Expr.prototype.unmappedVars = function(map) {
  // Plain object, mapping from name to true.
  var allFree = this.freeVars();
  var result = [];
  for (var name in allFree) {
    if (!(name in map)) {
      result.push(name);
    }
  }
  return result.sort();
};

/**
 * Returns a truthy value iff this and the given Expr differ only in
 * names of free and/or bound variables.  When true, the value is a
 * substitution ("alpha conversion") that maps free variable names in
 * this to Atom objects in the Expr.  Applying the substitution to this
 * Expr results in an Expr that "matches" the Expr argument of this
 * method.  This does not attempt to match types.
 */
Expr.prototype.alphaMatch = function(expr_arg) {
  var expr = termify(expr_arg);
  var subst = expr.matchSchema(this);
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
 * Attempts to match part of this to part of the given schema.  The
 * arguments are a path within this, a schema, and a "schema part"
 * given as a subexpression of the schema.  The given path needs to
 * refer to the part of this that will match the specified part of the
 * schema, and the schema part needs to uniquely identify a part of
 * the schema to match.
 *
 * Let's call the part of this at the given path the "target"
 * expression.  This method calculates the path within the schema
 * where the schema part occurs (the "schema path"), then identifies
 * an expression in this that has the target at that same "schema
 * path".
 *
 * All arguments may be given as strings as desired.  The schema part
 * should of course occur exactly once in the schema.
 *
 * If successful, this method returns a substitution with an extra
 * "path" property containing the path to the part of this that
 * matches the entire schema.  The rest of the substitution maps from
 * names of schema variables to subexpressions of this that match
 * them.  If not successful, returns null.
 *
 * The implementation idea is that the path to the part of this
 * matching the entire schema must be a prefix of the given path.  If
 * there is such a path this method finds it, locates part of this
 * expression using it, and matches that subexpression with the
 * schema.
 *
 * The same task could be done by passing a (pretty) path from the
 * schema to the part of interest, rather than the part itself, but
 * this way seems to result in more readable code.
 *
 * TODO: Consider merging this with matchFactPart, creating something
 *   like applyMatchingFact.
 */
Expr.prototype.matchSchemaPart = function(path_arg, schema_arg, schema_part) {
  var schema = termify(schema_arg);
  var part = termify(schema_part);
  var targetPath = this.prettifyPath(this.asPath(path_arg));
  function match(expr) {
    return expr.matches(part);
  }
  var schemaPath = schema.prettyPathTo(match);
  var prefix = targetPath.upTo(schemaPath);
  if (!prefix) {
    return null;
  }
  var target = this.get(prefix);
  // TODO: Consider what to do if the substitution may fail.
  var subst = target.matchSchema(schema);
  if (subst) {
    subst.path = prefix;
    return subst;
  }
  return null;
};

/**
 * Returns an expression that is the result of applying the given
 * substitution to all free occurrences of its named variables.
 * The substitution is an object/map from name to Expr.
 *
 * All substitutions are legal.  This renames enough bound variables
 * in the target to ensure that they are all distinct from variables
 * in the replacement, possibly more than necessary, so don't count on
 * bound variables keeping their names after a substitution.
 *
 * This operation retains whatever type information may be already
 * present in the map, but does not check, update, or unify any
 * type information.  It is essentially first-order.
 */
Expr.prototype.subFree = function(map_arg) {
  var map = Object.create(null);
  // Object / set of names of variables that are free in some
  // term of the substitution.
  // TODO: This should probably include all variables that are free
  // in this before the substitution!
  var freeVars = {};
  for (var name in map_arg) {
    var replacement = map_arg[name];
    if (!(replacement instanceof Atom && replacement.name == name)) {
      // Omit no-op substitutions.
      map[name] = replacement;
      Object.assign(freeVars, replacement.freeVars());
    }
  }
  // The implementation strategy is to rename bound variables whose
  // names are free in any of the substitution terms.  We choose to
  // give them names distinct from all names appearing anywhere in
  // this Expr, distinct from all free names in the values of the
  // substitution map, and also distinct from each other, eliminating
  // potential for capturing.
  //
  // We pass the set of all var names recursively, adding new names to
  // it when binding points are found and the new name is generated.
  // As the traversal encounters lambdas we also update the map to
  // reflect current bound variable renamings and revert the mappings
  // on exit from the scope.
  const allNames = Object.assign(this.allNames(), freeVars);
  return Toy.isEmpty(map) ? this : this._subFree(map, freeVars, allNames);
};

/**
 * Substitutes the replacement for a single name, which can be a
 * string or Atom as done by Expr.subFree.  Used by Axiom 4 (axiom
 * of substitution).
 *
 * TODO: Consider implementing this independently of subFree, as this
 *   can be faster and cleaner.
 */
Expr.prototype.subFree1 = function(replacement, name) {
  return this.subFree(Toy.object0(name, replacement));
};

/**
 * Applies the given renaming to this term.  The renaming is an
 * object/map from strings to Atoms, which this uses to rename free
 * variables.  This assumes that the names of the Atoms in the map are
 * distinct from all variable names in this, free or not, so the
 * result will be equivalent to the input term.  The result is
 * untyped.
 */
Expr.prototype.rename = function(map) {
  const rename = term => {
    const ct = term.constructor;
    if (ct === Atom) {
      return map[term.name] || term;
    } else if (ct === Call) {
      return new Call(rename(term.fn), rename(term.arg));
    } else if (ct === Lambda) {
      return new Lambda(rename(term.bound), rename(term.body));
    }
  };
  return rename(this);
};

/**
 * Called with a non-rendered step; returns a path to the main
 * part of the step; or if the main is an equivalence or
 * equality, returns the RHS of that.
 */
Expr.prototype.pathToFocalPart = function() {
  var main = this.getMain();
  return Toy.asPath(main.isCall2('=')
                    ? '/main/right'
                    : '/main');
};


/**
 * Returns truthy iff this is a conditional and the path is on its
 * assumptions side.  Usually "this" is a whole step.
 */
Expr.prototype.isAsmPath = function(path) {
  return this.implies() && path.isLeft();
};

var _assertionCounter = 1;


////
//// Methods that properly belong to Exprs that are proof steps
////

/**
 * Computes the "base instance" of a proof step.  Each level of
 * justification has its own Expr, all equal, but each with its
 * own justification and details.  This accesses the bottom level
 * step.
 */
Step.prototype.getBase = function() {
  var result = this;
  while (result.details) {
    result = result.details;
  }
  return result;
};

//// End of methods for proof steps

/**
 * Finds and returns a plain object/map of free variable names in this
 * expression, from name to true.  In typical implementations
 * iteration over the map will get variables in right-to-left order
 * for the potential benefit of performance in things like tautology
 * checking.  For guaranteed ordering, see Expr.freeVarSet.
 */
Expr.prototype.freeVars = function() {
  // This method gets called a lot for substitutions.
  var byName = new Set();
  this._addFreeVars(byName, null);
  var result = {};
  for (const name of byName) {
    result[name] = true;
  }
  return result;
};

/**
 * Finds and returns a Set object containing all the free variable
 * names in this expression.  Iteration is guaranteed to return the
 * names in traversal order of first occurrence, where function is
 * considered to come before arg in calls.
 */
Expr.prototype.freeVarSet = function() {
  var byName = new Set();
  this._addFreeVarSet(byName, null);
  return byName;
};

/**
 * Set of all names of constants that are used in any statement
 * considered true in the theory.  Numeric literals other than 0 and 1
 * are not considered names, but as abbreviations for expressions
 * containing 0 and 1.
 */
const namedConstants = new Set();

/**
 * Adds the given iterable (e.g. Set or Array) of names to the set of
 * all named constants.
 */
function addConstants(names) {
  names.forEach(function(name) {
      namedConstants.add(name);
    });
}

/**
 * Finds and returns a Set of names of constants in this expression
 * that are not in namedConstants.
 */
Expr.prototype.newConstants = function() {
  const names = new Set();
  this._addNewConstants(names, null);
  return names;
};

/**
 * Finds all occurrences of free variables in this expression that are
 * used as inputs to known math operators, or compared for equality
 * with the result of a math operator that returns a number.  The math
 * operators are currently the basic 4, neg, recip, exponentiation,
 * and the ordering relationals.  This is a convenience rather than a
 * type analysis.
 *
 * Returns the result as a set (map from name to true).
 *
 * TODO: Replace this with a system that provides default types
 *   for variables according to their names.
 */
Expr.prototype.mathVars = function() {
  var map = {}; 
  this._addMathVars(null, map);
  return map;
};

/**
 * Returns a conjunction of conditions that each of the mathVars of
 * this expression is of type R (real), or null if the set of mathVars
 * is empty.  The variables occur in the conditions in the order they
 * are returned from the freeVars method.  This is based on order of
 * occurrence, so mathParse will give results that alphaMatch when
 * given inputs that alphaMatch when given to Toy.parse.
 *
 * If the optional expr is present, uses that as an initial conjunct
 * to add to.
 */
Expr.prototype.mathVarConditions = function(expr) {
  var real = new Atom('R');
  // Order the names for nice presentation.
  var names = [];
  const freeVars = Array.from(this.freeVarSet());
  const numVars = this.mathVars();
  freeVars.forEach(function(name) {
      if (numVars[name]) {
        names.push(name);
      }
    });
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
 * Finds and returns an object/map of all the names bound in this
 * expression at the location given by the path, represented by an
 * object/map from names to the variable Atom actually bound.
 */
Expr.prototype.boundNames = function(path) {
  path = this.asPath(path);
  var bindings = this._boundNames(path, null);
  var map = {};
  for (var more = bindings; more; more = more.more) {
    map[more.from] = more.to;
  }
  return map;
};

/**
 * Finds and returns an object/map with all names occurring in this
 * expression as the keys, with values of "true".
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
 * TODO: Make this available for Step objects.
 */
Expr.prototype.getMain = function() {
  return this.isCall2('=>') ? this.getRight() : this;
};

/**
 * Returns the assumptions of a conditional, if any, else falsy.
 */
Expr.prototype.getAsms = function() {
  return this.isCall2('=>') && this.getLeft();
};

Expr.prototype.isTypeTest = function() {
  return (this.isCall1() &&
          (this.fn.name === 'R' ||
           this.fn.name === 'NN' ||
           this.fn.name === 'ZZ'));
};

/**
 * Returns truthy iff this looks like a subgoal.
 */
Expr.prototype.likeSubgoal = function() {
  return (!this.isTypeTest() &&
          !this.matchSchema('not (x = y)') &&
          !this.matchSchema('x != y'));
};

/**
 * Tests whether the given goal (wff) has a subgoal within its
 * assumptions, currently defined as anything other than a real number
 * assumption or an inequality condition.
 */
Expr.prototype.hasSubgoal = function() {
  const asms = this.getAsms();
  return asms && asms.scanConj(x => x.likeSubgoal());
};

/**
 * Returns the nth "element" of this expression.  Recurs top down
 * through function parts of calls until finding a Atom, which is
 * consider element 0.  The arg part of that call is element 1,
 * and the arg goes up by 1 for each level.  The effect is that a
 * call written as (f a b c) gives the Atom "f" as element 0, "a"
 * as element 1, "b" as element 2, and "c" as element 3.
 */
Expr.prototype.nthArg = function(n) {
  var result = this._nthArg(n);
  assert(result instanceof Expr, 'Expr {1} has no position {2}', result, n);
  return result;
};

/**
 * Get the assumptions of this step if it has any, else null.
 */
Step.prototype.asmPart = function() {
  var wff = this.wff;
  return wff.isCall2('=>') ? wff.getLeft() : null;
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
      && (name == null || left.fn.name == name || left.fn.pname == name);
  } else {
    return false;
  }
};

/**
 * Tests whether this Expr is conditional.
 */
Expr.prototype.implies = function() {
  return this.isCall2('=>');
};

/**
 * True iff this is a call to a lambda expression.
 */
Expr.prototype.isLambdaCall = function() {
  return this instanceof Call && this.fn instanceof Lambda;
};

var exprMethods = {

  /**
   * If this term is a call, returns the first "fn" descendent that
   * is not a Call (thus an atom or lambda), otherwise returns null.
   */
  func: function() {
    var term = this;
    if (!(term instanceof Call)) {
      return null;
    }
    while (term instanceof Call) {
      term = term.fn;
    }
    return term;
  },

  /**
   * Returns an array of the actual arguments to the function that
   * would be the result of applying "func" to this Expr.
   */
  args: function() {
    var term = this;
    var result = [];
    while (term instanceof Call) {
      result.unshift(term.arg);
      term = term.fn;
    }
    return result;
  },

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
    var rest = p.rest;
    if (this.isCall2() && isInfixDesired(this.getBinOp())) {
      if (segment === 'arg') {
        return new Path('right', this.getRight().prettifyPath(rest));
      } else if (segment === 'fn') {
        var seg2 = rest.segment;
        if (seg2 === 'fn') {
          return new Path('binop', this.getBinOp().prettifyPath(rest.rest));
        } else if (seg2 === 'arg') {
          return new Path('left', this.getLeft().prettifyPath(rest.rest));
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
            (this.isCall2('=>') && this.getRight().isCall2('=')));
  },

  /**
   * Gets the left side of an equation, possibly with assumptions.
   */
  eqnLeft: function() {
    var eqn = this.isCall2('=>') ? this.getRight() : this;
    eqn.assertCall2('=');
    return eqn.getLeft();
  },
  
  /**
   * Gets the right side of an equation, possibly with assumptions.
   */
  eqnRight: function() {
    var eqn = this.isCall2('=>') ? this.getRight() : this;
    eqn.assertCall2('=');
    return eqn.getRight();
  }

};
Toy.addMethods(Expr, exprMethods);

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
    '=>': 'a conditional',
    '=': 'an equation',
    '&': 'a conjunction',
    '|': 'a disjunction'
  };
  var message;
  if (name == null) {
    message = 'Not a call to a named 2-argument function';
  } else {
    var uni = unicodeNames[name] || name;
    message = ('Not ' + (map[name] || 'a call to ' + uni) + ': ' + this);
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
 * Public version of "get", finding a subexpression from an argument
 * convertible to a path using Expr.asPath.
 */
Expr.prototype.get = function(arg) {
  let p = this.asPath(arg);
  let next = this;
  while (p !== Path.empty) {
    const seg = p.segment;
    p = p.rest;
    next = next.descend(seg);
  }
  return next;
};

/**
 * Returns the subterm at the given reverse path.  If the path does
 * not refer to a term, it is an error.
 */
Expr.prototype.revGet = function(rpath) {
  if (rpath.isEnd()) {
    return this;
  } else {
    const term = this.revGet(rpath.rest);
    return term.descend(rpath.segment);
  }
};
    

/**
 * Converts the argument into a path within this Expr.  Given a Path
 * or path string, this adjusts leading occurrences of "/main" based
 * on the structure of this Expr.
 * 
 * If the argument is a string either empty or beginning with "/",
 * parses it into a Path object; otherwise treats a string as an Expr,
 * parsing it into a term.  Accepts a Bindings object, interpreting it
 * as a reversed sequence of path segments.
 *
 * An Expr or function causes this to search for a match; if an Expr,
 * a subterm that is sameAs, if a function, a subterm satisfying it.
 *
 * Returns the resulting Path object, which will not start with a
 * /main segment.
 */
Expr.prototype.asPath = function(arg) {
  const self = this;

  // If the initial segment of the path is 'main' or 'rt'
  // and the term is conditional, return a path to its RHS.
  function adjust(path) {
    var segment = path.segment;
    if (segment == 'main') {
      path = path.rest;
      if (self.isCall2('=>')) {
        path = new Path('right', path);
      }
    } else if (segment == 'rt') {
      path = path.rest;
      if (self.isCall2('=>')) {
        path = new Path('right', path);
      }
    }
    return path;
  }

  const type = typeof arg;
  if (type === 'function') {
    return this.pathTo(arg);
  } else if (arg instanceof Expr) {
    function sameAs(term) {
      return term.sameAs(arg);
    }
    const result = this.pathTo(sameAs);
    assert(result, 'No term found matching {1}', arg);
    return result;
  } else if (type === 'string' && arg.length && arg[0] !== '/') {
    const result = this.asPath(termify(arg));
    assert(result, 'Term not found: {1}', arg);
    return result;
  } else {
    return adjust(Toy.asPath(arg));
  }
}

/**
 * Return the subexpression of this referenced by
 * the given segment string.
 */
Expr.prototype.descend = function(segment) {
  assert(this !== Path.empty, 'Path is empty');
  if (this instanceof Call) {
    if (this.fn instanceof Call) {
      if (segment === 'left') {
        return this.getLeft();
      } else if (segment === 'binop') {
        return this.getBinOp();
      } else if (segment === 'right') {
        return this.getRight();
      }
    }
    if (segment === 'fn') {
      return this.fn;
    } else if (segment === 'arg') {
      return this.arg;
    }
  } else if (this instanceof Lambda) {
    if (segment === 'bound') {
      return this.bound;
    } else if (segment === 'body') {
      return this.body;
    }
  }
  this._checkSegment(new Path(segment));
};

/**
 * Really for a top-level Expr, i.e. wff.  This ensures an initial
 * /main wherever possible, giving a result that refers to the same
 * place.  Rightward paths into a conditional replace /right or /arg
 * with /main.  Otherwise it prepends /main.
 */
Expr.prototype.mainify = function(path) {
  if (path.segment == 'main') {
    return path;
  } else if (path.isRight() && this.implies()) {
    return new Path('main', path.rest);
  } else if (this.implies()) {
    // It is a leftward path into a conditional.
    return path;
  } else {
    return new Path('main', path);
  }
};

/**
 * Returns true iff this expression is a proof step.
 *
 * TODO: Remove this when there is a Step class.
 */
Expr.prototype.isProved = function() {
  // A property only proof steps have.
  return !!this.ruleName;
};

/**
 * Returns a truthy value iff the argument is a proof step.
 */
function isProved(x) {
  return x instanceof Step && x.isProved();
}

/**
 * Searches for a subexpression of this that passes the test, given as
 * a boolean function of one argument.  Returns a (non-pretty) path
 * from this to the occurrence, or null if none found.  Tests this
 * expression first, followed by the rest in top-down right-to-left
 * order.  Does not search for variable bindings, use pathToBinding
 * instead.  Alternatively accepts a term to be matched with sameAs,
 * which may be given as a string.
 */
Expr.prototype.pathTo = function(arg) {
  // TODO: Make a more efficient version that works directly with
  // forward paths.
  let test = arg;
  if (typeof arg === 'string' || arg instanceof Expr) {
    const target = termify(arg);
    test = function(term) { return target.sameAs(term); };
  }
  const rpath = this._path(test, Toy.asPath(''));
  return rpath ? rpath.reverse() : null;
};

/**
 * Searches for the (first) subexpression of this that "matches" the
 * given term, an Expr or string parsed to one.  Neither is taken as a
 * schma.  Returns a path to the term if found, or null.
 */
Expr.prototype.find = function(term_arg) {
  var term = termify(term_arg);
  function alike(x) {
    return x.matches(term);
  }
  return this.pathTo(alike);
};

/**
 * Like Expr.pathTo, but for infix calls produces a path with /left,
 * /right, or /binop rather than combinations of /fn and /arg.
 * If given a Step that is not conditional, prepends /main.
 *
 * Given a term to match against, this searches for an identical
 * term, not just a sameAs term, unlike pathTo.
 *
 * TODO: Consider also converting initial /right to /main
 *   and removing mainify.
 */
Expr.prototype.prettyPathTo = function(pred) {
  if (pred instanceof Expr) {
    var target = pred;
    pred = function(term) { return target == term; };
  }
  var p = this._prettyPath(pred, Toy.asPath(''));
  return (this.isProved() && !this.isCall2('=>')
          ? new Path('main', p)
          : p);
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
  var path = Toy.asPath(path_arg);
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
    return parentPath.concat(Toy.asPath('/left/right'));
  } else {
    // Left operand is something else.
    return parentPath.concat(Toy.asPath('/left'));
  }
};

/**
 * Like leftNeighborPath, but gets a right neighbor expression if
 * there is one, or null if not.
 */
Expr.prototype.rightNeighborPath = function(path_arg, operators) {
  var path = Toy.asPath(path_arg);
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
    return parentPath2.concat(Toy.asPath('/right'));
  }
  return null;
};

/**
 * Returns an array of the "ancestor" expressions of the subexpression
 * of this referenced by the path, starting with this and including
 * the one at the end of the path.  Returns exactly one ancestor per
 * segment in the path, plus this.  Note that the expression at the end
 * of the path is the last element of the array.
 *
 * This traces through the path exactly as given, so if the path uses
 * segments such as /left or /binOp, it will skip terms in the result.
 */
Expr.prototype.ancestors = function(path_arg) {
  let p = this.asPath(path_arg);
  let term = this;
  const result = [];
  while (true) {
    result.push(term);
    if (p.isEnd()) {
      break;
    }
    term = term.descend(p.segment);
    p = p.rest;
  }
  return result;
};

/**
 * Among the ancestors of the subexpression at the given path (see
 * Expr.ancestors), finds a path to the ancestor nearest to the
 * subexpression that passes the given test.  Returns null if none is
 * found.
 */
Expr.prototype.findParent = function(path_arg, test) {
  var p = this.asPath(path_arg);
  // Expression descended to so far.
  var term = this;
  // Portion of path not yet traversed.
  var tail = p;
  // Path to the latest parent found.
  var foundPath = null;
  // Now traverse down the path, recording paths to parents that pass.
  while (true) {
    if (test(term)) {
      // Parent is found, remember the path to it.
      foundPath = p.upTo(tail);
    }
    if (tail.isEnd()) {
      break;
    }
    term = term.descend(tail.segment);
    tail = tail.rest;
  }
  return foundPath;
};

/**
 * Returns the parent subexpression that is a binary call to '=' (or '==')
 */
Expr.prototype.parentEqn = function(path) {
  return this.findParent(path, function(term) { return term.isCall2('='); });
};

/**
 * Returns an array of all of the operands of a chain of calls to a
 * binary operator.  If the current term is not a call to a binary
 * operator there are no such operands and this returns an empty
 * array.
 *
 * If it is a binop call, this returns all operands of the chain of
 * calls to the same operator, from right to left, so always at least
 * two values.  (All but the last will be accessed with a final
 * rightward path segment, and the last one with a leftward path
 * segment.)
 */
Expr.prototype.chainTerms = function(chainOp) {
  const result = [];
  let node = this;
  if (node.isCall2(chainOp)) {
    while (true) {
      result.push(node.getRight());
      let next = node.getLeft();
      if (next.isCall2(chainOp)) {
        node = next;
        continue;
      } else {
        result.push(next);
        break;
      }
    }
  } else {
    result.push(this);
  }
  return result;
};

/**
 * Returns an array of Paths from this Expr to each of the operands of
 * a chain of calls to the given chainOp, as for chainTerms, but
 * returning paths rather than terms.
 */
Expr.prototype.chainPaths = function(chainOp) {
  const result = [];
  let node = this;
  if (node.isCall2(chainOp)) {
    let chainPath = Path.empty;
    while (true) {
      result.push(new Path('right', chainPath));
      let next = node.getLeft();
      let nextPath = new Path('left', chainPath);
      if (next.isCall2(chainOp)) {
        node = next;
        chainPath = nextPath;
        continue;
      } else {
        result.push(new Path('left', chainPath));
        break;
      }
    }
  } else {
    result.push(Path.empty);
  }
  return result;
};

// TODO: Probably remove this and nearestChain.
var chainMap = new Map();
{
  const ops=[['+', '-'], ['*', '/'], ['&'], ['|']];
  ops.forEach(a => a.forEach(op => chainMap.set(op, a)));
}

/**
 * Returns the innermost chain, if any, that this term belongs to.  A
 * chain is a leftward sequence of terms with connected by binary
 * operators compatible with a binop parent term.  Left operands are
 * not members of the chain unless they are "leftmost", i.e. not a
 * call with compatible binop.
 *
 * This descends through the path, 
 */
Expr.prototype.nearestChain = function(path) {
  let p = Toy.asPath(path);
  if (p.isEnd()) {
    return null;
  }

  let chain = null;
  // If this is non-null at the target term, it is the chain of which
  // the target term is an element.  Top and continuation terms of a
  // chain (e.g. any "+" term within a chain of "+ terms) are not
  // elements of it.
  let parent = null;
  // This is an array of binary operations that participate in the current
  // chain (or an empty array if no chain).
  let chops = [];
  let term = this;

  // Inside the loop, "segment" is the segment that brought us to the
  // current term.  It is significant that it is initially null.
  let segment = null;

  // If the term is a named binary operator, returns the name, else falsy.
  const bopName = term => term.isCall2() ? term.getBinOp().name : null;

  // The term starts a new chain.  It could be an element of the
  // previous current chain.
  const newChain = () => {
    const nm = term.getBinOp().name;
    parent = chain;
    chain = term;
    chops = chainMap.get(nm) || [];
  };

  // The term does not continue a chain nor start a new one.
  // It could be an element of the previous current chain.
  const noChain = () => {
    parent = chain;
    chain = null;
    chops = [];
  };
  while (true) {
    const nm = bopName(term);
    if (segment === 'left' && chops.includes(nm)) {
      // The term continues a chain, do nothing.
    } else if (chainMap.has(nm)) {
      newChain();
    } else {
      noChain();
    }
    if (p.isEnd()) {
      return parent;
    }
    segment = p.segment;
    term = term.descend(segment);
    p = p.rest;
  }
};

/**
 * Returns a description of the movement of a variable in this
 * equational Expr, which may be conditional.  Each side of the
 * equation should contain the variable exactly once, and the
 * returned value is a plain object with:
 *
 * left: pretty path to vbl from the LHS
 * right: pretty path to vbl from the RHS
 *
 * The variable may be given as a string.  It could also be a term.
 */
Expr.prototype.movement = function(vbl_arg) {
  const vbl = termify(vbl_arg);
  const left = this.eqnLeft();
  const right = this.eqnRight();
  const lPath = check(left.prettyPathTo(term => term.matches(vbl)))
  const rPath = check(right.prettyPathTo(term => term.matches(vbl)));
  return {from: lPath, to: rPath};
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
  var revPath = this._bindingPath(pred, Toy.asPath(''));
  return revPath ? revPath.reverse() : null;
};

/**
 * Walks through all subexpressions of this Expr, applying the
 * function to each one, passing the (reverse) path to the
 * subexpression as an argument.  The rpath is relative to this,
 * though if an rpath is given here, the function receives the
 * concatenation of the one given here and the relative path.
 *
 * This is intended for use searching for places to apply
 * simple rewrites, so for the sake of simplicity it does not
 * descend into lambdas.
 *
 * TODO: Consider replacing traverse and all of its uses with
 *   Expr.searchMost.
 */
Expr.prototype.traverse = function(fn, rpath) {
  this._traverse(fn, rpath || Path.empty);
};

/**
 * True iff this expression is a Call with at least N arguments, where
 * N is at least 1.  Meaning to say this and N - 1 levels of calls
 * nested within its function part.
 */
Expr.prototype.hasArgs = function(n) {
  return (n < 1) ? true : this instanceof Call && this.fn.hasArgs(n - 1);
};

/**
 * Returns the number of arguments passed to the function in this
 * Call.  The result is based on the structure of the Call, merely
 * calculating the depth to reach a Lambda or Atom.  Result is zero if
 * given a Lambda or Atom.
 */
Expr.prototype.argsPassed = function() {
  return (this instanceof Call
          ? this.fn.argsPassed() + 1
          : 0);
};

/**
 * Descends recursively into "fn" parts of this Expr to the first
 * Lambda or Atom, returning it.
 */
Expr.prototype.funPart = function() {
  return (this instanceof Call ? this.fn.funPart() : this);
};

/**
 * Treating this as a chain of assumptions hk & h(k-1) & ... h1, and
 * given an expression that matches one of the assumptions, builds an
 * expression where "h" is in the position of the matched assumption,
 * and the rest are labeled hk ... h1 according to their position from
 * the right.
 */
Expr.prototype.hypLocater = function(hyp) {
  var h = new Atom('h');
  // Note: positions start with 1 at the right end of the chain.
  function locater(self, pos) {
    if (hyp.matches(self)) {
      return h;
    } else if (!self.isCall2('&')) {
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
 * Treating this as a conjunctive chain of assumptions, returns an
 * equation with LHS and RHS both chains.  The LHS has 'h' wherever
 * this chain has an element matching toMove, otherwise hk where k is
 * the 1-based index of the chain element in this chain.  The RHS has
 * the same variables in order, but at most one occurrence of 'h' as
 * its last chain element.
 *
 * In other words this generates an equation tautology that works with
 * rules.rewrite to remove duplicate occurrences of the given term and
 * put a single occurrence of it at the right end of the chain.
 *
 * TODO: Consider adding Step.eachAsm.
 */
Expr.prototype.hypMover = function(toMove) {
  // TODO: Re-implement to work with any conjunct in a tree of conjuncts,
  // replacing its occurrences by T and adding it to the end, then
  // deduplicating with conjunctionArranger.
  var i = 1;
  var lhs = null;
  var rhs = null;
  var found = false;
  this.scanConj(function(term) {
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
 * Taking this expression as a chain of assumptions, applies the given
 * action function to each conjunct in the chain, going from left to
 * right.
 *
 * If the action returns a truthy value given any asm, that value
 * immediately becomes the value of the call.  Otherwise returns
 * the value of the last call to the action.
 */
Expr.prototype.scanConj = function(action) {
  if (this.isCall2('&')) {
    return (this.getLeft().scanConj(action) ||
            action(this.getRight()));
  } else {
    return action(this);
  }
};

/**
 * Returns a map from path string to term, containing all terms of the
 * step that are assumptions; empty if there are no assumptions.
 * The paths use /left and /right.
 */
Step.prototype.asmMap = function() {
  const scan = function(expr, pathStr) {
    if (expr.isCall2('&')) {
      scan(expr.getLeft(), pathStr + '/left');
      asms.set(pathStr + '/right', expr.getRight());
    } else {
      asms.set(pathStr, expr);
    }
  };
  const asms = new Map();
  if (this.wff.isCall2('=>')) {
    scan(this.getLeft(), '/left');
  }
  return asms;
};

/**
 * Taking this is a tree of disjuncts, applies the given action
 * function to each leaf node, in order from left to right.  If any
 * call returns a truthy value, that becomes immediately the result,
 * stopping the tree traversal.  The action is applied only to leaf
 * nodes, i.e. ones that are not themselves disjunctions.
 */
Expr.prototype.scanDisjuncts = function(action) {
  if (this.isCall2('|')) {
    return (this.getLeft().scanDisjuncts(action) ||
            this.getRight().scanDisjuncts(action));
  } else {
    return action(this);
  }
};

/**
 * Taking this is a tree of conjuncts, applies the given action
 * function to each leaf node, in order from left to right.  If any
 * call returns a truthy value, that becomes immediately the result,
 * stopping the tree traversal.  The action is applied only to leaf
 * nodes, i.e. nodes that are not themselves conjunctions.
 */
Expr.prototype.scanConjuncts = function(action) {
  if (this.isCall2('&')) {
    return (this.getLeft().scanConjuncts(action) ||
            this.getRight().scanConjuncts(action));
  } else {
    return action(this);
  }
};

/**
 * Makes a new TermSet of all the conjuncts obtained by
 * applying scanConjuncts to the given term, as for example
 * making the assumptions of a step into a TermSet.
 */
function makeConjunctionSet(term) {
  var set = new TermSet();
  term.scanConjuncts(function (t) { set.add(t); });
  return set;
}

/**
 * Build and return a TermSet containing the assumptions
 * of this wff.  If the wff is not conditional, returns
 * an empty set.
 */
Expr.prototype.asmSet = function() {
  return (this.isCall2('=>')
          ? Toy.makeConjunctionSet(this.getLeft())
          : new Toy.TermSet());
};

/**
 * Applies the given action to each conjunct in a chain of conjuncts,
 * from left to right, and a reverse path to the conjunct.  If any
 * action returns a truthy value, immediately returns that value.
 */
Expr.prototype.eachConjunct = function(action, rpath_arg) {
  const rpath = rpath_arg || Path.empty;
  if (this.isCall2('&')) {
    return this.getLeft()
      .eachConjunct(action, new Path('/left', rpath)) ||
      action(this.getRight(), new Path('/right', rpath));
  } else {
    return action(this, rpath);
  }
};

/**
 * Transforms an expression that is a chain of conjuncts by applying
 * the xform function to each of its conjuncts.  To match scanConj,
 * descends into left-hand arguments, but does not descend into
 * right-hand arguments of '&'.
 *
 * TODO: Use or remove.
 */
Expr.prototype.transformConjuncts = function(xform) {
  if (this.isCall2('&')) {
    return infixCall(this.getLeft().transformConjuncts(xform),
                     '&',
                     xform(this.getRight()));
  } else {
    return xform(this);
  }
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
    path = Toy.asPath('');
  }
  var op = this.isCall2() && this.getBinOp().name;
  return (test(this, path) ||
          (op && op in _searchTermsOps &&
           (this.getRight().searchTerms(test, new Path('right', path)) ||
            this.getLeft().searchTerms(test, new Path('left', path)))));
};

/**
 * Searches for a patternInfo whose "match" property matches this
 * term.  If it finds one, then for each schema variable that has a
 * specified action function, applies the function at each of the
 * variable's occurrences in the matching schema, passing it the
 * subexpression of this that matches and a reverse path from this to
 * the occurrence.  Does not return a value, but Toy.returnFrom can be
 * useful for returning a value.  The search through patterns proceeds
 * left to right.
 *
 * The patternInfo is a plain object with property "match" being the
 * schema to match, and (usually) properties named after variables in
 * the schema, the value of each being the action function for that
 * schema variable.
 *
 * The optional path argument is a path that will be prepended to the
 * path passed to the path passed to any patternInfo function that may
 * be called.
 */
Expr.prototype.walkPatterns = function(patternInfos, path_arg) {
  var self = this;
  const cxtPath = path_arg || Path.empty;
  function handleTerm(schemaTerm, revPath) {
    // Note this is defined outside the loop, but it uses patternInfo
    // and map, which are in scope in JavaScript.
    if (schemaTerm.isVariable()) {
      var name = schemaTerm.name;
      if (name && patternInfo[name]) {
        // Call the function associated with the name of this
        // variable in the schema.
        patternInfo[name].call(null, map[name],
                               cxtPath.concat(revPath.reverse()));
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
// OOPS, this does not dump any type information, so it may conflate
// terms that are not really the same.  It is not relied on by
// deduction, so the flaw is non-fatal.
//
// Internal calls accept a Bindings object as an argument.
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
// _subFree(Object map, Object newFreeVars)
//
// The map argument is an object mapping variable names to replacement
// expressions.  Substitutes the corresponding replacement expression
// for each free occurrence of each name in this Expr.  Also copies
// type information to all newly-created terms as needed for the
// operation of Axiom 4.
//
// newFreeVars must be given as an object / set of all names free in any
// of the replacement expressions.
//
// To ensure no names are captured, renames all bound variables in
// this that have the same name as any free variable in the
// replacement terms.
//
// Note that Rule R can introduce previously free variables into a
// scope where they become bound.
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
// _addNames(map result)
//
// Adds all names occurring in this expression to the object/map, with
// value of true for each, both free and bound names.
//
//
// _addFreeVars(Set result, Bindings bindings)
// 
// Adds all variable names that occur free in this Expr to the result
// Set.  Assumes that names in the Bindings object are bound in this
// expression's lexical context.  Private helper for the freeVars
// method.
//
//
// _addNewConstants(map result, Bindings bindings)
// 
// Adds to the object/set all constant names that occur free in this
// Expr and are "new" in the sense of isNewConstant.  Assumes that
// names in the Bindings object are bound in this expression's lexical
// context, even if they have the form of named constants (so constant
// names could be used for bound variables if desired).  Private
// helper for the newConstants method.
//
//
// _boundNames(path, bindings)
//
// Returns a Bindings object (or null if no bindings) representing the
// set of bindings in effect at the given path within this Expr, plus
// the given bindings.  Binds name to variable Atom.
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
// corresponding parts of the argument.  If present anywhere, types
// must also match.  Type variable names may differ (only renamings).
//
//
// matches(e2, bindings)
//
// Tests whether all components of this expression and e2 are the same
// except for names of bound variables.  Names of constants and free
// variables must match in each component.  Names of bound variables
// may differ if the bindings map the name in this to the name in e2.
// The bindings map from names of variables bound in expressions
// containing this expression to corresponding variable names of the
// expression containing e2.  Currently does not match types.
//
//
// _traverse(fn, rpath)
//
// Applies the function to this expression, then recursively to any
// subexpressions.  Does not descend into the variable binding parts
// of Lambdas.  Used on rendered steps, perhaps also non-rendered.
//
// TODO: Consider how to support flexible paths better, with /main.
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
// Search order is right to left (arg before fn in calls), but parents
// before children.
//
//
// _prettyPath(pred, path)
//
// Like _path, but for infix expressions produces /left, /right, etc.
// rather than combinations of /fn and /arg; and returns a forward
// path.
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
// attempts to do the same traversal of expr2, and calls action2
// where expr2 has a part corresponding to the part in expr1.
//
//
// _matchAsSchema(expr, substitution, bindings)
//
// Checks that this expression matches the argument expression under
// the given substitution (map from names in this to expressions in
// expr).  The bindings indicate the variable bindings in effect for
// this and the argument expression, mapping from variable name in
// this to variable name in expr.
//
// Returns true iff it does and extends the substitution to a
// new variable if needed to make this and the argument match.  If
// this contains lambda expressions, it is smart about match failure
// due to capturing of free variables in the expr, and smart about
// using calls to function variables in this to enable substitution in
// spite of capturing.  Matching here is as defined for the "matches"
// method.
//
// Where needed and possible, this matches (boolean) terms with lambda
// terms and attaches a %expansion property to the substitution, with
// the names of each such predicate variable mapped to a count of the
// number of beta reductions needed to match normally after
// substitution.
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
// searchMost(fn, opt_path, opt_bindings)
//
// Tree walks though this Expr and its subexpressions, recursively,
// calling the function to each one, passing it the term and a reverse
// path from this term to that point until the function returns a
// truthy value.  Descends first into the arg part to make the search
// proceed right to left.  All subexpressions of Lambda terms receive
// non-null bindings, mapping the name of the bound variable to the
// lambda in which it is bound, innermost first.  Returns the first
// truthy value returned from "fn" at any level.  If not given, this
// treats the path and bindings as empty.
*/

//// Methods for Atom

/**
 * If not producing Unicode, returns this Atom's pname.  If producing
 * Unicode, and if the pname has a Unicode counterpart, returns that
 * counterpart, otherwise just the pname.  Boolean equality is "==".
 */
Atom.prototype._toString = function() {
  const text = (useUnicode
                ? this.unicodeName()
                : this.isEquivOp()
                ? '=='
                : this.pname);
  const show = Toy.showTypes;
  return (show && this.type &&
          (show === 'atoms' || show === 'testing' || this.isVariable())
          ? text + ":" + this.type.toString()
          : text);
};

/**
 * Unicode rendering of the name of this Atom.
 */
Atom.prototype.unicodeName = function() {
  // Always show boolean equality as such.
  // Using pname helps here in some obsolescent usage.
  const name = this.isEquivOp() ? '==' : this.pname;
  var uname = unicodeNames[name];
  if (uname) {
    return uname;
  }
  var info = this.parseName();
  var result = info.name;
  if (info.sub) {
    // Convert it to a Unicode subscript.
    //
    // Caution: browsers (e.g. Chrome) do not correctly display
    // Unicode subscript characters!  I see that the STIXGeneral font
    // has been deprecated for years.  Google fonts includes STIX Two
    // Text, and the STIX Two Text font as released by the STIX
    // project seems to include proper rendering of subscript chars,
    // but Google fonts omits those chars from its release.
    var offset = 0x2080 - '0'.charCodeAt(0);
    var sub = info.sub;
    for (var i = 0; i < sub.length; i++) {
      result += String.fromCharCode(sub.charCodeAt(i) + offset);
    }
  }
  return result;
};

// Translations of names, applied during conversion to Unicode.
// (When generating HTML and/or Unicode text.)
var unicodeNames = {
  '==': '\u2261',     // Triple equal (equiv)
  // or '==': '\u21d4',     // Two-headed horizontal double arrow.
  '&': '\u2227',      // &and;
  '|': '\u2228',      // &or;
  'not': '\u00ac',    // &not;
  '=>': '\u21d2',     // &rArr; ("implies") (\u27f9 is longer)
  '=>>': '\u21db',    // rightwards triple arrow
  '!=': '\u2260',     // &ne;
  '<=': '\u2264',     // &le;
  '>=': '\u2265',     // &ge;
  'in': '\u2208',     // &in;
  'notin': '\u2209',  // &notin;
  '**': '**',         // Dont change to sdots.
  '*': '\u22c5',      // &sdot;
  '-': '\u2212',      // &minus;
  '</': '</',         // Treat this as HTML.
  '/': '\u2215',      // division slash
  neg: '-',           // (different than "minus")
  empty: '\u2205',    // Null set
  iota: '\u2129',     // Inverted iota
  none: '\u22a5',     // Bottom / "up tack"
  R: '\u211d',        // Real numbers
  NN: '\u2115',       // Natural numbers
  forall: '\u2200',
  exists: '\u2203',
  exists1: '\u2203!'
};

// Defines aliases that affect both printing and parsing.
var aliases = {
  // Note that limiting '==' to boolean inputs would make it more than
  // just an alias as currently defined.
  '==': '=',
};

// This is useful in itself, but Expr.toHtml does not invoke this
// internally for Atoms.
// TODO: Fix Expr.toHtml.  
Atom.prototype.toHtml = function() {
  // Always show boolean equality as such.
  // Using pname helps here in some obsolescent usage.
  const name = this.isEquivOp() ? '==' : this.pname;
  var uname = unicodeNames[name];
  if (uname) {
    return uname;
  }
  var info = this.parseName();
  var text = info.name;
  if (info.sub) {
    text += `<sub>${info.sub}</sub>`;
  }
  // The lines below are the same as in Atom._toString:
  const show = Toy.showTypes;
  return (show && this.type &&
          (show === 'atoms' || show === 'testing' || this.isVariable())
          ? text + ":" + this.type.toString()
          : text);
};

// TODO: Consider whetheer it is worth fixing this to include type
// information.
Atom.prototype.dump = function() {
  return this.name;
};

Atom.prototype._subFree = function(map, freeVars, allNames) {
  // Note that in some cases it is important not to copy this
  // Atom if not necessary, e.g. when used within Axiom 4.
  return map[this.name] || this;
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

Atom.prototype._addFreeVars = function(set, bindings) {
  if (this.isVariable() && getBinding(this.name, bindings) == null) {
    set.add(this.name);
  }
};

Atom.prototype._addFreeVarSet = Atom.prototype._addFreeVars;

Atom.prototype._addNewConstants = function(set, bindings) {
  var name = this.name;
  if (this.isNamedConst() &&
      getBinding(name, bindings) == null &&
      !namedConstants.has(name)) {
    set.add(this.name);
  }
};

Atom.prototype._boundNames = function(path, bindings) {
  if (path.isMatch()) {
    return bindings;
  } else {
    this._checkSegment(path);
  }
};

Atom.prototype._addMathVars = function(bindings, set) {
  return false;
};

Atom.prototype.replaceAt = function(path, xformer) {
  return path.isMatch() ? xformer(this) : this;
};

Atom.prototype.matches = function(expr, bindings) {
  if (expr instanceof Atom) {
    var expectedName = getBinding(this.name, bindings) || this.name;
    return expr.name === expectedName;
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

Atom.prototype._prettyPath = function(pred, pth) {
  return pred(this) ? pth : null;
};

Atom.prototype._bindingPath = function(pred, revPath) {
  return null;
};

Atom.prototype._checkSegment = function(path) {
  assert(path === Path.empty,
         'Path {1} is not applicable to an Atom: {2}', path, this);
};

Atom.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.name == name) {
    action1(this);
    expr2 && action2(expr2);
  }
};

Atom.prototype._matchAsSchema = function(expr, map, bindings) {
  // This method does not return true when matching a defined name
  // with an expression that matches its definition; thus it does not
  // treat definitions exactly as abbreviations.
  if (this.isConst()) {
    // Expr must be an Atom with the same name.
    return this.matches(expr);
  }
  var name = this.name;
  var boundTo = getBinding(name, bindings);
  if (boundTo) {
    // This is a bound variable.  It matches iff the argument is the
    // corresponding bound variable in expr.
    return expr.name == boundTo;
  }
  // When within the scope of any bound variables, check that the
  // candidate substitution would not have to rename any variables in
  // expr, as this kind of matching is not defined to include
  // substitution into expr.
  var frees = bindings && expr.freeVars();
  for (var binding = bindings; binding; binding = binding.more) {
    if (frees[binding.to]) {
      return false;
    }
  }
  // This is a free variable.  If it already has a defined substitute,
  // check that it matches expr; otherwise add a mapping for it into
  // the substitution.
  var mapped = map[name];
  if (mapped) {
    return expr.matches(mapped, bindings);
  } else {
    map[name] = expr;
    return true;
  }
  return false;
};

Atom.prototype._matchAsPattern = function(term, map) {
  if (this.isConst()) {
    return this.matches(term);
  } else {
    // This is a variable.
    var value = map[this.name];
    if (value) {
      return value.matches(term);
    } else {
      map[this.name] = term;
      return true;
    }
  }
};

Atom.prototype._asPattern = function(term) {
  return this.__var || this;
};

Atom.prototype.searchMost = function(fn, path, bindings) {
  return fn(this, path, bindings);
};


//// Utilities for Atoms

/**
 * Return the Atom v, or if the argument is a string, create a new
 * variable from it.  The name must be legal for a user-created
 * variable.
 */
function varify(v) {
  var v = (typeof v == 'string') ? new Atom(v) : v;
  if (!v.isVariable()) {
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
 * Converts a JS number to a numeric constant, checking that it
 * it is acceptable as a numeric constant.
 */
function numify(num) {
  assert(typeof num === 'number');
  Toy.checkRange(num);
  assert(Math.floor(num) === num);
  return Toy.constify(num.toFixed(0));
}

/**
 * Returns the string name given if it is not in existingNames, an
 * object or Set with name strings as keys.  Otherwise returns a
 * generated name with the same "base" as the one given, and not in
 * existingNames.  The base is the name with any trailing digits
 * removed.  The generated suffix will be the lowest-numbered one not
 * yet in use, starting with "1".
 */
function genName(name, existingNames) {
  var base = name[0];
  var candidate = name;
  if (existingNames instanceof Set) {
    for (var i = 10; existingNames.has(candidate); i++) {
      candidate = base + '_' + i;
    }
  } else {
    for (var i = 1; existingNames[candidate]; i++) {
      candidate = base + '_' + i;
    }
  }
  return candidate;
}

/**
 * Returns a new Atom with a name generated by genName.
 */
function genVar(name, existingNames) {
  return new Atom(genName(name, existingNames));
}

/**
 * Generates a new bound variable with new name; private to
 * Expr.subFree, which guarantees that the variable will never
 * appear free.  Private to Expr.subFree.
 */
function _genBoundVar(name, freeVars) {
  // Use only the first letter of the previous name to
  // avoid names with multiple numeric parts.
  let newName;
  let counter = 10;
  while ((newName = name[0] + '_' + counter++) in freeVars) {}
  return new Atom(newName);
}

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


//// Methods for Call -- application of a function to an argument

Call.prototype._toString = function() {
  if (this._string) {
    return this._string;
  }
  if (this.isCall2()) {
    const op = this.getBinOp();
    if (isInfixDesired(op)) {
      if (useUnicode && op.name == '**') {
        // Use HTML for exponentiation.  So "Unicode" here is
        // currently a misnomer.
        return this.getLeft() + '<sup>' + this.getRight() + '</sup>';
      } else {
        const opStr = op._toString();
        return ('(' + this.getLeft() + ' ' + opStr +
                ' ' + this.getRight() + ')');
      }
    } else {
      return ('(' + op + ' ' + this.getLeft() +
              ' ' + this.getRight() + ')');
    }
  } else {
    return '(' + this.fn + ' ' + this.arg + ')';
  }
};

/**
 * TODO: Return a reverse path instead of the item, so we can find
 * the place to rewrite.
 *
 */
Call.prototype.pathIntoChain = function(n, ops_arg) {
  // Every "chain" consists of at least one binary operator and at
  // least two operands, numbered starting from 0 on the right.  So n
  // operators support up to n+1 operands, but if there are n+1
  // operands, the last segment of the path is left rather than right.
  const ops = (typeof ops_arg == 'string'
               ? [ops_arg]
               : Array.isArray(ops_arg)
               ? ops_arg
               : assert(false, 'Bad argument'));
  const inChain = term => term.isCall2() && ops.includes(term.getBinOp().name);
  // assert(inChain(this), 'No chain of operators');
  if (!inChain(this)) {
    return null;
  }
  for (let i = 0,
         // In each iteration revPath will lead to opTerm.
         revPath = Path.empty,
         // In each iteration, opTerm provides access to operand i,
         // and if it is the last of the chain, to operand i+1.
         opTerm = this;

       // Iterate up to n+1 times.
       i <= n;

       i++,
         opTerm = opTerm.getLeft(),
         revPath = new Path('left', revPath)) {
    if (inChain(opTerm)) {
      if (i == n) {
        // There are at least n + 1 suitable operators in the chain, so
        // the last segment is rightward, e.g. one operator and n = 0.
        return new Path('right', revPath);
      }
      // i has not reached n yet, so continue down the chain.
    } else if (i == n) {
      // If there are exactly n operators in the chain, revPath leads
      // to the element.
      return revPath;
    } else {
      // There are not enough operators in the chain.
      // assert(false, 'No chain element #{1}', n);
      return null;
    }
  }
  return null;
};

Call.prototype.dump = function() {
  return '(' + this.fn.dump() + ' ' + this.arg.dump() + ')';
};

Call.prototype._subFree = function(map, freeVars, allNames) {
  var fn = this.fn._subFree(map, freeVars, allNames);
  var arg = this.arg._subFree(map, freeVars, allNames);
  if (fn == this.fn && arg == this.arg) {
    return this;
  } else {
    return new Call(fn, arg);
  }
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

Call.prototype._addFreeVars = function(set, bindings) {
  // Add the arg first to encourage right-to-left ordering in typical
  // implementation iteration.
  this.arg._addFreeVars(set, bindings);
  this.fn._addFreeVars(set, bindings);
};

Call.prototype._addFreeVarSet = function(set, bindings) {
  this.fn._addFreeVarSet(set, bindings);
  this.arg._addFreeVarSet(set, bindings);
};

Call.prototype._addNewConstants = function(set, bindings) {
  this.arg._addNewConstants(set, bindings);
  this.fn._addNewConstants(set, bindings);
};

Call.prototype._boundNames = function(path, bindings) {
  if (path.isMatch()) {
    return bindings;
  } else {
    return this.descend(path.segment)._boundNames(path.rest, bindings);
  }
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
    var isLeftReal = left._addMathVars(bindings, set);
    var isRightReal = right._addMathVars(bindings, set);
    if (op == '=' || op == '!=') {
       if (isLeftReal && isFreeVar(right)) {
        set[right.name] = true;
      }
      if (isRightReal && isFreeVar(left)) {
        set[left.name] = true;
      }
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
        return infixCall(this.getLeft().replaceAt(path.rest, xformer),
                         this.getBinOp(),
                         this.getRight());
      } else if (segment === 'binop') {
        return infixCall(this.getLeft(),
                         this.getBinOp().replaceAt(path.rest, xformer),
                         this.getRight());
      } else if (segment === 'right') {
        return infixCall(this.getLeft(),
                         this.getBinOp(),
                         this.getRight().replaceAt(path.rest, xformer));
      }
    }
    if (segment === 'fn') {
      return new Call(this.fn.replaceAt(path.rest, xformer), this.arg);
    } else if (segment === 'arg') {
      return new Call(this.fn, this.arg.replaceAt(path.rest, xformer));
    }
    this._checkSegment(path);
  }
};

Call.prototype.matches = function(expr, bindings) {
  if (expr === this && bindings === undefined) {
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
    : this.arg._path(pred, new Path('arg', revPath))
      || this.fn._path(pred, new Path('fn', revPath));
};

Call.prototype._prettyPath = function(pred, pth) {
  var p;
  if (pred(this)) {
    return pth;
  } else if (this.isInfixCall()) {
    p = this.getLeft()._prettyPath(pred, pth);
    if (p) {
      return new Path('left', p);
    }
    p = this.getBinOp()._prettyPath(pred, pth);
    if (p) {
      return new Path('binop', p);
    }
    p = this.getRight()._prettyPath(pred, pth);
    if (p) {
      return new Path('right', p);
    } else {
      return null;
    }
  } else {
    p = this.fn._prettyPath(pred, pth);
    if (p) {
      return new Path('fn', p);
    }
    p = this.arg._prettyPath(pred, pth);
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

// Keys in this object are legitimate paths to apply to a Call.
var _callSegmentNames = {fn: true, arg: true};

var _binopSegmentNames = {left: true, right: true, binop: true};

Call.prototype._checkSegment = function(path) {
  assert(this.isCall2()
         ? path.segment in _binopSegmentNames 
         : path.segment in _callSegmentNames,
         'Path segment {1} is not applicable to Call {2}', path.segment, this);
};

Call.prototype.findAll = function(name, action1, expr2, action2) {
  this.fn.findAll(name, action1, expr2 && expr2.fn, action2);
  this.arg.findAll(name, action1, expr2 && expr2.arg, action2);
};

Call.prototype._matchAsSchema = function(expr, map, bindings) {
  // If there is a match without introducing lambdas, use it.
  // Copy the substitution and restore it if necessary.
  var map2 = Object.assign({}, map);
  if (expr instanceof Call
      && this.fn._matchAsSchema(expr.fn, map, bindings)
      && this.arg._matchAsSchema(expr.arg, map, bindings)) {
    return true;
  }
  // TODO: If the arg is free in this context, consider doing a
  //   recursive call here thus excluding this arg from the
  //   more complex calculations here.
  //
  // First-order matching failed, so try a higher-order match.
  //
  // Clear the map to remove any additional substitutions tried and
  // restore the substitution to its state on entry to this method.
  Object.keys(map).forEach(function(key) { delete map[key]; });
  Object.assign(map, map2);
  var fn = this.func();
  if (fn && fn.isVariable() && !getBinding(fn.name, bindings)) {
    const matched = map[fn.name];
    if (matched) {
      // TODO: Consider making better use of Expr values computed by
      //   checkFnMatch here.
      const matcher = checkFnMatch(this, fn, expr, map, bindings);
      return !!matcher;
    } else {
      return addFnMatch(this, fn, expr, map, bindings);
    }
  }
};

/**
 * Returns an equation with term as LHS and RHS having all "head" lambdas
 * of the LHS beta reduced, just traversing "fn"s.
 *
 * TODO: Consider removing this as unused.  It is also an ugly piece
 *   of code.
 */
function multiReducer(term) {
  const rules = Toy.rules;
  let eqn = rules.eqSelf(term);
  if (!(term instanceof Call)) {
    return eqn;
  }
  // The path will be built as a reverse path, but all /fn so
  // it will be the same as its reverse.
  let path = Path.empty;
  let x = term;
  for (; x.fn instanceof Call; x = x.fn) {
    path = new Path('fn', path);
  }
  while (x.fn instanceof Lambda) {
    eqn = rules.reduce(eqn, new Path('right', path));
    if (path.isEnd()) {
      break;
    }
    path = path.rest;
    x = eqn.getRight().get(path);
  }
  return eqn;
}

/**
 * This attempts to confirm that the schema, a call to a function
 * variable, with one or more arguments, constitutes a higher-order
 * match with "expr", combined with an established substitution into
 * the schema defined by the map for the given function variable "fn".
 * If it does, returns a proved equation from the schema to a term
 * that "matches" expr in this binding context, otherwise null.
 * Internal to _matchAsSchema.
 *
 * As currently implemented, this does not actually beta reduce
 * "expr".
 */
function checkFnMatch(schema, fn, expr, map, bindings) {
  const name = fn.name;
  const lambdas = map[name];

  // The path will be built as a reverse path, but all /fn so
  // it will be the same as its reverse.
  let path = Path.empty;
  for (let term = schema;
       term instanceof Call && term.fn instanceof Call;
       term = term.fn) {
    path = new Path('fn', path);
  }
  const reducer =
        () => Toy.rules.consider(schema).andThen('instVar', lambdas, name);
  let reduced = Toy.catching(reducer);
  if (reduced instanceof Error) {
    console.error(reduced);
    return null;
  }
  while (path !== Path.empty) {
    const reducible = reduced.getRight();
    if (reducible.matches(expr, bindings)) {
      return reduced;
    }
    if (reducible.isLambdaCall()) {
      reduced = rules.reduce(reduced, '/right');
    } else {
      return null;
    }
    path = path.rest;
  }
}

/**
 * For each substitution map that has expansions of terms into
 * lambdas, a count of the number of expansions applied to
 * each such term.  Maybe a good idea, but currently unused.
 */
Toy.betaExpansions = new WeakMap();

/**
 * Given a schema that is a function call whose function is a
 * variable, this attempts to build a lambda term or nested lambda
 * terms to substitute for the variable, resulting in the given expr
 * after also beta reducing the calls to those lambda(s).  Returns
 * true and extends the map on success, as for _matchAsSchema.  On
 * success, this works in the context of the given bound variable
 * renamings from the schema to the matched term.  Internal to
 * _matchAsSchema.
 */
function addFnMatch(schema, fn, expr, map, renamings) {
  // Key point: Suppose all variables bound in the context of the
  // schema, whose counterparts of the same name occur free in expr,
  // appear as actual arguments to the function, we can find a
  // substitution.
  var args = schema.args();
  // These are free in expr, but may be bound in expr's context.
  var exprVars = expr.freeVarSet();
  // If any variable occurring (free) in expr is bound in expr's
  // context and thus needs to have a bound variable here
  // substituted for it, but that bound variable is not in the args,
  // the substitution fails.
  var findBindingValue = Toy.findBindingValue;
  for (var name of exprVars) {
    var b = findBindingValue(name, renamings);
    if (b) {
      var argName = b.from;
      if (!args.find(arg => arg.isVariable() && arg.name == argName)) {
        return false;
      }
    }
  }

  // Now we know the function call arguments are suitable.  Construct
  // a lambda to substitute for the function variable.
  var result = expr;
  var arg;
  // This will be the number of beta reductions to apply after the
  // substitution.
  var expansions = 0;
  const vList = Array.from(exprVars);
  while (args.length) {
    // This is the next actual argument to the function variable.
    var arg = args.pop();
    if (arg.isVariable()) {
      // This is non-null iff bound here.  Iff bound here, it
      // corresponds to a variable bound in expr.
      const exprName = getBinding(arg.name, renamings);
      // If it is a fresh variable, it will be substituted nowhere.
      var toBind = (exprName
                    ? new Atom(exprName)
                    : vList.length > 0
                    ? new Atom(vList.pop())
                    : expr.freshVar(arg.name));
      result = new Lambda(toBind, result);
      expansions++;
    } else {
      return false;
    }
  }
  var existing = map[fn.name];
  // Fail if there is an existing substitution and the computed
  // result does not match it.
  if (existing && !existing.matches(result)) {
    return false;
  }

  if (expansions > 0) {
    const bx = Toy.betaExpansions;
    var xpanded = bx.get(map);
    if (!xpanded) {
      xpanded = {};
      bx.set(map, xpanded);
    }
    xpanded[fn.name] = expansions;
  }
  // Substitute the lambda term for the function variable.
  map[fn.name] = result;
  // Report success without traversing this further.
  return true;
}

Call.prototype._matchAsPattern = function(term, map) {
  return (term instanceof Call &&
          this.fn._matchAsPattern(term.fn, map) &&
          this.arg._matchAsPattern(term.arg, map));
};

Call.prototype._asPattern = function(term) {
  return this.__var || new Call(this.fn._asPattern(), this.arg._asPattern());
};

Call.prototype.searchMost = function(fn, path, bindings) {
  return (fn(this, path, bindings) ||
          // Try the arg first to help substitutions apply toward the
          // right sides of formulas.
          this.arg.searchMost(fn, new Path('arg', path), bindings) ||
          this.fn.searchMost(fn, new Path('fn', path), bindings));
};


//// Methods for Lambda -- variable bindings

Lambda.prototype._toString = function() {
  if (this._string) {
    return this._string;
  }
  // TODO: Fix dependencies so we can display with arrows
  // even when producing ASCII text.  That probably means fixing
  // parsing to handle the arrows.
  if (useUnicode) {
    const type = this.type;
    if (type && type.isSetType() && !type.fromType.equal(Toy.boolean)) {
      return '{' + this.bound + '. ' + this.body + '}';
    } else {
      return '(' + this.bound + '. ' + this.body + ')';
    }
  } else {
    return '{' + this.bound + '. ' + this.body + '}';
  }
};

Lambda.prototype.dump = function() {
  return '{' + this.bound.dump() + '. ' + this.body.dump() + '}';
};

Lambda.prototype._subFree = function(map, freeVars, allNames) {
  const boundName = this.bound.name;
  const savedRebinding = map[boundName];
  if (savedRebinding) {
    // A variable to be substituted is bound here.  Remove it from the
    // map during substitution in this scope.
    delete map[boundName];
    // If there are no other entries in the map, restore the binding
    // and return this immediately.
    if (Toy.isEmpty(map)) {
      map[boundName] = savedRebinding;
      return this;
    }
  }
  let result;
  if (boundName in freeVars) {
    // The bound name here appears as a free variable in some
    // replacement expression.  Rename the bound variable to ensure
    // there will be no capturing. We do this without checking whether
    // capturing actually would occur.  This also renames it if there
    // are free occurrences of a variable of the same name before the
    // substitution.
    const newVar = genVar(boundName, allNames);
    allNames[newVar.name] = true;
    // TODO: Consider updating the map and doing one substitution
    //   rather than two.
    const newBody = this.body._subFree(Toy.object0(boundName, newVar),
                                       freeVars, allNames);
    const renamed = new Lambda(newVar, newBody);
    // Substitute into the modified Lambda term.
    result = renamed._subFree(map, freeVars, allNames);
  } else {
    const newBody = this.body._subFree(map, freeVars, allNames);
    // Don't copy anything if no substitution is actually done.
    if (newBody === this.body) {
      result = this;
    } else {
      result = new Lambda(this.bound, newBody);
    }
  }
  if (savedRebinding) {
    map[boundName] = savedRebinding;
  }
  return result;
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

Lambda.prototype._addFreeVars = function(set, bindings) {
  var name = this.bound.name;
  this.body._addFreeVars(set, new Bindings(name, true, bindings));
};

Lambda.prototype._addFreeVarSet = function(set, bindings) {
  var name = this.bound.name;
  this.body._addFreeVarSet(set, new Bindings(name, true, bindings));
};


Lambda.prototype._addNewConstants = function(set, bindings) {
  var name = this.bound.name;
  this.body._addNewConstants(set, new Bindings(name, true, bindings));
};

Lambda.prototype._boundNames = function(path, bindings) {
  if (path.isMatch()) {
    return bindings;
  } else {
    var newBindings = new Bindings(this.bound.name, this.bound, bindings);
    var segment = path.segment;
    var rest = path.rest;
    if (segment === 'bound') {
      return this.bound._boundNames(rest, newBindings);
    } else if (segment === 'body') {
      return this.body._boundNames(rest, newBindings);
    }
    throw new Error('Path segment "' + segment +
                    '" is not applicable to a Lambda: ' + this);
 
  }
};

Lambda.prototype._addMathVars = function(bindings, set) {
  this.body._addMathVars(new Bindings(this.bound.name, true, bindings), set);
  return false;
};

Lambda.prototype.replaceAt = function(path, xformer) {
  if (path.isMatch()) {
    return xformer(this);
  } else if (path.segment === 'body') {
    var body = this.body.replaceAt(path.rest, xformer);
    return (body == this.body) ? this : new Lambda(this.bound, body);
  }
  this._checkSegment(path);
};

Lambda.prototype.matches = function(expr, bindings) {
  if (expr === this && bindings === undefined) {
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
  // This does not descend into lambdas, though fn could potentially
  // do so.
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
  return (body == this.body) ? this : new Lambda(this.bound, body);
};

Lambda.prototype._path = function(pred, revPath) {
  return pred(this)
    ? revPath
    : this.body._path(pred, new Path('body', revPath));
};

Lambda.prototype._prettyPath = function(pred, pth) {
  if (pred(this)) {
    return pth;
  } else {
    var p = this.body._prettyPath(pred, pth);
    return p ? new Path('body', p) : null;
  }
};

Lambda.prototype._bindingPath = function(pred, revPath) {
  return (pred(this.bound)
          ? revPath
          : this.body._bindingPath(pred, new Path('body', revPath)));
};

Lambda.prototype._checkSegment = function(path) {
  var segment = path.segment;
  assert(segment === 'bound' || segment === 'body',
         'Path segment {1} is not applicable to a Lambda: {2}',
         segment, this);
};

Lambda.prototype.findAll = function(name, action1, expr2, action2) {
  if (this.bound.name != name) {
    this.body.findAll(name, action1, expr2 && expr2.body, action2);
  }
};

Lambda.prototype._matchAsSchema = function(expr, map, bindings) {
  if (expr instanceof Lambda) {
    var extended = new Bindings(this.bound.name, expr.bound.name, bindings);
    return this.body._matchAsSchema(expr.body, map, extended);
  } else {
    return false;
  }
};

Lambda.prototype._matchAsPattern = function(term, map) {
  // TODO: Consider supporting matches with lambdas differing only by
  //   change of bound variable names.  Such a match presumably would
  //   not create any bindings in the substitution.
  return (term instanceof Lambda &&
          this.bound._matchAsPattern(term.bound, map) &&
          this.body._matchAsPattern(term.body, map));
};

Lambda.prototype._asPattern = function(term) {
  return this.__var || new Lambda(this.bound, this.body._asPattern());
};

Lambda.prototype.searchMost = function(fn, path, bindings) {
  return (fn(this, path, bindings) ||
          this.body.searchMost(fn, new Path('body', path),
                               new Bindings(this.bound.name, this, bindings)));
};

// Private methods grouped by name.

/**
 * Returns the term found inside here, or if not found, the first
 * index not seen.
 */
Atom.prototype._nthArg = function(n) {
  return n == 0 ? this : 1;
};

Call.prototype._nthArg = function(n) {
  var here = this.fn._nthArg(n);
  if (here instanceof Expr) {
    return here;
  } else if (n == here) {
    return this.arg;
  } else {
    return here + 1;
  }
};

Lambda.prototype._nthArg = function(n) {
  assert(false, 'Nth not relevant in lambdas');
};

/**
 * Given the wff of a rewrite rule, this returns true iff
 * the rule is conditional and every free variable of the RHS
 * also appears free in the LHS of the equation.  (If there
 * is no equation, this takes it as LHS == T.
 */
function neverWhenBound(rule) {
  // Consider the locally free variables in the term to be matched,
  // and a substitution that generates that term from some rewrite
  // rule.  Each of those free variables was either free in the
  // rewrite rule (and not replaced), or it was free in a replacement
  // term of the substitution.  Thus if every free variable of the
  // rule LHS also appears in its assumptions, then every free
  // variable of the result of the substitution into the LHS also
  // appears in the result of the substitution into the assumptions,
  // and the rule cannot apply if any of them are bound in that
  // context.
  // 
  return (rule.implies() &&
          (!rule.getRight().isCall2('=') ||
           Toy.setDiff(rule.getRight().freeVars(),
                       rule.getLeft().freeVars()).size === 0));
};

// Methods.

// The result of this method is very similar to toString, but this
// uses the "name" property, so aliases are treated as the same thing.
// Intended for use in identifying facts that match terms in steps.
Expr.prototype.toKey = function() {
  const key = x => {
    const c = x.constructor;
    if (c === Atom) {
      const isInfix = Toy.isInfixDesired(x);
      return isInfix ? '(' + x.name + ')' : x.name;
    } else if (c === Call) {
      if (x.isCall2()) {
        const op = x.getBinOp();
        if (isInfixDesired(op)) {
          return ('(' + key(x.getLeft()) + ' ' + op.name +
                  ' ' + key(x.getRight()) + ')');
        } else {
          return ('(' + key(op) + ' ' + key(x.getLeft()) +
                  ' ' + key(x.getRight()) + ')');
        }
      } else {
        return '(' + key(x.fn) + ' ' + key(x.arg) + ')';
      }
    } else if (c === Lambda) {
      return '{' + key(x.bound) + '. ' + key(x.body) + '}';
    } else {
      abort('Bad input: {1}', x);
    }
  }
  return key(this);
};


//// Export public names.

Toy.assertEqn = assertEqn;

Toy.TermSet = TermSet;
Toy.TermMap = TermMap;

Toy.Expr = Expr;
Toy.Step = Step;
Toy.Atom = Atom;
Toy.Call = Call;
Toy.Lambda = Lambda;

Toy.varify = varify;
Toy.constify = constify;
Toy.numify = numify;
Toy.isConstantName = isConstantName;
Toy.isVariableName = isVariableName;
Toy.isIdentifier = isIdentifier;
Toy.isIntegerLiteral = isIntegerLiteral;
Toy.isFraction = isFraction;
Toy.checkRange = checkRange;
Toy.isProved = isProved;

Toy.showTypes = false;
Toy.unicodeNames = unicodeNames;
Toy.makeConjunctionSet = makeConjunctionSet;

Toy.genName = genName;
Toy.genVar = genVar;

Toy.namedConstants = namedConstants;
Toy.addConstants = addConstants;

Toy.multiReducer = multiReducer;
Toy.addFnMatch = addFnMatch;
Toy.checkFnMatch = checkFnMatch;

Toy.neverWhenBound = neverWhenBound;

// Private to xutil.js:
Toy._identifierPattern = identifierPattern;

})();
