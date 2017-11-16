// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

// Utilities for types, parsing, and definitions, building
// on expressions.

// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

// Make some names available without prefix.
var Expr = Toy.Expr;
var Atom = Toy.Atom;
var Call = Toy.Call;
var Lambda = Toy.Lambda;
var assert = Toy.assertTrue;
var err = Toy.err;
var Path = Toy.Path;
var path = Toy.path;

////
//// Extended Utilities that may depend on expr.js.
////


//// TYPE ANALYSIS

/**
 * Specialized error for use when type checking/inference fails.
 */
function TypeCheckError(msg) {
  // Do not call Error because that behaves specially,
  // just fill in a "message" property.
  this.message = msg;
}
Toy.extends(TypeCheckError, Error);


// Private to the TypeVariable constructor.
var _typeVarCounter = 1;

/**
 * Type variable constructor.  The name is optional, 't' followed by
 * digits if not given explicitly.  Names are currently required to
 * begin with 't' when parsed.  The "fresh" method assumes that all
 * distinct type variables have distinct names within the type
 * expression it is applied to.
 */
function TypeVariable(name) {
  // Type variables are often unified with other type variables or
  // resolved into more specific types.  When that happens, the
  // instance is set to some other type.  At the end of such a chain
  // is the actual resolved type.
  this.instance = null;
  if (name) {
    this.name = name;
  } else {
    this.name = 't' + _typeVarCounter++;
  }
}

TypeVariable.prototype.toString = function() {
  // Returns the dereferenced value without modifying
  // the internals.
  return this.instance ? this.instance.toString() : this.name;
};

/**
 * When applying the "fresh" operation to a type expression, the
 * resulting expression has the same structure as the input, but all
 * occurrences of each "generic" type variable are replaced with
 * occurrences of a "fresh" type variable distinct from all others.
 *
 * The mappings are from previous type variable names to new type
 * variable names.
 *
 * Note: with only top-level definitions, generic type variables are
 * exactly those in the types of defined constants, but definitions
 * in inner scopes can have mixed generic and non-generic type
 * variables.
 */
TypeVariable.prototype.fresh = function(mappings, nonGenerics) {
  var type = dereference(this);
  if (type instanceof TypeVariable) {
    var name = type.name;
    if (occursInList(name, nonGenerics)) {
      return type;
    } else {
      if (!mappings.hasOwnProperty(name)) {
        mappings[name] = new TypeVariable();
      }
      return mappings[name];
    }
  } else {
    // This is not really a variable after being dereferenced.
    return type.fresh(mappings, nonGenerics);
  }
};

/**
 * Type constant constructor.
 */
function TypeConstant(name) {
  this.name = name;
  this.types = [];
}
Toy.extends(TypeConstant, null);

var tcMethods = {
  toString: function() {
    return this.name;
  },

  fresh: function(mapping, nonGenerics) {
    return this;
  }
};
TypeConstant.addMethods(tcMethods);

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
  return dereference(this._type) || Toy.fail('Type not available: ' + this);
};

/**
 * Like getType, but returns a falsy value if there is no type
 * annotation.
 */
Expr.prototype.hasType = function() {
  return dereference(this._type);
};

/**
 * Returns the type of the expression like findType, but also
 * annotates the expression and all subexpressions with type
 * information as the _type property of each.  Every occurrence of any
 * shared structure must have the same type, so the definition must be
 * copied when replacing an occurrence of a defined constant.
 *
 * If this is already annotated, simply returns the annotation.
 */
Expr.prototype.annotateWithTypes = function() {
  return this._type || findType(this, true);
};

/**
 * Returns true iff the type of the term is Real.  Only ever returns
 * true if Expr is part of a WFF that has been annotated with type
 * information.
 */
Expr.prototype.isReal = function() {
  return this.hasType() == realType;
};

/**
 * Analyzed type of this is boolean, similarly to isReal.
 */
Expr.prototype.isBoolean = function() {
  return this.hasType() == boolean;
};

/**
 * Analyzed type of this is individual, similarly to isReal.
 */
Expr.prototype.isIndividual = function() {
  return this.hasType() == individual;
};

// TODO: Consider implementing a "mating" function to use in rule R to
// unify the type of the target site with the type of the term that
// will replace it.  The function must unify the two types and
// propagate the unification throughout the result.
//
// Note that if the type of the replacement term has no type variables
// in it, it can be used as-is with its types intact.  If the mating
// results in a replacement with no variables, the result might
// sensibly be cached for future use.  In some situations the result
// of rule R may have to be a completely new structure.

/**
 * Find and return the (dereferenced)type of an expression (Expr).
 * Throws an Error if type checking fails.  The error may have a
 * "cause" property with the original error (TypeCheckError).
 *
 * The second argument is private to annotateWithTypes.
 */
function findType(expr, annotate) {
  if (expr._type) {
    return dereference(expr._type);
  }

  // In this code types[i] will be the type of vars[i].
  // The vars are names of variables.  Bound variables and their types
  // are pushed onto the lists, and on exit from a scope the
  // information is popped off the lists.  Type lookups search from
  // the end toward the beginning thus finding the type of the
  // variable visible in the current scope.
  var vars = [];
  var types = [];
  // A list of TypeVariable objects that are not generic in the
  // current scope.  Type variables in the types of bound variables
  // appear here when their variable is in scope, and in types of free
  // variables they are inserted upon the first occurrence of the free
  // variable, and remain thereafter.
  // TODO: Consider removing nonGenerics, using just vars instead,
  //   Q0 does not have truly generic functions, just families of
  //   type-specific functions.
  var nonGenerics = [];
  //
  // Note: Generic type variables reflect the fact that different
  // occurrences of the same defined or primitive constant can have
  // different types.

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
    throw new TypeCheckError('Not an expression: ' + expr);
  }

  /**
   * Returns a type based on the name of an Atom.
   */
  function typeFromName(name) {
    if (Toy.isIntegerLiteral(name)) {
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
    if (Toy.isConstantName(name)) {
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
      console.warn(name, 'is defined but type is not recorded.');
      return findType(getDefinition(name).getRight());
    } else {
      throw new TypeCheckError('Cannot find type for: ' + name);
    }
  }

  function isGeneric(v) {
    return !occursInList(v, nonGenerics);
  }

  /**
   * Dereference the type to make sure its "instance" is the most
   * specific one available.  If it is a type operator, do the
   * same with its type arguments.
   */
  function tidy(type) {
    var t = dereference(type);
    if (t instanceof TypeOperator) {
      var types = t.types;
      for (var i = 0; i < types.length; i++) {
        tidy(t.types[i]);
      }
    }
  }

  /**
   * Tidy up the type information for the given expression and all of
   * its subexpressions.
   */
  function tidyAll(term) {
    if (term instanceof Call) {
      tidy(term.arg._type);
      tidy(term.fn._type);
    } else if (term instanceof Lambda) {
      tidy(term.body._type)
    }
    tidy(term._type);
  }

  try {
    var result = analyze(expr);
    if (annotate) {
      // If annotating, walk through all subexpressions of the expr,
      // tidying up their types, which are now all in final form.
      tidyAll(expr);
    } else {
      tidy(result);
    }
    return result;
  } catch(e) {
    if (e instanceof TypeCheckError) {
      var e2 = new TypeCheckError('Cannot find type for ' + expr.toUnicode());
      e2.cause = e;
      console.error(e);
      // Place a breakpoint here to help diagnose the problem.
      throw e2;
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

/**
 * Returns the given type, removing indirections in the representation
 * of type variables.
 *
 * Note that this is the identity function for objects that are not
 * type variables, including null and undefined.
 *
 * Also, unification mutates Type objects, so the result may mutate as
 * a result of any future unifications relevant to this type.
 */
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

/**
 * Returns a truthy value iff the term has been annotated with a type
 * and the type maps from 2 booleans to a boolean.
 */
function isBooleanBinOp(term) {
  var type = term.hasType();
  if ((type instanceof FunctionType) && dereference(type.types[0]) == boolean) {
    var t1 = dereference(type.types[1]);
    return ((t1 instanceof FunctionType) &&
            dereference(t1.types[0]) == boolean &&
            dereference(t1.types[1]) == boolean);
  } else {
    return false;
  }
}

function equalityType() {
  var v = new TypeVariable();
  return new FunctionType(v, new FunctionType(v, boolean));
}

/**
 * Function from individuals to individuals.
 */ 
function funType() {
  return new FunctionType(individual, individual);
}

/**
 * Function of two individuals, returning an individual.
 */
function fun2Type() {
  var v = individual;
  return new FunctionType(v, new FunctionType(v, v));
}

function theType() {
  var v = new TypeVariable();
  return new FunctionType(new FunctionType(v, boolean), v);
}

// Types of _primitive_ constants only here.
//
// TODO: Eliminate all but the truly primitive constants from this list
//   when functions and predicates can be properly defined.
//   According to current thinking, all functions here that apply to
//   real numbers should only apply to individuals, which still may
//   include many things besides real numbers.  So it looks like only
//   equality, iota, and "the" will have generic types.
//
// TODO: Consider using only boolean values here and using this just to
//   test whether a name is already defined.  The defining statement
//   presumably will give the constant its type.
var constantTypes = {
  T: boolean,
  F: boolean,
  '=': equalityType(),
  iota: theType(),

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
  div: fun2Type(),
  mod: fun2Type(),
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
  '=>': booleanBinOpType()
};

// Indexed by the name defined.  Value is an Expr (not a step) if the
// definition is simple.  If by cases, the value is a map from 'T' and
// 'F' to the definition for each case.  The "definition" rule justifies
// the defining WFF on each access.
//
// Primitive constants are here, but the definitions are truthy fakes.
// This prevents them from being defined later.
var definitions = {
  T: true,
  F: true,
  '=': true,
  iota: true
};

/**
 * Add a simple abbreviation-like definition, e.g.
 * define('forall', equal(lambda(x, T))).  Returns the equation.
 *
 * TODO: Require that the defining term only have (free) type
 *   variables that are also in the defined name.
 *
 * TODO: Consider replacing this function with one that takes a
 *   defining statement as its argument instead of a name and
 *   "definition".  It would automatically recognize certain forms
 *   such as [C = <term>] and [A => C = <term>], and arbitrary WFFs
 *   would also be supported if the apppropriate existence fact is
 *   already established.
 */
function define(name, definition) {
  assert(Toy.isConstantName(name), 'Not a constant name: {1}', name);
  definition = termify(definition);
  assert(definition instanceof Expr,
         'Definition must be a term: ' + definition);
  if (isDefined(name)) {
    assert(definition.matches(getDefinition(name)),
           'Already defined: ' + name);
    // Benign redefinition, do nothing.
    return;
  }
  var freeSet = definition.freeVars();
  if (!Toy.isEmpty(freeSet)) {
    var freeList = [];
    for (var nm in freeSet) {
      freeList.push(nm);
    }
    var names = freeList.join(', ');
    assert(false, 'Definition of {1} has free variable(s) {2}',
           name, names);
    return null;
  }
  constantTypes[name] = findType(definition);
  var defn = equal(Toy.constify(name), definition);
  definitions[name] = defn;
  return defn;
}

/**
 * Add a simple definition with true/false cases.  A call could
 * be something like defineCases('not', F, T).
 */
function defineCases(name, ifTrue, ifFalse) {
  assert(Toy.isConstantName(name), 'Not a constant name: ' + name);
  assert(!definitions.hasOwnProperty(name), 'Already defined: ' + name);
  ifTrue = termify(ifTrue);
  ifFalse = termify(ifFalse);
  for (var n in ifTrue.freeVars()) {
    assert(false, 'Definition has free variables: ' + name);
  }
  for (var n in ifFalse.freeVars()) {
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
 */
function getDefinition(name, tOrF) {
  var defn = findDefinition(name, tOrF);
  assert(defn, 'Not defined: ' + name);
  return defn;
}

/**
 * Finds a definition or by-cases definition in the definitions
 * database.  If the tOrF argument is present, the definition must be
 * by cases, otherwise simple.  Also accepts an Atom.
 *
 * Returns null if there is no such definition.
 */
function findDefinition(name, tOrF) {
  name = name instanceof Atom ? name.name : name;
  var defn = definitions[name];
  if (!defn) {
    return null;
  }
  if (!tOrF) {
    return defn instanceof Expr && defn;
  } else {
    if (tOrF == true || (tOrF instanceof Atom && tOrF.name == 'T')) {
      tOrF = 'T';
    } else if (tOrF == false || (tOrF instanceof Atom && tOrF.name == 'F')) {
      tOrF = 'F';
    }
    if (defn instanceof Expr) {
      return null;
    }
    var defnCase = defn[tOrF];
    return defnCase;
  }
}

/**
 * Defines the name (Atom or parseable string) using the definition,
 * which is a WFF or parseable string and proved statement (a step or
 * statement of a fact or theorem name).
 *
 * The proved statement must have the form "exists {v. A}", where
 * substituting the new constant for "v" in "{v. A}" gives a statement
 * that matches the given definition (up to changes of bound
 * variables).
 *
 * The proved statement must have no free variables, and only (free)
 * type variables that are in the bound variable of its main
 * existential quantifier.
 *
 * If the conditions are met, this asserts the given definition and
 * returns it.  It functions like an axiom, but with assurance that it
 * will not introduce any contradiction into the system.
 *
 * TODO: Consider supporting definition of multiple constants with one
 *   defining fact (with multiple existentially quantified variables).
 *
 * TODO: Test this.
 */
function definex(name_arg, fact) {
  var constant = Toy.constify(name_arg);
  var name = constant.name;
  var result = Toy.getTheorem(fact) || Toy.getResult(fact);
  if (result) {
    assert(result.isCall1('exists'), 'Not an existential statement', result);
    assert(result.arg instanceof Toy.Lambda, 'Not a lambda:', result.arg);
    var free = result.freeVars();
    assert(Toy.isEmpty(free), 'Definition must be a closed statement', result);
    var definition = result.arg.body.subFree1(constant, result.arg.bound);
    // TODO: Check for free type variables as specified.
    definitions[name] = definition;
  } else {
    assert(false, 'Not proved: ' + result);
  }
}


////
//// PARSING
////

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
                           Toy._identifierPattern,
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
 * In most cases the Unicode displays can serve as alternative names
 * for the more ASCCI-style tokens known to the parsing code.
 *
 * TODO: Consider making most or all non-ASCII operator characters
 * self-delimiting, meaning that a sequence of them is always a
 * sequence of tokens, never a single multi-character token.
 */
function _buildAltTokens() {
  var result = {};
  var map = Toy.unicodeNames;
  for (var name in map) {
    // Do not map a hyphen to unary negation.  It could be and very
    // often is "minus".
    if (name !== 'neg') {
      result[map[name]] = name;
    }
  }
  return result;
}

// Object/map from alternative token names to the standard internal
// token name.  Useful for pasting displays of formulas into text
// fields.  Private to Toy.tokenize.
var _altTokens = _buildAltTokens();


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
    var name = match[0];
    result.push(new Atom(_altTokens[name] || name, match.index));
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
    err({cause: e,
         message: 'Could not parse "' + input + '": ' + e.message});
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
   * Returns the second next token without consuming anything,
   * or the end token if two more tokens are not available.
   */
  function peek2() {
    return tokens[1] || end;
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
   * Given an operator to the left of some expression and one to its
   * right, should the left one take precedence?  E. g.
   *
   * e1 | e2 & ... , where leftOp is "|" and rightOp is "&", or
   * (p e1 ! ... , where leftOp is "(" and rightOp is "!", or
   * x + f a - ... , where leftOp is + and rightOp is -, or
   * We want f a - y to be (f a) - y.
   *
   * TODO: Support right-associative binary operators here.
   *
   */
  function hasPrecedence(leftOp, rightOp) {
    var left = getPrecedence(leftOp);
    var right = getPrecedence(rightOp);
    return left >= right;
  }

  /**
   * True iff the given precedence indicates a binary operator.
   */
  function isBinaryPower(power) {
    return 0 < power && power < namePower;
  }

  /**
   * Returns a truthy value iff the token is a unary or binary
   * operator.  (Not true for brackets.)
   */
  function isOperator(token) {
    var power = getPrecedence(token);
    return power == unaryPower || isBinaryPower(power);
  }

  /**
   * Parses zero or one expressions, stopping at the first operator
   * token it sees that does not bind tighter than the given one.
   * (Opening brackets cause recursive calls, so inner calls parse
   * inner closing brackets.)  Returns the parsed expression or null
   * if none is available.
   * 
   * This function is responsible for parsing a subexpression that was
   * preceded by an infix operator or opening "bracket", or start of
   * text.
   */
  function parse1Above(lastOp) {
    // This is a top-down operator precedence parser.
    var token = next();
    var name = token.name;
    var expr;
    if (name === '(') {
      var t1 = peek();
      if (isOperator(t1) && peek2().name === ')') {
        // Special case of "(<op>)", allowing a bare operator to
        // appear as an expression.
        next();
        next();
        return t1;
      } else {
        expr = mustParseAbove(whatever);
        expect(')');
        return expr;
      }
    } else if (name === '{') {
      var id = next();
      assert(id.isVariable(), 'Expected identifier, got ' + id.name);
      expect('.');
      var body = mustParseAbove(whatever);
      expr = lambda(id, body);
      expect('}');
      return expr;
    }
    var power = getPrecedence(token);
    // Handle unary operators, including "-".
    if (power === unaryPower) {
      return new Call(token, mustParseAbove(token));
    } else if (token.name === '-') {
      // If the leading token is '-', treat it as 'neg', or even as
      // part of a negative number.
      var peeked = peek();
      if (peeked.pos === token.pos + 1 && peeked.isNumeral()) {
        // If the "-" is directly adjacent, treat the whole thing
        // as a negative numeral.  The tokenizer will not build
        // a numeral with a leading "-".
        next();
        return new Atom('-' + peeked.name, token.pos);
      } else {
        var neg = new Atom('neg');
        return new Call(neg,  mustParseAbove(neg));
      }
    } else if (power === namePower) {
      return token;
    } else {
      return null;
    }
  }

  /**
   * Parses a sequence of one or more expressions, returning the one
   * expression or an appropriate Call for a sequence of two or more.
   * Throws an error if no expressions are available.
   *
   * Like parseAbove, always stops before any (top-level) token that
   * does not bind tighter than the given one.
   */
  function mustParseAbove(lastOp) {
    var left = parse1Above(lastOp);
    if (!left) {
      throw new Error('Empty expression at ' + peek().pos);
    }
    while (true) {
      var token = peek();
      if (hasPrecedence(lastOp, token)) {
        // Return the parse tree from the prior tokens.  The token may
        // still participate in an enclosing expression.
        return left;
      } else {
        var power = getPrecedence(token);
        if (isBinaryPower(power)) {
          next();
          left = infixCall(left, token, mustParseAbove(token));
        } else {
          var arg = parse1Above(lastOp);
          if (!arg) {
            return left;
          }
          left = new Call(left, arg);
        }
      }
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
  // A token of precedence 0.
  var whatever = new Atom('(end)');
  // Parse an expression.  A special "(begin)" delimiter does not seem
  // to be required, though note this does not require or even allow a
  // closing paren.
  var result = mustParseAbove(whatever);
  if (tokens.length) {
    throw new Error('Extra input: "' + tokens[0] + '"');
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
 * If string begins with "@", simply parses the rest with "parse".
 * Otherwise this also checks for any apparent math variables (as by
 * calling Expr.mathVars) and adds assumptions that all of those "math
 * variables" are real numbers.  If the main operator of the
 * expression is =>, concatenates any added assumptions and its LHS.
 */
function mathParse(str) {
  if (str[0] === '@') {
    return parse(str.slice(1));
  }
  var expr = justParse(str);
  var assume = expr.mathVarConditions();
  if (assume) {
    if (expr.isCall2('=>')) {
      // Any type assumptions precede the LHS.
      // These may later be matched against a proved result, so we aim
      // to achieve the usual ordering here.
      var result = infixCall(assume.concat(expr.getLeft(), '&'),
                             '=>',
                             expr.getRight());
      findType(result);
      return result;
    } else {
      var result = infixCall(assume, '=>', expr);
      result.hasHyps = true;
      findType(result);
      return result;
    }
  } else {
    findType(expr);
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
  var name = token.pname;
  if (precedence.hasOwnProperty(name)) {
    return precedence[name];
  } else {
    return (!Toy.isIdentifier(name) && !token.isLiteral()
            // It's written as an operator, give it the default precedence.
            ? 40
            // Otherwise it is a name.
            : namePower);
  }
}

// Unary operators should all be the same.
// No unary operators exist at this time, but the constant
// is used in rendering.
var unaryPower = 200;

// Alphanumeric names have this power unless specified otherwise.
var namePower = 100;

// Precedence table for infix operators.
var precedence = {
  // Closing tokens have power 0 to make infix parsing return.
  '(end)': 0,
  ')': 0,
  '}': 0,
  // Alias for '=', with lower precedence.
  // TODO: Use this for boolean equivalence when all terms are
  //   properly marked with types. 
  '==': 2,
  '=>': 11,
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
  // Infix operator meaning "if condition then value else none".
  '?': 25,
  '+': 30,
  '-': 30,
  '*': 40,
  '/': 40,
  div: 40,
  mod: 40,
  '**': 50,
  // Specials
  '(': 1000,
  '{': 1000
};

/**
 * Returns a truthy value iff this Expr is an Atom with a specific
 * precedence, so not a simple named or literal constant, nor a
 * variable.  This is used to control extra parenthesization when
 * such an Expr is rendered (or perhaps printed).
 */
Expr.prototype.isOperator = function() {
  return this instanceof Atom && this.pname in precedence;
};


//// UTILITY FUNCTIONS

// Unicode superscript digits.  Unfortunately 2 and 3 display
// differently than the rest in almost all fonts.
var superscripts = [
  '\u2070',
  '\u2071',
  '\u00b2',
  '\u00b3',
  '\u2074',
  '\u2075',
  '\u2076',
  '\u2077',
  '\u2078',
  '\u2079'
];

/**
 * Convert text to non-HTML Unicode.  Mainly useful for console
 * logging.  Use Toy.mathMarkup where HTML output is OK.
 */
function unicodify(text) {
  var pattern =
    /=>|==|!=|<=|>=|\s*\*\*\s*-?[0-9]+|\*\*|\*|-|<\/|\/|\bforall\b|\bexists\b/g;
  return text.replace(pattern, function(symbol) {
    var match;
    if ((match = symbol.match(/\s*\*\*\s*(-?)([0-9]+)/))) {
      // Part of the text matches an integer exponent.
      var sign = match[1] ? '\u207b' : '';
      var exponent = match[2];
      var supers = '';
      var zeroCode = '0'.charCodeAt(0);
      for (var i = 0; i < exponent.length; i++) {
        supers += superscripts[exponent.charCodeAt(i) - zeroCode];
      }
      return sign + supers;
    } else {
      return Toy.unicodeNames[symbol];
    }
  });
}

/**
 * Coerce the given Expr or string to an Expr by parsing it
 * if not an Expr.
 */
function termify(x) {
  return (x instanceof Expr) ? x : parse(x);
}

/**
 * Coerce the given Object to a string by taking its 'name' property
 * if it is not a string.  Expects a string or Atom.
 */
function namify(x) {
  return (typeof x === 'string') ? x : x.name;
}

var boolOps = {
  '==': true,
  '&': true,
  '|': true,
  '=>': true
};

// Boolean ops for looksBoolean.
var looseBoolOps = {
  '==': true,
  // This one is practical though a bit deprecated.  If it appears
  // with only the other boolean ops, it will generally work out.
  '=': true,
  '&': true,
  '|': true,
  '=>': true
};

/**
 * Given a term, returns a truthy value if it has the superficial
 * form of a statement in propositional calculus, using just the
 * usual boolean operators as for boolSchema, and the only other
 * constants present are T and F.
 */
function looksBoolean(term) {
  if (term instanceof Atom) {
    return term.isVariable() || term.name == 'T' || term.name == 'F';
  }
  if (term.isCall2()) {
    var op = term.getBinOp();
    return (op.pname in looseBoolOps &&
            looksBoolean(term.getLeft()) &&
            looksBoolean(term.getRight()));
  }
  if (term.isCall1('not')) {
    return looksBoolean(term.arg);
  }
  return false;
}

/**
 * Given a term, creates a new schema term that consists only of the
 * boolean operators (==, &, |, =>, and "not"), and variables, having
 * the original as a substitution instance.  Descends into all
 * occurrences of the boolean operators and no others, replacing all
 * other terms with boolean variables.  The schema variables are the
 * TermMap variables, in textual order from left to right.
 */
function boolSchema(term) {
  var map = new Toy.TermMap();
  var infix = Toy.infixCall;
  function makeSchema(term) {
    var v = map.get(term);
    if (v) {
      return v;
    }
    if (term.isCall2()) {
      var op = term.getBinOp()
      if (op.pname in boolOps) {
        return infix(makeSchema(term.getLeft()), op,
                     makeSchema(term.getRight()));
      }
    }
    if (term.isCall1('not')) {
      return new Toy.Call(term.fn, makeSchema(term.arg));
    }
    map.addTerm(term);
    return map.get(term);
  }
  return makeSchema(term);
}

/**
 * Convert all variables in the given term to standard names as by
 * TermMap, with those names in text order from left to right.
 */
function standardVars(term) {
  var map = new Toy.TermMap();
  function makeSchema(term) {
    if (term instanceof Toy.Call) {
      return new Toy.Call(makeSchema(term.fn),
                          makeSchema(term.arg));
    } else if (term instanceof Toy.Lambda) {
      var v = map.bindVar(term.bound);
      var result = new Toy.Lambda(v, makeSchema(term.body));
      map.unbind();
      return result;
    } else if (term instanceof Toy.Atom) {
      if (term.isVariable()) {
        return map.addTerm(term);
      } else {
        return term;
      }
    }
  }
  return makeSchema(term);
}

/**
 * True iff this expression has the form of a rewrite rule, being an
 * equation, possibly with assumptions, and all free variables in
 * assumptions appearing also in the LHS of the equation.  (This
 * eliminates facts such as transitivity of equality.)
 */
Expr.prototype.isRewriter = function() {
  var stmt = this;
  if (!stmt.isEquation()) {
    return false;
  }
  // Should statements like [R a & R b => (a = b == a + c = b + c)] be
  // treated differently?  (It introduces a new var in the RHS.)
  // This seems OK as it is.
  if (stmt.isCall2('=>')) {
    var asms = stmt.getLeft();
    var lhs = stmt.eqnLeft();
    var aFree = asms.freeVars();
    var lFree = lhs.freeVars();
    for (var name in aFree) {
      if (!(name in lFree)) {
        // Some free var in the assumptions is not free in the LHS.
        return false;
      }
    }
  }
  return true;
};
  

//// SIMPLE UTILITIES

/**
 * Calls a function given as an Expr or name of a constant, passing
 * one or more arguments.
 */
// TODO: Eliminate use of binops in favor of infixCall.  This will
// be problematic for some infix operators.
function call(fn, arg) {
  // TODO: Allow fn to be a variable name.
  fn = fn instanceof Expr ? fn : Toy.constify(fn);
  var result = new Call(fn, termify(arg));
  // Skip fn and the first "arg" after that.
  for (var i = 2; i < arguments.length; i++) {
    result = call(result, arguments[i]);
  }
  return result;
}

/**
 * Returns a call with the two operands and the given op (middle
 * argument) as the binary operator between them.  The op must be an
 * Expr or name of a constant.
 */
function infixCall(arg1, op, arg2) {
  // TODO: Change this when redefining meaning of infix operators.
  return call(op, arg1, arg2);
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
 * Builds an expression [lhs => rhs].
 */
function implies(lhs, rhs) {
  return call('=>', lhs, rhs);
}

/**
 * Builds a Lambda.  The "bound" argument may be a name, converted to
 * an Atom with varify.  If generating a bound variable
 * programmatically, call the Lambda constructor directly.
 */
function lambda(bound, body) {
  return new Lambda(Toy.varify(bound), body);
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
  return 0 < p && p < namePower;
}

/**
 * True iff the given Atom is a unary operator.  Method that applies
 * only to Vars.
 */
Atom.prototype.isUnary = function() {
  return getPrecedence(this) === 300;
}

/**
 * True iff the result of calling asmComparator is less than 0.
 * Useful for ordering deduplicated hypotheses.
 */
function asmLess(e1, e2) {
  return asmComparator(e1, e2) < 0;
}

/**
 * Comparator for Array.sort corresponding to asmLess.  Terms that are
 * calls to "R" come first, then abbreviations, then terms from
 * assumption steps come next, ordered by the step ordinal, and then
 * all others.  Value < 0 means e1 is less than e2.  Value is 0 iff
 * the terms are identical.
 */
function asmComparator(e1, e2) {
  function asmScore(e) {
    return (e.isCall1('R')
            ? 4
            : e.isAbbrevDef()
            ? 3
            : e.sourceStep
            ? 2
            : 1);
  }
  var s1 = asmScore(e1);
  var s2 = asmScore(e2);
  var diff = s1 - s2;
  if (diff) {
    return Math.sign(diff);
  }
  switch (s1) {
  case 4:
    return asmComparator(e1.arg, e2.arg);
  case 2:
    return e1.sourceStep.ordinal - e2.sourceStep.ordinal;
  case 3:
  case 1:
    var x1 = e1.dump();
    var x2 = e2.dump();
    return (x1 === x2
            ? 0
            : (x1 < x2 ? -1 : 1));
  }
  Toy.err('Internal error');
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
 * Given an operator name and a list of terms, produces a term
 * that is a "chain" of calls to the operator.  If the list
 * is emtpry, return the given default, or if just one item,
 * returns the item.
 */
function chainCall(operator, list, dfault) {
  if (list.length == 0) {
    return dfault;
  }
  // else
  var infix = Toy.infixCall;
  var result = list[0];
  for (var i = 1; i < list.length; i++) {
    result = infix(result, operator, list[i]);
  }
  return result;
}

/**
 * Commutes the left and right sides of an equation in the form
 * l = r or a => l = r.  Calls err if structure does not match.
 * Returns the same form of "=" found in the equation.
 */
function commuteEqn(eqn) {
  var infix = Toy.infixCall;
  var subst;
  if (subst = eqn.matchSchema('a = b')) {
    return infix(subst.b, eqn.getBinOp(), subst.a);
  } else if (subst = eqn.matchSchema('h => a = b')) {
    var op = eqn.getRight().getBinOp();
    return infix(subst.h, '=>', infix(subst.b, op, subst.a))
  } else {
    err(Toy.format('Not an equation: {1}', eqn));
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
      var ruleName = stepInfo.shift().name;
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

Toy.infixCall = infixCall;
Toy.call = call;
Toy.equal = equal;
Toy.implies = implies;
Toy.lambda = lambda;
Toy.isInfixDesired = isInfixDesired;

Toy.asmLess = asmLess;
Toy.asmComparator = asmComparator;
Toy.repeatedCall = repeatedCall;
Toy.chainCall = chainCall;
Toy.commuteEqn = commuteEqn;

Toy.encodeSteps = encodeSteps;
Toy.decodeSteps = decodeSteps;

Toy.unicodify = unicodify;

Toy.termify = termify;
Toy.namify = namify;

Toy.looksBoolean = looksBoolean;
Toy.boolSchema = boolSchema;
Toy.standardVars = standardVars;

// Definitions

Toy.define = define;
Toy.defineCases = defineCases;
Toy.definex = definex;
Toy.isDefined = isDefined;
Toy.isDefinedByCases = isDefinedByCases;
Toy.findDefinition = findDefinition;
Toy.getDefinition = getDefinition;
// For testing:
Toy.definitions = definitions;

// Types

Toy.boolean = boolean;
Toy.individual = individual;
Toy.realType = realType;
Toy.TypeCheckError = TypeCheckError;
Toy.TypeVariable = TypeVariable;
Toy.TypeConstant = TypeConstant;
Toy.TypeOperator = TypeOperator;
Toy.FunctionType = FunctionType;
Toy.parseType = parseType;
Toy.findType = findType;
Toy.isBooleanBinOp = isBooleanBinOp;

// Expression parsing

Toy.unaryPower = unaryPower;
Toy.namePower = namePower;
Toy.getPrecedence = getPrecedence;
Toy.tokenize = tokenize;
Toy.parse = parse;
Toy.justParse = justParse;
Toy.mathParse = mathParse;
Toy.parseStringContent = parseStringContent;

// For testing:
Toy._equalityType = equalityType;
Toy.unparseString = unparseString;
Toy._decodeArg = decodeArg;

// For debugging
Toy.nParsed = nParsed;
Toy._constantTypes = constantTypes;
Toy._dereference = dereference;

})();
