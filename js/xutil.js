// Copyright 2011 - 2018 Crispin Perdue.
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
 * Find and return the (dereferenced) type of an expression (Expr).
 * Throws an Error if type checking fails.  The error may have a
 * "cause" property with the original error (TypeCheckError).
 *
 * This uses established types of primitive and defined constants.  It
 * also allows new constants to appear, much like free variables.  It
 * registers the types of any such occurrences of new constants using
 * the same type analysis as for free variables.  This is intended for
 * parsing of new constant definitions.
 *
 * The second argument is private to annotateWithTypes.
 */
function findType(expr, annotate) {
  if (expr._type) {
    return dereference(expr._type);
  }
  Toy.ft++;

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
      return typeFromName(expr);
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
   * Returns the type of an Atom, based largely on its name.  May have
   * side effects on "vars", "types", and "nonGenerics".
   */
  function typeFromName(atom) {
    var name = atom.name;
    if (constantTypes.hasOwnProperty(name)) {
      // If it is a constant -- primitive, defined, or even a constant
      // name that has appeared in a well-formed term but is not yet
      // defined, return its type.
      return constantTypes[name].fresh({}, nonGenerics);
    }
    if (atom.isLiteral()) {
      // I say integers are individuals.
      return individual;
    }
    // Is it a bound or (already-seen) free variable, or constant seen
    // in this analysis with no type recorded in constantTypes?
    for (var i = vars.length - 1; i >= 0; --i) {
      if (vars[i] == name) {
        var type = types[i];
        // Return a fresh instance of the variable's type.
        return type.fresh({}, nonGenerics);
      }
    }
    // Free variable, or constant not yet defined.
    // Like handling of a variable binding, but scope is the remainder
    // of the expression, and bound variables get searched first.
    var varType = new TypeVariable();
    vars.unshift(name);
    types.unshift(varType);
    nonGenerics.unshift(varType);
    return varType;
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
    // The analysis can throw.
    var result = analyze(expr);
    // If successful do the rest of the work.
    if (annotate) {
      // If annotating, walk through all subexpressions of the expr,
      // tidying up their types, which are now all in final form.
      tidyAll(expr);
    } else {
      tidy(result);
    }
    // Scan through "vars" for the names of any constants analyzed
    // here for the first time, and record the discovered type
    // information.  This preferably would only have effect when
    // parsing the definition of a new constant, as real forward
    // references might not record the exact type.
    for (var i = 0; i < vars.length; i++) {
      var nm = vars[i];
      if (Toy.isConstantName(nm)) {
        // If the name already had a recorded type in constantTypes,
        // it would not be in the vars list.
        var type = types[i];
        tidy(type);
        // console.log('New constant', nm, 'assigned type', '' + type);
        // console.log('  in', '' + expr);
        // TODO: Consider adding the name and expr to a list of forms
        //   introducing new constants, and check at certain moments
        //   whether all names in it have definitions, giving a warning
        //   if not.  For example one might check when the event loop
        //   returns to idle.
        constantTypes[nm] = dereference(type);
      }
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
 * Look up the type of a primitive or defined constant.  Result is
 * not fresh.  Returns null if preconditions are not met.
 */
function lookupType(name) {
  if (constantTypes.hasOwnProperty(name)) {
    return constantTypes[name];
  } else if (isDefinedByCases(name)) {
    return definedTypes[name];
  } else if (isDefinedSimply(name)) {
    console.warn(name, 'is defined but type is not recorded.');
    return findType(getDefinition(name).getRight());
  } else {
    return null;
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

/**
 * Function of any two things of the same type, with boolean result.
 */
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

/**
 * Function from a collection of things of some type, to
 * a thing of that type.
 */
function theType() {
  var v = new TypeVariable();
  return new FunctionType(new FunctionType(v, boolean), v);
}

// Primitive constants.  Unlike textbook, these include T and F.
var _primitives = {T: true, F: true, '=': true, the1: true};

Atom.prototype.isPrimitive = function() {
  return _primitives.hasOwnProperty(this.name);
};

// Types of constants here.
//
// TODO: Trim this collection as more constants become properly
//   defined.
//
var constantTypes = {
  // Primitive constants
  T: boolean,
  F: boolean,
  '=': equalityType(),
  the1: theType(),

  // The real numbers.
  R: new FunctionType(individual, boolean),
  // Functions with inputs of arbitrary type
  '>': equalityType(),
  '>=': equalityType(),
  '<': equalityType(),
  '<=': equalityType(),
  '!=': equalityType(),
  // Functions on individuals
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
  the1: true
};

/**
 * Add a simple definition with true/false cases.  A call could
 * be something like defineCases('not', F, T).
 *
 * TODO: Consider replacing this with definitions whose statement
 *   includes "if-then-else".
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
  // Procedurally unify the type of the true branch and the false
  // branch, and add a boolean input.
  var type1 = findType(ifTrue);
  unifyTypes(type1, findType(ifFalse));
  var type = new FunctionType(boolean, dereference(type1));
  constantTypes[name] = type;
  definitions[name] = {T: equal(call(name, 'T'), ifTrue),
                       F: equal(call(name, 'F'), ifFalse)};
}

/**
 * Returns whether the name (or Atom) currently has a simple
 * definition.
 */
function isDefinedSimply(name) {
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
 * Returns null if the given name has no definition; false if
 * it is a primitive constant.
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
 * Returns a truthy value iff the given constant name has a
 * definition, not just "seen" previously as a constant in some axiom
 * or assertion.
 */
function isDefined(name) {
  var def = definitions[name];
  return def !== true && !!def;
}

/**
 * Returns a truthy value iff the given name has a simple equational
 * definition as a function (Lambda).
 */
function isFunDef(name) {
  const def = definitions[name];
  return (def instanceof Expr &&
          def.isCall2('=') &&
          def.getRight() instanceof Lambda);
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
 * TODO: Remove this.
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
 *
 * Unicode names in the unicodeNames table (non-ASCII characters) are
 * tokenized here as the "ASCII" equivalent, so those characters get
 * parsed as if the usual textual form were seen.
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
// TODO: Use a Map.
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
    const e2 = new Error('Could not parse "' + input + '": ' + e.message);
    e2.cause = e;
    throw e2;
  }
}

/**
 * Same as justParse, but throws errors with low-level messages.
 * The second argument is private to parseMin.
 */
function justParse1(input, aboveToken) {
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
   * if it is not equal to the one expected.
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
        expr = mustParseAbove(aboveWhat);
        expect(')');
        return expr;
      }
    } else if (name === '{' || name === '[') {
      var id = next();
      assert(id.isVariable(), 'Expected identifier, got ' + id.name);
      expect('.');
      var body = mustParseAbove(aboveWhat);
      expr = lambda(id, body);
      expect(name === '{' ? '}' : ']');
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
   * This always stops before any (top-level) token that does not bind
   * tighter than the given one.
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
  var aboveWhat = aboveToken || new Atom('(end)');
  // Parse an expression.  A special "(begin)" delimiter does not seem
  // to be required, though note this does not require or even allow a
  // closing paren.
  var result = mustParseAbove(aboveWhat);
  if (tokens.length) {
    throw new Error('Extra input: "' + tokens[0] + '"');
  }
  return result;
}

/**
 * Parses a minimal amount of input, such as a parenthesized
 * expression, without trying to find any type information.
 *
 * TODO: Currently unused; test this.
 */
function parseMin(input) {
  return justParse1(input, new Atom('x'));
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
 * Extracts and returns the actual string content from the external
 * representation of a string, replacing occurrences of backslash
 * followed by another character (except newline) with just the
 * following character.
 */
function parseStringContent(name) {
  var content = name.substring(1, name.length - 1);
  return content.replace(/\\(.)/g, '$1');
}

/**
 * Creates and returns a parseable external representation for a
 * string.  This quotes backslash and double quote by preceding them
 * with a backslash.  Everything else remains the same.
 *
 * TODO: Consider replacing this and parseString with JSON.stringify
 * and JSON.parse applied to strings.
 */
function unparseString(content) {
  var s1 = content.replace(/["\\]/g, '\\$&');  // For emacs: "]);
  return '"' + s1 + '"';
}

var _mathParsed = new Map();

/**
 * If string begins with "@", simply parses the rest with "parse".
 * Otherwise this also checks for any apparent math variables (as by
 * calling Expr.mathVars) and adds assumptions that all of those "math
 * variables" are real numbers.  If the main operator of the
 * expression is =>, concatenates any added assumptions at the end of
 * its LHS.  Given an Expr, simply returns it.
 *
 * TODO: Eventually modify this to use type declarations for
 *   variables, such as "x is real".  It will then need an extra
 *   (probably optional) parameter to specify the parsing context.  At
 *   that point, fact references and other statements will need to be
 *   able to identify the parsing context.  For example lists of facts
 *   will need to be able to include statements about default types of
 *   variables according to their names.
 */
function mathParse(str) {
  if (str instanceof Expr) {
    return str;
  }
  if (str[0] === '@') {
    return parse(str.slice(1));
  }
  const parsed = _mathParsed.get(str);
  if (parsed) {
    return parsed;
  }
  var expr = justParse(str);
  var result = expr.andMathVarConditions();
  findType(result);
  _mathParsed.set(str, result);
  return result;
}

/**
 * Adds "math var conditions" as the rightmost assumptions of this
 * wff.
 */
Expr.prototype.andMathVarConditions = function() {
  var assume = this.mathVarConditions();
  if (assume) {
    if (this.isCall2('=>')) {
      // Any type assumptions follow the LHS.
      // These may later be matched against a proved result, so we aim
      // to achieve the usual ordering here.
      return infixCall(this.getLeft().concat(assume, '&'),
                       '=>',
                       this.getRight());
    } else {
      return infixCall(assume, '=>', this);
    }
  } else {
    return this;
  }
};

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
const unaryPower = 200;

// Alphanumeric names have this power unless specified otherwise.
var namePower = 100;

// Precedence table for infix operators.
var precedence = {
  // Closing tokens have power 0 to make infix parsing return.
  '(end)': 0,
  ')': 0,
  ']': 0,
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
  '[': 1000,
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
function boolSchemaInfo(term) {
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
  return {schema: makeSchema(term), subst: map.subst};
}

/**
 * Returns just the schema part of the boolean schema info.
 */
function boolSchema(term) {
  return boolSchemaInfo(term).schema;
}

/**
 * Returns a substitution that renames all of the free variables
 * of the term into the "standard" variable names, following a
 * predictable, "left-to-right" order.
 */
function standardSubst(term) {
  const free = term.freeVarSet();
  // Names in a known LR order.
  const freeVars = Array.from(free);
  const subst = {};
  var counter = 1;
  freeVars.forEach(function(name) {
      // Using variable names as in TermMap.addTerm.
      subst[name] = new Atom('a' + counter);
      counter++;
    });
  return subst;
}

/**
 * Returns a term equivalent to (equi-satisfiable with) the input, in
 * which all variable names are converted to standard names by
 * internal use of a TermMap, applied to the variables in
 * left-to-right order.
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
 *
 * TODO: Rename this to isInfixOp.
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
  return getPrecedence(this) === unaryPower;
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
 * calls to "R" come before all others.  Value < 0 means e1 is less
 * than e2.  Value is 0 iff the terms are identical.
 */
function asmComparator(e1, e2) {
  function asmScore(e) {
    return (e.isCall1('R')
            ? 4
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
 * is empty, return the given default, or if just one item,
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
 * Given a string naming a rule, returns an array of input types for
 * the rule, decoding the "inputs" property of the rule info.  This
 * fails if the string does not name a rule, but does not validate the
 * inputs.  For any property in siteTypes, sets the next type to "_",
 * indicating an implied path following the step argument for the site,
 * e.g. {reducible: 1} gives the result ['reducible', '_'].
 */
function inputTypes(ruleName) {
  assert(typeof ruleName === 'string' && Toy.rules[ruleName],
         'Bad rule name {1}', ruleName);
  const inputs = Toy.rules[ruleName].info.inputs;
  if (!inputs) {
    return null;
  }
  const result = [];
  for (let type in inputs) {
    const arg = inputs[type];
    const indexes = typeof arg === 'number' ? [arg] : arg;
    indexes.forEach(function(index) {
        const i = index - 1;
        result[i] = type;
        if (type in Toy.siteTypes) {
          result[i + 1] = '_';
        }
      });
  }
  return result;
}

/**
 * Compute and return a string representing the given array of proof
 * steps, which may be either rendered or originals.  Treating
 * expressions with "multiple arguments" as lists, the format is an
 * expression starting with "steps", followed list of proof steps,
 * each represented as a list having first, the step's index, then the
 * rule name followed by all of the arguments.
 *
 * Each rule argument is represented as a list or string.  If a list,
 * the first element is "t" for a term (followed by the term itself),
 * "path" for a path (followed by the path as a string), or "s" for a
 * reference to another step (followed by the index of the referenced
 * step).
 *
 * The need to use fixupBoundNames here means that proofs cannot in
 * general rely on bound names to remain the same from one step
 * to the next!
 */
function encodeSteps(steps_arg) {
  const indexes = new WeakMap();

  function rep(step) {
    var index = indexes.get(step)
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
        const i = indexes.get(arg);
        // Note: This finesses the question of whether the step might
        // improperly refer to a step not part of the current proof.
        if (i) {
          result.push('(s ' + indexes.get(arg) + ')');
        } else {  
          result.push('(t ' + arg.fixupBoundNames()  + ')');
        }
      } else if (arg.constructor === Object) {
        // Treat this as a substitution
        const map = {};
        for (const key in arg) {
          const v = arg[key];
          if (v instanceof Expr) {
            map[key] = v.toString();
          } else if (typeof v === 'string') {
            map[key] = v;
          } else {
            console.warn('Substitution not term:', v, 'in', arg);
          }
        }
        result.push('(subst ' + unparseString(JSON.stringify(map)) + ')');
      } else if (Array.isArray(arg)) {
        // An array currently is always a list of facts.
        let ok = true;
        // A fact may be an Expr, a string, or a plain object.  The
        // plain objects usually contain functions, so we do not try
        // to encode them.
        const a = arg.map(function(v) {
            return (v instanceof Expr
                    // A fact will be parsed with mathParse, so make
                    // sure that adds no assumptions.
                    ? '@ ' + v.toString()
                    : typeof v === 'string'
                    ? v
                    : (console.warn('Bad fact list item:', v),
                       ok = false,
                       undefined));
          });
        assert(ok, 'Failed to encode steps');
        result.push('(facts ' + unparseString(JSON.stringify(a)) + ')');
      } else {
        console.warn('Bad rule argument:', arg);
        assert(false, 'Bad rule argument in encodeSteps');
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
    indexes.set(step, i + 1);
    reps.push(rep(step));
  }
  reps.push(')\n');
  return reps.join('\n');
}

/**
 * From the given input expression or string to be parsed, computes
 * and returns an array of steps, empty in case of failure.
 *
 * TODO: Consider possibly returning null for failure.
 */
function decodeSteps(input) {
  let parsed;
  try {
    parsed = typeof input == 'string' ? justParse(input) : input;
  } catch(e) {
    console.warn('Parse failed decoding ' + input);
    return [];
  }
  var descriptions = parsed.asArray();
  var outSteps = [];
  let args = [];
  for (let i = 1; i < descriptions.length; i++) {
    let message = '';
    let ruleName;
    // Ignore the first "description" by starting at 1.
    const stepTerm = descriptions[i];
    var stepInfo = stepTerm.asArray();
    assert(stepInfo.shift().getNumValue() == i, function() {
        return 'Mismatched step number in: ' + stepInfo;
      });
    ruleName = stepInfo.shift().name;
    // The remainder of the array is arguments to the rule.
    args = [];
    stepInfo.forEach(function(info) {
        args.push(decodeArg(info, outSteps));
      });
    try {
      const rule = Toy.rules[ruleName];
      if (rule) {
        outSteps.push(rule.apply(Toy.rules, args));
      } else {
        message = 'No such rule: ' + ruleName;
      }
    } catch(e) {
      message = '' + e;
    }
    if (message) {
      // Desirable? -- Toy.alert('Error decoding steps: ' + message);
      console.warn('Decoding steps:', message);
      console.warn('Applying rule', ruleName.$$, 'to', args.$$);
      break;
    }
  }
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
      // At present (2018-12-08) a term argument will be encoded as
      // a step if it constitutes the entire wff, so in the future
      // decoding may need to convert occurrences of 's' to the
      // wff of the step if the argument type required by
      // the rule is a term or close kin.
    case 's':
      // Step indexes are 1-based.
      return (steps[value.getNumValue() - 1]);
    case 't':
      return (value);
    case 'path':
      return (Toy.path(value._value));
    case 'subst':
    case 'facts':
      return JSON.parse(value.getStringValue());
    default:
      assert(false, 'Unknown encoding key: ' + key);
    }
  }
}

/**
 * Returns a string with all the key information for recreating a
 * proof in the step editor as JavaScript code that proves the last
 * step as a fact.  The first line of the string is a statement of the
 * fact, and the the remaining lines are suitable for use as the
 * elements of an array to pass to Toy.decodeProof, which proves the
 * last of the steps from the preceding ones.
 *
 * This is for use by developers in transferring proofs from the step
 * editor into the system source code.  Call it interactively from the
 * browser console, then cut and paste the two parts of the output
 * string.
 */
function dumpProof(proofEditor) {
  const ed = proofEditor || window.proofEditor;
  const step = ed.steps[ed.steps.length - 1].original;
  const steps = Toy.proofOf(step);
  const encoded = encodeSteps(steps);
  const split = encoded.split('\n');
  // TODO: Consider a different format that uses:
  // JSON.stringify(split, null, 1)
  // to produce multiline output that can be read back with
  // Array.join.
  split.pop();
  split.pop();
  split.shift();
  const quoted = split.map(function(line) { return "  '" + line + "'"; });
  return "stmt: '" + step.wff.toString() + "',\n" + quoted.join(',\n');
}

/**
 * Given an array of step descriptions, each in the serialized form as
 * from encodeSteps, builds a proof consisting of those steps, and
 * returns the proved result (last step).
 */
function decodeProof(steps_arg) {
  const steps = ['(steps '].concat(steps_arg, ')');
  const decoded = decodeSteps(steps.join('\n'));
  return decoded[decoded.length - 1];
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
Toy.inputTypes = inputTypes;

Toy.encodeSteps = encodeSteps;
Toy.decodeSteps = decodeSteps;

Toy.dumpProof = dumpProof;
Toy.decodeProof = decodeProof;

Toy.unicodify = unicodify;

Toy.termify = termify;
Toy.namify = namify;

Toy.looksBoolean = looksBoolean;
Toy.boolSchemaInfo = boolSchemaInfo;
Toy.boolSchema = boolSchema;
Toy.standardVars = standardVars;
Toy.standardSubst = standardSubst;

// Definitions

Toy.defineCases = defineCases;
Toy.definex = definex;
Toy.isDefinedSimply = isDefinedSimply;
Toy.isDefinedByCases = isDefinedByCases;
Toy.isDefined = isDefined;
Toy.isFunDef = isFunDef;
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
Toy.lookupType = lookupType;

// Counter for the number of nontrivial calls to findType.
Toy.ft = 0;

// Expression parsing

Toy.unaryPower = unaryPower;
Toy.namePower = namePower;
Toy.getPrecedence = getPrecedence;
Toy.tokenize = tokenize;
Toy.parse = parse;
Toy.justParse = justParse;
Toy.parseMin = parseMin;
Toy.mathParse = mathParse;
Toy.parseStringContent = parseStringContent;

// For testing:
Toy._equalityType = equalityType;
Toy.unparseString = unparseString;
Toy._decodeArg = decodeArg;
Toy._parsed = _parsed;
Toy._mathParsed = _mathParsed;

// For debugging
Toy.nParsed = nParsed;
Toy._constantTypes = constantTypes;
Toy._dereference = dereference;

Toy.loaded.trigger('xutil');

})();
