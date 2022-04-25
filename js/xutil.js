// Copyright Crispin Perdue.  All rights reserved.

// Utilities for types, parsing, and definitions, building
// on expressions.

// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

'use strict';

// Make some names available without prefix.
var Expr = Toy.Expr;
var Atom = Toy.Atom;
var Call = Toy.Call;
var Lambda = Toy.Lambda;
var assert = Toy.assertTrue;
var abort = Toy.abort;
var Path = Toy.Path;

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


// Base class constructor for type expressions.
function TypeEx() {}

/**
 * Returns a copy of this type term, with the same constraints but all
 * type variables renamed to fresh new ones.
 */
TypeEx.prototype.clone = function() {
  const replacements = new Map();
  const clohn = type => {
    const c = type.constructor;
    if (c === TypeVariable) {
      const name = type.name;
      const replica = replacements.get(name);
      if (replica) {
        return replica;
      } else {
        const replica = new TypeVariable();
        replacements.set(name, replica);
        return replica;
      }
    } else if (c === TypeConstant) {
      return type;
    } else if (c === FunctionType) {
      return new FunctionType(clohn(type.fromType),
                              clohn(type.toType));
    }
  }
  return clohn(this);
};

/**
 * Tests if this type expression is the same as the given
 * other one, after possible renamings.  The second argument
 * if given is a Map of additional renamings to be honored.
 * Any name correspondences encountered here are added to
 * that optional Map argument.
 */
TypeEx.prototype.equiv = function(other, map) {
  const renames = map || new Map();
  const equiv = (a, b) => {
    const c = a.constructor;
    if (c !== b.constructor) {
      return false;
    } else if (c === TypeConstant) {
      return a === b;
    } else if (c === TypeVariable) {
      const anm = a.name;
      const bnm = b.name;
      const expected = renames.get(anm);
      if (expected) {
        return bnm === expected;
      } else {
        renames.set(anm, bnm);
        return true;
      }
    } else if (c === FunctionType) {
      return a.fromType.equiv(b.fromType) && a.toType.equiv(b.toType);
    }
  };
  return equiv(this, other);
};


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
  if (name) {
    this.name = name;
  } else {
    this.name = 't' + _typeVarCounter++;
  }
}
Toy.extends(TypeVariable, TypeEx);

TypeVariable.prototype.toString = function() {
  const map = Toy._typeNums;
  if (Toy.showTypes === 'testing') {
    let num = map.get(this);
    if (!num) {
      num = map.size + 1;
      map.set(this, num);
    }
    return '' + num;
  } else {
    return this.name;
  }
};

// When applying the "fresh" operation to a type expression, the
// resulting expression has the same structure as the input, but all
// occurrences of each "generic" type variable are replaced with
// occurrences of the same new "fresh" type variable distinct from all
// others.
//
// The mappings are from type variable names in the definition to
// variable names in the instance (for generic types).
//
// Note: In Prooftoys generic type variables are those in the types of
// constants, built-in or defined.
//
// The Wikipedia article at
// /wiki/Hindley%E2%80%93Milner_type_system#Let-polymorphism comments
// that "type inference in polymorphic lambda calculus is not
// decidable", so it is not possible in general to support forms
// such as [f. if (f true) (f 3) 0] [x. x].

/**
 * If this type variable is not generic in the current scope, this
 * just returns its input.  For generics, this returns a type variable
 * to replace it, though if a replacement has already been generate it
 * uses that, as occurs for a FunctionType with multiple occurrences
 * of the same type variable, such as the identity function.
 *
 * The "replacements" indicates replacement type variables already chosen
 * for type variables in a generic type (generic FunctionType).
 */
TypeVariable.prototype.fresh = function(replacements, nonGenerics, map) {
  var type = dereference(this, map);
  if (type instanceof TypeVariable) {
    var name = type.name;
    if (occursInList(name, nonGenerics, map)) {
      return type;
    } else {
      if (!replacements.hasOwnProperty(name)) {
        replacements[name] = new TypeVariable();
      }
      return replacements[name];
    }
  } else {
    // The dereferenced value is not a type variable.
    return type.fresh(replacements, nonGenerics, map);
  }
};

TypeVariable.prototype.equal = function(other) {
  return other === this;
};

TypeVariable.prototype.hasVariable = function() {
  return true;
};


/**
 * Type constant constructor.
 */
function TypeConstant(name) {
  this.name = name;
}
Toy.extends(TypeConstant, TypeEx);

var tcMethods = {
  toString: function() {
    return this.name;
  },

  fresh: function(mapping, nonGenerics) {
    return this;
  },

  equal: function(other) {
    return other === this;
  },

  hasVariable: function() {
    return false;
  }
};
Toy.addMethods(TypeConstant, tcMethods);


function FunctionType(fromType, toType) {
  // Include these lines for debugging if needed.
  // assert(fromType instanceof TypeEx, 'fromType');
  // assert(toType instanceof TypeEx, 'toType');
  this.fromType = fromType;
  this.toType = toType;
}
Toy.extends(FunctionType, TypeEx);

FunctionType.prototype.toString = function() {
  return '(' + this.toType + ' ' + this.fromType + ')';
};

FunctionType.prototype.fresh = function(replacements, nonGenerics, map) {
  return new FunctionType(this.fromType.fresh(replacements, nonGenerics, map),
                          this.toType.fresh(replacements, nonGenerics, map));
};

FunctionType.prototype.equal = function(other) {
  return (other instanceof FunctionType &&
          other.fromType.equal(this.fromType) &&
          other.toType.equal(this.toType));
};

FunctionType.prototype.hasVariable = function() {
  return this.fromType.hasVariable() || this.toType.hasVariable();
};


//// PARSING

var individual = new TypeConstant('i');
var boolean = new TypeConstant('o');
// TODO: Change this to a proper type of its own.
var realType = individual;

// Returns a list of tokens as objects with properties 'name' and
// 'index'.
function tokenizeType(input) {
  // Matches a token with possible whitespace before and/or after.
  const tokenRE = /\s*([()]|[a-zA-Z0-9]+)\s*/g;
  let match;
  const tokens = [];
  while (match = tokenRE.exec(input)) {
    const t = {name: match[1], index: match.index};
    tokens.push(t);
  }
  if (tokens.lastIndex != undefined && tokens.lastIndex !== input.length) {
    console.log('In', input);
    console.log(`lastIndex ${tokens.lastIndex} vs $(input.length)`);
  }
  return tokens;
}
  
/**
 * Parse a type string, returning a type expression.
 * Input can only be parenthesized sequences of "i", "o", a single
 * upper case letter, or "t" followed by digits, with space as the
 * separater.
 */
function parseType(input) {
  return parseTokens(tokenizeType(input));
}

/**
 * Parses an array of tokens; see above.
 */
function parseTokens(tokens) {
  const end = {name: '(end)', index: -1};

  // Get next token, advancing past it, or "end" if no more.
  function next() {
    return tokens.shift() || end;
  }
    
  // Return the next token without advancing, or "end" if there are no
  // more.
  function peek() {
    return tokens[0] || end;
  }

  // Consume one type expression, returning a type, or null if no
  // input is consumed.
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
        if (name.match(/^(t[0-9]*)$/)) {
          var type = new TypeVariable(name);
          left = left ? new FunctionType(type, left) : type;
        } else {
          assert(false, 'Bad token in type term: "' + name + '"');
        }
      }
    }
    // End of input:
    return left;
  }

  var result = parse();
  assert(result, 'Empty input in type term');
  return result;
}


//// TYPE INFERENCE

// TODO: More and better comments throughout the type analysis code.

/**
 * Seeks and returns any subexpression of this with no type
 * information.  This is a debugging utility, not used in the rest of
 * the codebase.
 */
Expr.prototype.findUntyped = function() {
  const self = this;
  if (!self.type) {
    return self;
  }
  const c = self.constructor;
  if (c === Call) {
    return self.fn.findUntyped() || self.arg.findUntyped();
  } else if (c === Lambda) {
    return self.bound.findUntyped() || self.body.findUntyped();
  } else {
    return null;
  }
};

/**
 * If this already has a type, return it without making a copy.
 * Otherwise makes and returns a well-typed copy of this, ignoring any
 * type information already present.
 *
 * TODO: Document how and why this approach is (I think) adequate.
 *   Consider for example that a subterm may contain type information
 *   in its original context, that can become more general as part of
 *   this operation.  The term "f = g" in axiom3 seems an interesting
 *   case.
 */
Expr.prototype.typedCopy = function(mustCopy) {
  if (!mustCopy && this.type) {
    return this;
  }
  const self = this;
  // This is a list of variables bound in the current scope,
  // innermost first.
  const boundVars = [];
  // This is a Map of all free variables seen so far, keyed by
  // variable name.
  const freeVars = new Map();
  // This is a Set of new constants seen so far, i.e. ones with
  // no existing recorded type.
  const newConsts = new Map();
  // Array of type term pairs to unify (unification work queue)
  const toUnify = [];
  // Unifying substitution to make a consistent assignment of types:
  const unifier = new Map();
  // Recursive function that does all the work:
  const copy = x => {
    // Makes a copy with all-new nodes (except potentially monomorphic
    // constants).  If full resolution of type information mutates
    // types in the copy, no part of the input will be affected.
    if (x.isVariable()) {
      const xnm = x.name;
      const bound = boundVars.find(y => y.name === xnm);
      if (bound) {
        return bound;
      } else {
        const free = freeVars.get(xnm);
        if (free) {
          return free;
        } else {
          const xcopy = new Atom(xnm)._withType(new TypeVariable());
          freeVars.set(xnm, xcopy);
          return xcopy;
        }
      }
    }
    // X is not a variable.
    const c = x.constructor;
    if (c === Atom) {
      // It is some kind of constant.
      const xpnm = x.pname;
      const constType = constantTypes.get(xpnm);
      // This relies on constantTypes to include entries
      // for aliases, currently just "==".
      if (constType) {
        // In this case it is a known named constant.
        // TODO: Don't continually copy monomorphic named constants.
        const clone = constType.clone();
        return new Atom(x.name)._withType(clone);
      } else if (x.isLiteral()) {
        // All literals are currently individuals.
        return new Atom(x.name)._withType(individual);
      } else if (x.isConst()) {
        // It is a named constant not seen before.
        const existing = newConsts.get(x.name);
        if (existing) {
          return existing;
        } else {
          const newConst = new Atom(x.name)._withType(new TypeVariable());
          newConsts.set(newConst.name, newConst);
          return newConst;
        }
      } else {
        abort('Bad input: {1}', x);
      }
    } else if (c === Call) {
      const fn = copy(x.fn);
      const arg = copy(x.arg);
      const resultType = new TypeVariable();
      const ft = new FunctionType(arg.type, resultType);
      if (!Toy.andUnifTypes(ft, fn.type, unifier, toUnify)) {
        console.log('In', self.$$);
        console.log('Failed to unify fn', fn, 'with arg', arg);
        console.log('Types', fn.type.fromType, 'and', arg.type);
        abort('Not unifiable');
      }
      return new Call(fn, arg)._withType(resultType);
    } else if (c === Lambda) {
      const bound = new Atom(x.bound.name)._withType(new TypeVariable());
      boundVars.unshift(bound);
      const body = copy(x.body);
      const result = (new Lambda(bound, body)
                      ._withType(new FunctionType(bound.type, body.type)));
      boundVars.shift();
      return result;
    } else {
      abort('Bad input: {1}', x);
    }
  };
  const annotated = copy(this);
  if (!Toy.unifTypesList(unifier, toUnify)) {
    abort('Type assignment failed');
  }
  const finalUnifier = Toy.resolve(unifier);
  annotated.replaceTypes(finalUnifier);
  // Tried storing the association of original to typed copy in
  // a WeakMap, but it did not seem to help performance.
  return annotated;
};

/**
 * Returns a copy like deepCopy, also bringing over all type
 * information from the original, suitable for rendering because all
 * occurrences of variables are represented by distinct structure in
 * the result.
 */
Expr.prototype.copyWithTypes = function() {
  const c = this.constructor;
  if (c === Atom) {
    return new Atom(this.pname)._typeFrom(this);
  } else if (c === Call) {
    return new Call(this.fn.copyWithTypes(),
                    this.arg.copyWithTypes())._typeFrom(this);
  } else if (c === Lambda) {
    return new Lambda(this.bound.copyWithTypes(),
                      this.body.copyWithTypes())._typeFrom(this);
  } else {
    abort('Bad input: {1}', this);
  }
};

/**
 * Expr method that returns any annotated type, otherwise aborts with
 * an error.
 */
Expr.prototype.getType = function() {
  return this.hasType() || abort('Type not available: ' + this);
};

/**
 * Like getType, but returns a falsy value if the term is not
 * annotated.
 */
Expr.prototype.hasType = function() {
  return this.type;
};

/**
 * Returns true iff the type of the term is Real.  Only ever returns
 * true if Expr is part of a WFF that has been annotated with type
 * information.
 *
 * TODO: This check is only approximate.  Reconsider all uses of it.
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

// Note that if the type of the replacement term has no type variables
// in it, it can be used as-is with its types intact.  If the mating
// results in a replacement with no variables, the result might
// sensibly be cached for future use.  In some situations the result
// of rule R may have to be a completely new structure.


/**
 * Assumes "type" is dereferenced.
 */
function occursInList(type, types, map) {
  for (var i = 0; i < types.length; i++) {
    if (occursInType(type, types[i], map)) {
      return true;
    }
  }
  return false;
}

/**
 * Assumes type1 is dereferenced.
 */
function occursInType(type1, type2, map) {
  var type2 = dereference(type2, map);
  if (type2 == type1) {
    return true;
  } else if (type2 instanceof FunctionType) {
    return (occursInType(type1, type2.fromType, map) ||
            occursInType(type1, type2.toType, map));
  }
}

/**
 * This updates the map as needed to unify t1 and t2.
 * The return value is only meaningful in case of failure,
 * and then it is a TypeCheckError.
 */
function unifyTypes(t1, t2, map) {
  // TODO: Consider whether withExit is expensive to use,
  // perhaps because it contains a try block.
  return Toy.withExit(exit => {
    function failAs(msg) {
      exit(new TypeCheckError(msg));
    }

    function unifT(t1, t2) {
      var a = dereference(t1, map);
      var b = dereference(t2, map);
      if (a instanceof TypeVariable) {
        if (a != b) {
          if (occursInType(a, b, map)) {
            failAs('recursive unification');
          }
          map.set(a, b);
        }
      } else if (b instanceof TypeVariable) {
        unifT(b, a);
      } else if (a instanceof TypeConstant) {
        if (a !== b) {
          // Note that this does not permit multiple copies of a constant.
          failAs('Type mismatch: ' + a + ' != ' + b);
        }
      } else if (a instanceof FunctionType && b instanceof FunctionType) {
          unifT(a.fromType, b.fromType);
          unifT(a.toType, b.toType);
      } else {
        failAs('Not similar');
      }
    }
    unifT(t1, t2);
  });
}

/**
 * Returns the ultimate binding of the given type in the substitution
 * map (a Map), removing indirections in the bindings of type
 * variables.  If the given type is a TypeVar t1 that has a mapping to
 * another TypeVar t2, this maps t1 directly to the ultimate binding,
 * and does likewise to t2.
 *
 * Note that this is the identity function for objects that are not
 * type variables, including null and undefined.
 */
function dereference(type, map) {
  if (type instanceof TypeVariable) {
    const ref = map.get(type);
    if (ref) {
      const ref2 = dereference(ref, map);
      map.set(type, ref2);
      return ref2;
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
  if ((type instanceof FunctionType) && type.fromType === boolean) {
    var t1 = type.toType;
    return ((t1 instanceof FunctionType) &&
            t1.fromType === boolean &&
            t1.toType == boolean);
  } else {
    return false;
  }
}

/**
 * True iff this Atom is the boolean equivalence operator.
 */
Atom.prototype.isEquivOp = function(op) {
  return this.name === '=' && isBooleanBinOp(this);
}

/**
 * Function of any two things of the same type, with boolean result.
 * The input type defaults to a new type variable.
 */
function equalityType(ofType = new TypeVariable()) {
  return new FunctionType(ofType, new FunctionType(ofType, boolean));
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

function ifType() {
  const fn = (from, to) => new FunctionType(from, to);
  const v = new TypeVariable();
  return fn(boolean, fn(v, fn(v, v)));
}

// Common monomorphic composite constant types.
// This list supports sharing of the instances.
const commonTypes =
  [
   booleanBinOpType(),
   funType(),
   fun2Type(),
   equalityType(individual),
   new FunctionType(boolean, boolean),
   new FunctionType(individual, boolean)
   ];

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
var constantTypes = new Map(Object.entries({
  // Primitive constants
  T: boolean,
  F: boolean,
  'if': ifType(),
  '=': equalityType(),
  '==': booleanBinOpType(),
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
  }));

// Indexed by the name defined.  Value is an Expr (not a step).  The
// "definition" rule justifies the defining WFF on each access.
//
// Primitive constants are here, but the definitions are truthy fakes.
// This prevents them from being defined later.
var definitions = {
  T: true,
  // TODO: try removing this, since F is defined.
  F: true,
  '=': true,
  the1: true
};

/**
 * Fetches a definition from the definitions database.  Aborts if an
 * appropriate definition is not found.
 */
function getDefinition(name) {
  var defn = findDefinition(name);
  assert(defn, 'Not defined: ' + name);
  return defn;
}

/**
 * Finds a definition in the definitions database.  Also accepts an
 * Atom.
 *
 * Returns null if the given name has no definition; false if it is a
 * primitive constant.
 */
function findDefinition(name) {
  name = name instanceof Atom ? name.name : name;
  var defn = definitions[name];
  if (!defn) {
    return null;
  }
  return defn instanceof Expr && defn;
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
    constant._typeFrom(result.arg.bound);
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
 * Parses a string or array of token strings into a fully typed
 * expression (Expr).  Removes tokens parsed from the tokens list.
 * Aborts if parsing or type checking fails.  If the input is a
 * string, caches the result on success, and reuses a cached result if
 * one exists.
 *
 * TODO: Consider whether the result should be typed, or whether there
 *   should be a separate function for that.  Typed constants such as
 *   T, and literals, deserve some special treatment.  We should make
 *   fewer copies of monomorphic constants, and perhaps some variables
 *   should also be typed (e.g. by their names); and fewer copies
 *   made.
 */
function parse(input) {
  if (typeof input == 'string' &&
      _parsed.hasOwnProperty(input)) {
    return _parsed[input];
  }
  var result = justParse(input).typedCopy();
  if (typeof input == 'string') {
    _parsed[input] = result;
  }
  return result;
}

/**
 * Registers the types of all constants found in this term that have
 * not already been registered.
 */
Expr.prototype.registerConstants = function() {
  // Really just visiting all, not searching.
  this.search(term => {
      if (term.isNamedConst() &&
          !constantTypes.has(term.name)) {
        constantTypes.set(term.name, term.type);
      }
    });   
};

/**
 * Same as "parse", but does not annotate the result with types and
 * does not memoize in _parsed.
 */ 
function justParse(input) {
  try {
    return justParse1(input);
  } catch(e) {
    abort({cause: e}, 'Could not parse "{1}": {2}', input, e.message);
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
      abort({position: token.pos},
            'Expected ' + expected + ', got ' + token.name);
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
      abort('Empty expression at ' + peek().pos);
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
    abort('No parser input');
  }
  // A token of precedence 0.
  var aboveWhat = aboveToken || new Atom('(end)');
  // Parse an expression.  A special "(begin)" delimiter does not seem
  // to be required, though note this does not require or even allow a
  // closing paren.
  var result = mustParseAbove(aboveWhat);
  if (tokens.length) {
    abort('Extra input: "' + tokens[0] + '"');
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
 * If string begins with "@", simply parses the rest with "justParse".
 * Otherwise this also checks for any apparent math variables (as by
 * calling Expr.mathVars) and adds assumptions that all of those "math
 * variables" are real numbers.  If the main operator of the
 * expression is =>, concatenates any added assumptions at the end of
 * its LHS and typechecks the result.
 *
 * With a string input, caches a sucessful result and uses any cached
 * item.  Given an Expr, simply returns it.
 *
 * TODO: Eventually modify this to use type declarations for
 *   variables, such as "x is real".  It will then need an extra
 *   (probably optional) parameter to specify the parsing context.  At
 *   that point, fact references and other statements will need to be
 *   able to identify the parsing context.  For example lists of facts
 *   will need to be able to include statements about default types of
 *   variables according to their names.
 */
function mathParse(arg) {
  if (arg instanceof Expr) {
    return arg.typedCopy();
  }
  if (arg[0] === '@') {
    return parse(arg.slice(1));
  }
  const parsed = _mathParsed.get(arg);
  if (parsed) {
    return parsed;
  }
  const expr = justParse(arg);
  const result = expr.andMathVarConditions().typedCopy();
  _mathParsed.set(arg, result);
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
  // TODO: Clean this up.  Without the special case, getPrecedence
  //   only works for "==" during parsing.  After that it gets treated the
  //   same as "=".
  var name = token.isEquivOp() ? '==' : token.pname;
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
  // This is boolean equivalence.
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
  // Following Lean for precedence of "in" and "notin"
  'in': 20,
  'notin': 20,
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
    // Caution: the term might not be typed.
    return ((op.name in boolOps || op.isEquivOp())  &&
            looksBoolean(term.getLeft()) &&
            looksBoolean(term.getRight()));
  }
  if (term.isCall1('not')) {
    return looksBoolean(term.arg);
  }
  return false;
}

/**
 * Given a typed term, creates a new schema term that consists only of
 * the boolean operators (==, &, |, =>, and "not"), and variables,
 * having the original as a substitution instance.  Descends into all
 * occurrences of the boolean operators and no others, replacing all
 * other terms with boolean variables.  The schema variables are the
 * TermMap variables, in textual order from left to right.
 *
 * TODO: Check that the term is typed.
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
      var op = term.getBinOp();
      if (op.pname in boolOps || op.isEquivOp()) {
        return infix(makeSchema(term.getLeft()), op,
                     makeSchema(term.getRight()));
      }
    }
    if (term.isCall1('not')) {
      return new Toy.Call(term.fn, makeSchema(term.arg));
    }
    if (term instanceof Atom) {
      const name = term.name;
      // Presumably these names will never be overloaded.
      if (name === 'T' || name === 'F') {
        return term;
      }
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
 * Returns the appropriate subexpression of this to match against a
 * target site if this Expr is to be used as a rewriter.  Notice that
 * it is completely determined by the form of this Expr.
 */
Expr.prototype.matchPart = function() {
  const self = this;
  // If given an equation or conditional equation, this is its
  // LHS.  Otherwise if given a conditional, the RHS, otherwise
  // the argument itself.
  return (self.isEquation()
          ? self.eqnLeft()
          : self.isCall2('=>')
          ? self.getRight()
          : self);
};

/**
 * Treating this term as the equation in a replacement,
 * returns the replacement part.  To support rewrite rules
 * that are implicitly equivalent to T, returns T in case
 * this is not equational.
 */
Expr.prototype.replacementTerm = function() {
  return (this.isEquation()
          ? this.get('/main/right')
          : Toy.parse('T'));
};
  

//// SIMPLE UTILITIES

/**
 * Calls a function given as an Expr or name of a constant, passing
 * one or more arguments, that may be passed as strings.
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
 * Builds a Lambda.  The "bound" argument may be a string, converted to
 * an Atom with varify.
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
 * True iff this Atom is a unary operator.
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
  abort('Internal error');
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
  // OK because all types are OK here.
  if (subst = eqn.matchSchema('a = b')) {
    return infix(subst.b, eqn.getBinOp(), subst.a);
  } else if (subst = eqn.matchSchema('h => a = b')) {
    var op = eqn.getRight().getBinOp();
    return infix(subst.h, '=>', infix(subst.b, op, subst.a))
  } else {
    abort(Toy.format('Not an equation: {1}', eqn));
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
 */
function encodeSteps(steps_arg) {
  // This maps from step to its index within the proof.
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
          result.push('(t ' + arg  + ')');
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
 * Returns a (strict) Error in case of failure.
 */
function decodeSteps(input) {
  const parsed = typeof input == 'string' ? justParse(input) : input;
  const descriptions = parsed.asArray();
  const outSteps = [];
  for (let i = 1; i < descriptions.length; i++) {
    let message = '';
    // Ignore the first "description" by starting at 1.
    const stepTerm = descriptions[i];
    const stepInfo = stepTerm.asArray();
    assert(stepInfo.shift().getNumValue() == i, function() {
        return 'Mismatched step number in: ' + stepInfo;
      });
    const ruleName = stepInfo.shift().name;
    // The remainder of the array is arguments to the rule.
    const args = [];
    stepInfo.forEach(function(info) {
        args.push(decodeArg(info, outSteps));
      });
    const rule = Toy.rules[ruleName];
    let result;
    let err;
    const errOut = () => {
      const fmt = Toy.format;
      const msg = (!rule
                   ? fmt('No such rule: {1}', ruleName)
                   : !result
                   ? fmt('No result from rule {1} with args {2}',
                         ruleName, args)
                   : fmt('decodeSteps failed on rule {1} with args {2}',
                         ruleName, args));
      console.log('Proof failed on step', i+',', 'status:');
      outSteps.forEach((s, i) => console.log((i+1)+':', s.toString()));
      const e = Toy.newError({with: {steps: outSteps,
                                   input: input,
                                   cause: err}},
                           '{1}', msg);
      console.error(e.self || e);
      // This can be a good point to stop and debug.
      debugger;
      return e;
    };
    if (rule) {
      if (Toy.catchAborts(() => { result = rule.apply(Toy.rules, args); })) {
        err = Toy.thrown;
      }
      if (result instanceof Error) {
        err = result;
      }
      if (result && !err) {
        outSteps.push(result);
      } else {
        var done = false;
        console.warn('To truncate the proof, set done = true');
        debugger;
        return done ? outSteps : errOut();
      }
    } else {
      return errOut()
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
    var key = info.nthArg(0).name;
    var value = info.nthArg(1);
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
      return (Toy.asPath(value._value));
    case 'subst':
    case 'facts':
      return JSON.parse(value.getStringValue());
    default:
      abort('Unknown encoding key: {1}', key);
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
 *
 * In case of an Error return from decodeSteps, returns that error.
 */
function decodeProof(steps_arg) {
  const steps = ['(steps '].concat(steps_arg, ')');
  let decoded = decodeSteps(steps.join('\n'));
  return (decoded instanceof Error
          ? decoded
          : decoded[decoded.length - 1]);
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

Toy.definex = definex;
Toy.isDefined = isDefined;
Toy.isFunDef = isFunDef;
Toy.findDefinition = findDefinition;
Toy.getDefinition = getDefinition;
// For testing:
Toy.definitions = definitions;

// Types

Toy.boolean = boolean;
Toy.individual = individual;
Toy.equalityType = equalityType;
Toy.commonTypes = commonTypes;
Toy.realType = realType;
Toy.TypeCheckError = TypeCheckError;
Toy.TypeVariable = TypeVariable;
Toy.TypeConstant = TypeConstant;
Toy.FunctionType = FunctionType;
Toy.tokenizeType = tokenizeType;
Toy.parseTokens = parseTokens;
Toy.parseType = parseType;
Toy.isBooleanBinOp = isBooleanBinOp;

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
