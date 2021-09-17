//// Copyright Crispin Perdue.  All rights reserved.

//// Unification in the style of John Harrison's "Practical Logic".

'use strict';

(function() {

const Expr = Toy.Expr;
const Atom = Toy.Atom;
const Call = Toy.Call;
const Lambda = Toy.Lambda;

const TypeVariable = Toy.TypeVariable;
const TypeConstant = Toy.TypeConstant;
const FunctionType = Toy.FunctionType;
const Bindings = Toy.Bindings;
const findBinding = Toy.findBinding;

// Given bindings of names to terms, a variable name, and a term,
// returns true iff the term is a type variable and the name matches
// it after applying the bindings zero or more times.  This
// indicates that the current bindings are sufficient to match the
// variable with the term.  Otherwise the result is false.
//
// If the term is composite, this applies the bindings to its parts
// recursively, and if it ever reaches the same variable, it fails by
// returning null (the "occurs" check); else false as stated above.
//
// In typical use, a value of true indicates a trivial match; false
// indicates matching is not trivial; and null is a unification
// failure (cycle).
function checkTriv(map, name, term) {
  if (term instanceof TypeVariable) {
    const n2 = term.name;
    if (name === n2) {
      return true;
    } else {
      const to = map.get(n2)
      return !!to && checkTriv(map, name, to);
    }
  } else if (term instanceof FunctionType) {
    const t1 = checkTriv(map, name, term.fromType);
    if (t1 === null) {
      return null;
    } else {
      const t2 = checkTriv(map, name, term.toType);
      return (t2 === null || t1 || t2
              ? null
              : false);
    }
  } else {
    return false;
  }
}

// Straw man, just checks for trivial type variable unification.
// Has no "occurs check", DO NOT USE.
function justCheckTriv(map, name, term) {
  while (term instanceof TypeVariable) {
    const tnm = term.name;
    if (name === tnm) {
      return true;
    } else {
      term = map.get(tnm);
    }
  }
  return false;
}

// Consider an additional pair to be unified in the context of the
// given map of bindings and array of pairs still to be unified.
// Returns falsy if unification fails, else truthy.
function andUnifTypes(type1, type2, map, pairs) {
  const c1 = type1.constructor;
  const c2 = type2.constructor;
  const unifVar = (v, type) => {
    const name = v.name;
    const found = map.get(name);
    if (found) {
      // The name already has a binding.  Match it with the type.
      pairs.push([found, type]);
    } else {
      const triv = checkTriv(map, name, type);
      if (triv == null) {
        // Unification would be cyclic.
        return false;
      } else if (!triv) {
        map.set(name, type);
      }
    }
    // The variable unifies.
    return true;
  };
  if (c1 === TypeConstant && c2 === TypeConstant) {
    return type1 === type2;
  } else if (c1 === TypeVariable) {
    return unifVar(type1, type2);
  } else if (c2 === TypeVariable) {
    return unifVar(type2, type1);
  } else if (c1 === FunctionType && c2 === FunctionType) {
    // Push two new pairs onto the work queue.
    pairs.push([type1.fromType, type2.fromType],
               [type1.toType, type2.toType]);
    return true;
  } else {
    // Unification has failed, though not cyclic.
    return false;
  }
}

// If the pairs unify given existing substitutions in the map, returns
// the updated map holding the unification, or null if they do not.
// The unification may still need to be resolved.  Treats the pairs as
// a stack, so examines the last pair first.  May consume some of the
// pairs, or all if successful.
function unifTypesList(map_arg, pairs_arg) {
  const map = map_arg;
  const pairs = pairs_arg;
  while (pairs.length > 0) {
    const [x, y] = pairs.pop();
    if (!andUnifTypes(x, y, map, pairs)) {
      return null;
    }
  }
  return map;
}

// Converts a Map resulting from unification into a single
// substitution that does the entire work, or returns null
// if given null.
function resolve(map) {
  if (!map) {
    return map;
  }

  let changed;
  // Continue doing rounds of substitution until no term changes.
  do {
    changed = false;
    let map2 = new Map();
      for (const [nm, term] of map) {
        const term2 = term.tsubst(map);
        // This test presumes that a no-op substitution
        // returns its input, not a copy.
        if (term2 !== term) {
          changed = true;
        }
        map2.set(nm, term2);
      }
      map = map2;
  } while (changed);
  return map;
}

// Attempts to unify two type terms, returning the unifying Map on
// success; otherwise null.  If successful there is a unifier,
// but the unification is not "resolved".  See "resolve" or
// fullUnifTypes for this.
function coreUnifTypes(type1, type2) {
  const pairs = [];
  const map = new Map()
  return (andUnifTypes(type1, type2, map, pairs) &&
          unifTypesList(map, pairs));
}

// Returns a Map with the result of fully unifying just type1 and
// type2, or null if the terms do not unify.
function fullUnifTypes(type1, type2) {
  const map = coreUnifTypes(type1, type2);
  return map ? resolve(map) : null;
}

// TODO: Consider whether the constructors for Call and Lambda
// should install type information where possible.


//// TYPE SUBSTITUTION

// Substitutes for the named type variables in this term, returning a
// term with updated type information.  If the substitution is empty,
// just returns this term, otherwise a copy as needed.
//
// The map preferably should not have any identity mappings; this
// copies structure any time a mapping applies to a node's type.
Expr.prototype.subsType = function(map) {
  if (!map.size) {
    return this;
  }
  // This may create new objects, and if so we need to install the new
  // type information.
  const type = this.type.tsubst(map);
  if (this instanceof Call) {
    const fn = this.fn.subsType(map);
    const arg = this.arg.subsType(map);
    if (fn === this.fn && arg === this.arg && type == this.type) {
      return this;
    } else {
      return new Call(fn, arg)._withType(type);
    }
  } else if (this instanceof Lambda) {
    const body = this.body.subsType(map);
    const bound = this.bound.subsType(map);
    if (body === this.body && bound === this.bound && type === this.type) {
      return this;
    } else {
      return new Lambda(bound, body)._withType(type);
    }
  } else if (this instanceof Atom) {
    if (type === this.type) {
      return this;
    } else {
      // The pname is the one to use with the constructor.
      return new Atom(this.pname)._withType(type);
    }
  } else {
    abort('Bad input');
  }
};

// Destructively applies the given type substitution to
// all parts of this term.  Careful, this is destructive.
Expr.prototype.replaceTypes = function(map) {
  if (!map.size) {
    return this;
  }
  const atomsSeen = new Set();
  const treeWalk = term => {
    const c = term.constructor;
    if (c === Call) {
      treeWalk(term.fn);
      treeWalk(term.arg);
    } else if (c === Lambda) {
      treeWalk(term.bound);
      treeWalk(term.body);
    } else if (c === Atom) {
      if (atomsSeen.has(term)) {
        // Don't substitute if this Atom (variable) has already
        // been visited.
        return;
      } else {
        atomsSeen.add(term);
      }
    } else {
      abort('Bad input');
    }
    term.__type = term.type.tsubst(map);
  }
  treeWalk(this);
};

TypeVariable.prototype.tsubst = function(map) {
 return map.get(this.name) || this;
};

TypeConstant.prototype.tsubst = function(map) {
  return this;
};

// Substitutes for type variables in this type.  The implementation
// takes some care to share existing instances rather than creating new
// ones, the main purpose being to avoid using unnecessary space.
FunctionType.prototype.tsubst = function(map, seen = []) {
  const from = this.fromType.tsubst(map, seen);
  const to = this.toType.tsubst(map, seen);
  if (from === this.fromType && to === this.toType) {
    // This substitution is a no-op.
    return this;
  } else {
    // The substitution affects this type, but
    // avoid re-creating essentially the same type.
    const found = (seen.find(x => x.equal(this)) ||
                   Toy.commonTypes.find(x => x.equal(this)));
    const result = found || new FunctionType(from, to);
    seen.push(result);
    return result;
  }
};


//// Finding TypeVariable names.

// Computes and returns a Set of the names of
// type variables apppearing within this expression.
Expr.prototype.typeVars = function() {
  return this._addTVars(new Set());
};

Expr.prototype._addTVars = function(vars) {
  if (this instanceof Call) {
    this.fn._addTVars(vars);
    this.arg._addTVars(vars);
  } else if (this instanceof Lambda) {
    this.body._addTVars(vars);
  } else if (this instanceof Atom) {
    this.type._addTVars(vars);
  } else {
    abort('Bad input');
  }
  return vars;
};

// These add the names of all type variables appearing within their
// type term to the given set of type variable names.

TypeVariable.prototype._addTVars = function(vars) {
  vars.add(this.name);
};

TypeConstant.prototype._addTVars = function(vars) {
};

FunctionType.prototype._addTVars = function(vars) {
  this.fromType._addTVars(vars);
  this.toType._addTVars(vars);
};


//// DISTINGUISHING TYPE VARIABLES

// TODO: before unifying type variables across steps, check for any
// type variables that occur in both and rename all of those in one of
// the steps.

// Returns a substitution Map that can make the type variables in this
// all distinct from the type variables in the argument term, e.g.  by
// calling Expr.subsType with the result.
Expr.prototype.typesDistinctifier = function(term2) {
  const term1 = this;
  const vars1 = term1.typeVars();
  const vars2 = term2.typeVars();
  const conflicts = Toy.intersection(vars1, vars2);
  const map = new Map();
  for (const name of conflicts) {
    map.set(name, new TypeVariable());
  }
  return map;
};

// Returns a substitution Map that unifies the types in this with the
// types in the Expr argument; or a falsy value in case unification
// fails.  Assumes that this Expr and the argument are exactly the
// same other than type assignments and names of bound variables.
//
// Call this.subsType and expr.subsType with the result of this call
// to make their type assignments the same.  The result is resolved.
Expr.prototype.typesUnifier = function(expr2) {
  const map = new Map();
  const pairs = [];
  const andUnif = (type1, type2) => andUnifTypes(type1, type2, map, pairs);
  function unifTerm(t1, t2) {
    const c = t1.constructor;
    if (c === Atom) {
      return andUnif(t1.type, t2.type);
    } else if (c === Call) {
      return (unifTerm(t1.fn, t2.fn) &&
              unifTerm(t1.arg, t2.arg) &&
              andUnif(t1.type, t2.type));
    } else if (c === Lambda) {
      return (unifTerm(t1.bound, t2.bound) &&
              unifTerm(t1.body, t2.body) &&
              andUnif(t1.type, t2.type));
    } else {
      abort('Bad expression: {1}', t1);
    }
  }
  const u = unifTerm(this, expr2) && unifTypesList(map, pairs);
  return u && resolve(u);
};

// Returns this or if necessary a copy with type variables substituted
// to be all distinct from type variables of the argument.
//
// TODO: Consider a version that updates types in place, never copying.
Expr.prototype.distinctify = function(expr2) {
  const distinctor = this.typesDistinctifier(expr2);
  const result = this.subsType(distinctor);
  return result;
};

// Returns an array of pairs of types that need to be unified
// to make the current preterm well-formed in its type assignments.
// This is work in progress, unused, untested, and not full
// type inference.
Expr.prototype.annotate1 = function() {
  const pairs = [];
  // This returns a type expression for the term visited.  This type
  // may still need to be unified with others.
  const visit = (term) => {
    const c = term.constructor;
    if (c === Atom) {
      if (term.type) {
        // Only atoms should be pre-typed, which can occur
        // from shared structure for variables.
        return term.type;
      }
      const ctype = constantNames.get(c.pname);
      if (ctype) {
        return ctype.clone();
      } else if (term.isLiteral()) {
        // Literals so far are individuals.
        term.__type = individual;
        return individual;
      } else if (term.isVariable()) {
        term.__type = new TypeVariable();
        return term.type;
      } else {
        abort('Unable to determine type for {1}', term);
      }
    } else if (c === Call) {
      const fnType = visit(term.fn);
      const inType = visit(term.arg);
      const outType = new TypeVariable();
      pairs.push([inType, fnType.fromType], [outType, fnType.toType]);
      return outType;
    } else if (c === Lambda) {
      const inType = visit(term.bound);
      const outType = visit(term.body);
      return new FunctionType(inType, outType);
    }
  };
  visit(this);
};


//// SIMPLE TYPECHECKING

// This checks that all subexpression types match each other.
// types must be present throughout.
// Returns the failing term or falsy for success.
Expr.prototype.typeCheck = function() {
  // Bound variable info is at the front of these,
  // free variable info at the end.
  const names = [];
  const types = [];
  // Returns true iff OK.
  function checkAtom(v) {
    if (v.isVariable()) {
      const nm = v.name;
      const i = names.indexOf(nm);
      if (i < 0) {
        names.push(nm);
        types.push(v.type);
        return true;
      } else {
        return types[i].equal(v.type);
      }
    } else {
      return true;
    }
  }
  function tCheck(x) {
    const c = x.constructor;
    if (c === Atom) {
      return !checkAtom(x) && x;
    } else if (c === Call) {
      const failure = (tCheck(x.fn) || tCheck(x.arg) ||
                       !x.fn.type.fromType.equal(x.arg.type) ||
                       !x.fn.type.toType.equal(x.type));
      return failure && x;
    } else if (c === Lambda) {
      names.unshift(x.bound.name);
      types.unshift(x.bound.type);
      const failure = tCheck(x.body);
      names.shift();
      types.shift();
      return failure && x;
    }
  }
  return tCheck(this);
};


//// EXPORTS

Toy.andUnifTypes = andUnifTypes;
Toy.unifTypesList = unifTypesList;
Toy.resolve = resolve;
Toy.fullUnifTypes = fullUnifTypes;
Toy.checkTriv = checkTriv;
Toy.coreUnifTypes = coreUnifTypes;

})();
