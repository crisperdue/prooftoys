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
// returns true iff the variable matches the term after applying the
// bindings zero or more times.  This indicates that the current
// bindings are sufficient to match the variable with the term.
// Otherwise the result is false.
//
// If the term is composite, this applies the bindings to its parts
// recursively, and if it ever reaches the same variable, it fails by
// returning null; else false as stated above.
function isTriv(map, name, term) {
  if (term instanceof TypeVariable) {
    const n2 = term.name;
    if (name === n2) {
      return true;
    } else {
      const to = map.get(n2)
      return !!to && isTriv(map, name, to);
    }
  } else if (term instanceof FunctionType) {
    return (isTriv(map, name, term.fromType) ||
            isTriv(map, name, term.toType)
            ? null
            : false);
  } else {
    return false;
  }
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
      const triv = isTriv(map, name, type);
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
  if (c1 === TypeConstant && c2 === TypeConstant && type1 === type2) {
    return true;
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

// Substitutes for the named type variables in this term, returning
// a term with updated type information.  If the substitution is a
// no-op, just returns this term, otherwise a copy as needed.
//
// The map preferably should not have any identity mappings; this
// copies structure any time a mapping applies to a node's type.
Expr.prototype.subsType = function(map) {
  if (!map.size) {
    return this;
  }
  // This may create new objects, and if so we need to install the new
  // type information.
  if (this instanceof Call) {
    const fn = this.fn.subsType(map);
    const arg = this.arg.subsType(map);
    if (fn === this.fn && arg === this.arg) {
      return this;
    } else {
      const result = new Call(fn, arg);
      result._type = fn._type.toType;
      return result;
    }
  } else if (this instanceof Lambda) {
    const body = this.body.subsType(map);
    const bound = this.bound.subsType(map);
    if (body === this.body && bound === this.bound) {
      return this;
    } else {
      const result = new Lambda(bound, body);
      result._type = new FunctionType(bound._type, body._type);
      return result;
    }
  } else if (this instanceof Atom) {
    const type = this._type.tsubst(map);
    if (type === this._type) {
      return this;
    } else {
      // The pname is the one to use with the constructor.
      const atom = new Atom(this.pname);
      atom._type = type;
      return atom;
    }
  } else {
    abort('Bad input');
  }
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
    this._type._addTVars(vars);
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
Expr.prototype.distinctifyTypes = function(term2) {
  // TODO: Rename to typesDistinctifier.
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
      return andUnif(t1._type, t2._type);
    } else if (c === Call) {
      return (unifTerm(t1.fn, t2.fn) &&
              unifTerm(t1.arg, t2.arg) &&
              andUnif(t1._type, t2._type));
    } else if (c === Lambda) {
      return (unifTerm(t1.bound, t2.bound) &&
              unifTerm(t1.body, t2.body) &&
              andUnif(t1._type, t2._type));
    } else {
      abort('Bad expression: {1}', t1);
    }
  }
  const u = unifTerm(this, expr2) && unifTypesList(map, pairs);
  return u && resolve(u);
};

// Returns this or if necessary a copy with type variables substituted
// to be all distinct from type variables of the argument.
Expr.prototype.distinctify = function(expr2) {
  const distinctor = this.distinctifyTypes(expr2);
  const result = this.subsType(distinctor);
  return result;
};

// Attempts to unify the type variables of this and the argument,
// returning a pair of terms.  Untested and unused.
Expr.prototype.withTypesUnified = function(expr2) {
  const distinct = this.distinctify(expr2);
  const u = distinct.typesUnifier(expr2);
  if (!u) {
    return null;
  }
  return [distinct.subsType(u), expr2.subsType(u)];
};


//// EXPORTS

Toy.andUnifTypes = andUnifTypes;
Toy.unifTypesList = unifTypesList;
Toy.resolve = resolve;
Toy.fullUnifTypes = fullUnifTypes;
Toy.isTriv = isTriv;
Toy.coreUnifTypes = coreUnifTypes;

})();
