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
function andUnifTypes(term1, term2, map, pairs) {
  const c1 = term1.constructor;
  const c2 = term2.constructor;
  const unifVar = (v, term) => {
    const name = v.name;
    const found = map.get(name);
    if (found) {
      // The name already has a binding.  Match it with the term.
      pairs.push([found, term]);
    } else {
      const triv = isTriv(map, name, term);
      if (triv == null) {
        // Unification would be cyclic.
        return false;
      } else if (!triv) {
        map.set(name, term);
      }
    }
    // The variable unifies.
    return true;
  };
  if (c1 === TypeConstant && c2 === TypeConstant && term1 === term2) {
    return true;
  } else if (c1 === TypeVariable) {
    return unifVar(term1, term2);
  } else if (c2 === TypeVariable) {
    return unifVar(term2, term1);
  } else if (c1 === FunctionType && c2 === FunctionType) {
    // Push two new pairs onto the work queue.
    pairs.push([term1.fromType, term2.fromType],
               [term1.toType, term2.toType]);
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

// Attempts to unify terms x and y in the context of an existing
// unification given in the map.  Returns the unifying Map on
// success; otherwise null.
function coreUnifTypes(type1, type2) {
  const pairs = [];
  const map = new Map()
  return (andUnifTypes(type1, type2, map, pairs) &&
          unifTypesList(map, pairs));
}

// Returns a Map with the result of fully unifying just term1 and
// term2, or null if the terms do not unify.
function fullUnifTypes(type1, type2) {
  const map = coreUnifTypes(type1, type2);
  return map ? resolve(map) : null;
}


//// TYPE SUBSTITUTION

/**
 * Substitutes for the named type variables in this term, installing
 * type information for atoms.  If it leaves a Call or Lambda
 * unchanged, any type information remains, but it does not add type
 * information to terms of these kinds.
 */
Expr.prototype.subsType = function(map) {
  if (!map.size) {
    return this;
  }

  // For Calls and Lambdas, if the substitution is a no-op on their
  // parts, the result is a no-op, so in these cases any existing type
  // information is kept; but if this creates a new object, it will
  // have no type information.
  if (this instanceof Call) {
    const fn = this.fn.subsType(map);
    const arg = this.arg.subsType(map);
    return (fn === this.fn && arg === this.arg
            ? this
            : new Call(fn, arg));
  } else if (this instanceof Lambda) {
    const body = this.body.subsType(map);
    return (body === this.body
            ? this
            : new Lambda(this.bound, body));
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

FunctionType.prototype.tsubst = function(map) {
  const from = this.fromType.tsubst(map);
  const to = this.toType.tsubst(map);
  return (from === this.fromType && to === this.toType
          ? this
          : new FunctionType(from, to));
};


//// Finding TypeVariable names.

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



//// EXPORTS

Toy.andUnifTypes = andUnifTypes;
Toy.unifTypesList = unifTypesList;
Toy.resolve = resolve;
Toy.fullUnifTypes = fullUnifTypes;
Toy.isTriv = isTriv;
Toy.coreUnifTypes = coreUnifTypes;

})();
