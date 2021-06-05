//// Copyright Crispin Perdue.  All rights reserved.

//// Unification in the style of John Harrison's "Practical Logic".

'use strict';

(function() {

const TypeVar = Toy.TypeVariable;
const TypeConst = Toy.TypeConstant;
const FuncType = Toy.FunctionType;
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
// returning null.
function isTriv(map, name, term) {
  if (term instanceof TypeVar) {
    const n2 = term.name;
    if (name === n2) {
      return true;
    } else {
      const to = map.get(n2)
      return !!to && isTriv(map, name, to);
    }
  } else if (term instanceof FuncType) {
    return (isTriv(map, name, term.types[0]) ||
            isTriv(map, name, term.types[1])
            ? null
            : false);
  } else {
    return false;
  }
}

// Consider an additional pair to be unified in the context
// of the given map of bindings and array of pairs still
// to be unified.
function unifyStep(x, y, map, pairs) {
  const xt = x.constructor;
  const yt = y.constructor;
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
  if (xt === TypeConst && yt === TypeConst && x === y) {
    return true;
  } else if (xt === TypeVar) {
    return unifVar(x, y);
  } else if (yt === TypeVar) {
    return unifVar(y, x);
  } else if (xt === FuncType && yt === FuncType) {
    // Push two new pairs onto the work queue.
    pairs.push([x.types[0], y.types[0]],
               [x.types[1], y.types[1]]);
    return true;
  } else {
    // Unification has failed, though not cyclic.
    return false;
  }
}

// Returns true if the pairs unify, with the map holding the
// unification, or false if they do not.  The unification may still
// need to be resolved.  Treats the pairs as a stack, so examines the
// last pair first.
function coreUnify(map_arg, pairs_arg) {
  const map = map_arg;
  const pairs = pairs_arg;
  while (pairs.length > 0) {
    const [x, y] = pairs.pop();
    if (!unifyStep(x, y, map, pairs)) {
      return false;
    }
  }
  return true;
}

// Attempts to unify terms x and y in the context of an existing
// unification given in the map.  Returns true with the map updated on
// success; otherwise false.
function andUnify(x, y, map) {
  const pairs = [];
  return (unifyStep(x, y, map, pairs) &&
          coreUnify(map, pairs));
}

// This is substitution into a type term.
function tsubst(map, tm) {
  const type = tm.constructor;
  if (type === TypeVar) {
    return map.get(tm.name) || tm;
  } else if (type === FuncType) {
    const t1 = tm.types[1];
    const t0 = tm.types[0];
    const newT1 = tsubst(map, tm.types[1]);
    const newT0 = tsubst(map, tm.types[0]);
    return (newT1 === t1 && newT0 === t0
            ? tm
            : new FuncType(newT1, newT0));
  } else {
    return tm;
  }
}

// Converts the successful result of "coreUnify" into a single
// substitution that does the entire work, or passes along
// a null result.
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
        const term2 = tsubst(map, term);
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

function fullUnify(term1, term2) {
  return unif2(term1, term2);
}

// For debugging: parses a string representing
// a type term.
function pt(tterm) {
  return Toy.parseType(tterm);
}

// For debugging and perhaps other purposes; returns a Map with the
// result of fully unifying just term1 and term2.
function unif2(term1, term2) {
  const map = new Map();
  return (andUnify(term1, term2, map)
          ? resolve(map)
          : null);
}

// Like unif2, but does not resolve.  Is this useful?
// It might serve under a name like canUnify.
function unif2a(term1, term2) {
  const map = new Map();
  return (andUnify(term1, term2, map)
          ? map
          : null);
}

// TODO: Define unif2Map, that takes string inputs and returns a Map
//   with the bindings in order of their creation; then interactively
//   test it;

Toy.tsubst = tsubst;
Toy.isTriv = isTriv;
Toy.coreUnify = coreUnify;
Toy.andUnify = andUnify;
Toy.resolve = resolve;
Toy.fullUnify = fullUnify;
Toy.pt = pt;
Toy.unif2 = unif2;
Toy.unif2a = unif2a;

})();
