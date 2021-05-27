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
// invoking the exit with the false value.
function isTriv(map, name, term, exit) {
  if (term instanceof TypeVar) {
    const n2 = term.name;
    if (name === n2) {
      return true;
    } else {
      const to = map.get(n2)
      return !!to && isTriv(map, name, to);
    }
  } else if (term instanceof FuncType) {
    return (isTriv(map, name, term.types[0], exit) ||
            isTriv(map, name, term.types[1], exit)
            ? exit(false)
            : false);
  } else {
    return false;
  }
}

// Returns a map if the pairs unify, or false if they do not unify.
function coreUnify(map_arg, pairs_arg) {
  return Toy.withExit(exit => {
    const map = map_arg;
    function unite(pairs) {
      if (pairs == null) {
        return map;
      } else {
        const unifVar = (v, term) => {
          const name = v.name;
          const found = map.get(name);
          if (found) {
            return unite(new Bindings(found, term, pairs.more));
          } else {
            if (!isTriv(map, name, term, exit)) {
              map.set(name, term);
            }
            return unite(pairs.more);
          }
        };
        const x = pairs.from;
        const y = pairs.to;
        const xt = x.constructor;
        const yt = y.constructor;
        if (xt === TypeConst && yt === TypeConst && x === y) {
          return unite(pairs.more);
        } else if (xt === TypeVar) {
          return unifVar(x, y);
        } else if (yt === TypeVar) {
          return unifVar(y, x);
        } else if (xt === FuncType && yt === FuncType) {
          const newPairs =
                new Bindings(x.types[1], y.types[1],
                             new Bindings(x.types[0], y.types[0], pairs.more));
          return unite(newPairs);
        } else {
          return false;
        }
      }
    }
    return unite(pairs_arg);
  });
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

// Converts the result of "coreUnify" into a single substitution that does
// the entire work.
function resolve(map) {
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
  return resolve(unif2(term1, term2));
}

// For debugging: parses a string representing
// a type term.
function pt(tterm) {
  return Toy.parseType(tterm);
}

// For debugging and perhaps other purposes; returns a Map with the
// bindings from unifying just term1 and term2.
function unif2(term1, term2) {
  return coreUnify(new Map(), new Toy.Bindings(term1, term2, null));
}

// TODO: Define unif2Map, that takes string inputs and returns a Map
//   with the bindings in order of their creation; then interactively
//   test it;

Toy.tsubst = tsubst;
Toy.isTriv = isTriv;
Toy.coreUnify = coreUnify;
Toy.resolve = resolve;
Toy.fullUnify = fullUnify;
Toy.pt = pt;
Toy.unif2 = unif2;

})();
