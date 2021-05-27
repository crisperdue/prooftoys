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
function isTriv(bind, name, term, exit) {
  if (term instanceof TypeVar) {
    const n2 = term.name;
    if (name === n2) {
      return true;
    } else {
      const b = Toy.findBinding(n2, bind);
      return !!b && isTriv(bind, name, b.to);
    }
  } else if (term instanceof FuncType) {
    return (isTriv(bind, name, term.types[0], exit) ||
            isTriv(bind, name, term.types[1], exit)
            ? exit(false)
            : false);
  } else {
    return false;
  }
}

// Returns bindings if the pairs unify (possibly null if
// no substitution is needed); or false if they do not unify.
function coreUnify(bind_arg, pairs_arg) {
  return Toy.withExit(exit => {
    function unite(bind, pairs) {
      if (pairs == null) {
        return bind;
      } else {
        const unifVar = (v, term) => {
          const name = v.name;
          const found = Toy.findBinding(name, bind);
          if (found) {
            return unite(bind, new Bindings(found.to, term, pairs.more));
          } else {
            return unite(isTriv(bind, name, term, exit)
                          ? bind
                          : new Bindings(name, term, bind),
                          pairs.more);
          }
        };
        const x = pairs.from;
        const y = pairs.to;
        const xt = x.constructor;
        const yt = y.constructor;
        if (xt === TypeConst && yt === TypeConst && x === y) {
          return unite(bind, pairs.more);
        } else if (xt === TypeVar) {
          return unifVar(x, y);
        } else if (yt === TypeVar) {
          return unifVar(y, x);
        } else if (xt === FuncType && yt === FuncType) {
          const newPairs =
                new Bindings(x.types[1], y.types[1],
                             new Bindings(x.types[0], y.types[0], pairs.more));
          return unite(bind, newPairs);
        } else {
          return false;
        }
      }
    }
    return unite(bind_arg, pairs_arg);
  });
}

// This is substitution into a type term.
function tsubst(bind, tm) {
  const type = tm.constructor;
  if (type === TypeVar) {
    const found = Toy.findBinding(tm.name, bind);
    if (found) {
      return found.to;
    }
  } else if (type === FuncType) {
    const t1 = tm.types[1];
    const t0 = tm.types[0];
    const newT1 = tsubst(bind, tm.types[1]);
    const newT0 = tsubst(bind, tm.types[0]);
    if (newT1 !== t1 || newT0 !== t0) {
      return new FuncType(newT1, newT0);
    }
  }
  return tm;
}

// Converts the result of "coreUnify" into a single substitution that does
// the entire work.
function resolve(bind) {
  if (bind) {
    let changed;
    // Continue doing rounds of substitution until no term changes.
    do {
      changed = false;
      let bind2 = null;
      for (const [nm, term] of bind) {
        const term2 = tsubst(bind, term);
        // This test presumes that a no-op substitution
        // returns its input, not a copy.
        if (term2 !== term) {
          changed = true;
        }
        bind2 = new Bindings(nm, term2, bind2);
      }
      bind = bind2;
    } while (changed);
  }
  return bind;
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
  return coreUnify(null, new Toy.Bindings(term1, term2, null));
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
