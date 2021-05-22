// Copyright Crispin Perdue.  All rights reserved.

'use strict';

(function() {

const TypeVar = Toy.TypeVariable;
const TypeConst = Toy.TypeConstant;
const FuncType = Toy.FunctionType;
const Bindings = Toy.Bindings;
const findBinding = Toy.findBinding;

// Given bindings of names to terms, a variable name, and a term,
// returns true iff the variable matches the term, after applying (one
// of) the bindings if necessary.  This result indicates that the
// current bindings are sufficient to match the variable with the
// term.  Otherwise false.
//
// Also detects if the new match would introduce circularity, and in
// this case throws an Error.
function isTriv(bind, name, term) {
  if (term instanceof TypeVar) {
    const n2 = term.name;
    if (name === n2) {
      return true;
    } else {
      const b = Toy.findBinding(n2, bind);
      return !!b && isTriv(bind, name, b.to);
    }
  } else if (term instanceof FuncType) {
    return (isTriv(bind, name, term.types[0]) ||
            isTriv(bind, name, term.types[1])
            ? Toy.abort('cyclic')
            : false);
  } else {
    return false;
  }
}

function unify(bind, pairs) {
  if (pairs == null) {
    return bind;
  } else {
    const unifVar = (v, term) => {
      const name = v.name;
      const found = Toy.findBinding(name, bind);
      if (found) {
        return unify(bind, new Bindings(found.to, term, pairs.more));
      } else {
        return unify(isTriv(bind, name, term)
                     ? bind
                     : new Bindings(name, term, bind),
                     pairs.more);
      }
    }
    const x = pairs.from;
    const y = pairs.to;
    const xt = x.constructor;
    const yt = y.constructor;
    if (xt === TypeConst && yt === TypeConst && x === y) {
      return unify(bind, pairs.more);
    } else if (xt === TypeVar) {
      return unifVar(x, y);
    } else if (yt === TypeVar) {
      return unifVar(y, x);
    } else if (xt === FuncType && yt === FuncType) {
      const newPairs =
            new Bindings(x.types[0], y.types[0],
                         new Bindings(x.types[1], y.types[1], pairs.more));
      return unify(bind, newPairs);
    } else {
      Toy.abort('No unifier');
    }
  }
}

function solve(bind) {
  return;
}

function fullUnify(term1, term2) {

}

// For debugging: parses a string representing
// a type term.
function pt(tterm) {
  return Toy.parseType(tterm);
}

// For debugging and perhaps other purposes; returns a Map with the
// bindings from unifying just term1 and term2.
function unif1(term1, term2) {
  const BB = Toy.Bindings;
  return new Map(Toy.unify(null, new BB(term1, term2, null)));
}

Toy.isTriv = isTriv;
Toy.unify = unify;
Toy.solve = solve;
Toy.fullUnify = fullUnify;
Toy.pt = pt;
Toy.unif1 = unif1;

})();
