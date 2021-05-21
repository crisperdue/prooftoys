// Copyright Crispin Perdue.  All rights reserved.

var Toy = Toy || {};

(function() {

'use strict';

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
      return !!b || isTriv(bind, name, b.to);
    }
  } else if (term instanceof FuncType) {
    return (isTriv(bind, name, term.types[0]) ||
            isTriv(bind, name, term.types[1]) ||
            Toy.abort('Foo'));
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
                     : new Bindings(name, term, pairs.more));
      }
    }
    const x = pairs.from;
    const y = pairs.to;
    if (x instanceof TypeVar) {
      return unifVar(x, y);
    } else if (y instanceof TypeVar) {
      return unifVar(y, x);
    } else if (x instanceof FuncType && y instanceof FuncType) {
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

}

function fullunify(term1, term2) {

}

})();
