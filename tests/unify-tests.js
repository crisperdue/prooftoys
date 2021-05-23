// Copyright Crispin Perdue.  All rights reserved.

'use strict';

+function() {

  const Bindings = Toy.Bindings;

  const pt = Toy.parseType;
  const unif1 = Toy.unif1;
  const isTriv = Toy.isTriv;
  const unify = Toy.unify;
  const solve = Toy.solve;
  const fullUnify = Toy.fullUnify;

  const bind1 = new Bindings('t1', pt('i'));
  const bind2 = new Bindings('t2', pt('o i'));

  window.bind1 = bind1;
  window.bind2 = bind2;

  const tests = {

    tokTypes: a => {
      // This is an array of the names of all of the tokens.
      const tt = str => Toy.tokenizeType(str).map(x => x.name);
      const equal = a.deepEqual.bind(a);
      equal(tt('o'), ['o']);
      equal(tt('i'), ['i']);
      equal(tt('oi'), ['oi']);
      equal(tt(' 10'), ['10']);
      equal(tt(' asdf10'), ['asdf10']);
      equal(tt('o i'), ['o', 'i']);
      equal(tt('(o i)'), ['(', 'o', 'i', ')']);
      equal(tt('(o i)(o i)'), ['(', 'o', 'i', ')', '(', 'o', 'i', ')']);
      equal(tt('  o    i )(   ('), ['o', 'i', ')', '(', '(']);
    },

    testIsTriv: a => {
      a.ok(isTriv(null, 't', pt('t')));
      a.notOk(isTriv(null, 't', pt('o')));
      a.notOk(isTriv(null, 't', pt('o i')));
      a.throws(() => isTriv(null, 't', pt('(o t)')));
      a.notOk(isTriv(null, 't', pt('o i')));
      a.notOk(isTriv(null, 't', pt('o t2')));
    },

    testUnif1: a => {
      const equal = a.deepEqual.bind(a);
      // This converts a Bindings into an array of strings; if null,
      // i.e. no bindings, an empty array.
      const asArray = bb => {
        const result = [];
        if (bb) {
          for (const [k, v] of bb) {
            result.push(k, v && v.toString());
          }
        }
        return result;
      };
      const array1 = (a, b) => {
        const bind = unif1(pt(a), pt(b));
        console.log('' + bind);
        return asArray(bind);
      };
      equal(array1('i', 'i'), []);
      equal(array1('t', 't'), []);
      equal(array1('t', 'i'), ['t', 'i']);
      equal(array1('o', 't1'), ['t1', 'o']);
      equal(array1('t', 'o i'), ['t', '(o i)']);
      // Ordering of the result pair can be treated as arbitrary,
      // but it may be useful to predict it.
      equal(array1('t1', 't2'), ['t1', 't2']);
      equal(array1('t2', 't1'), ['t2', 't1']);
    }

  };

  // Run them:

  QUnit.module('Unif');

  const todos = new Set();
  for (var name in tests) {
    const fn = tests[name];
    if (typeof fn === 'function') {
      if (todos.has(name)) {
        QUnit.todo(name, fn);
      } else {
        QUnit.test(name, fn);
      }
    } else {
      console.log(name + ': not a function');
    }
  }

}();
