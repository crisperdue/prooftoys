// Copyright Crispin Perdue.  All rights reserved.

'use strict';

+function() {

  var tt = str => Toy.tokenizeType(str).map(x => x.name);

  var pt = Toy.pt;
  var unif1 = Toy.unif1;
  var isTriv = Toy.isTriv;
  var unify = Toy.unify;
  var solve = Toy.solve;
  var fullUnify = Toy.fullUnify;

  var tests = {

    hello: a => {
      a.ok(1);
      a.ok(true);
    },

    tokTypes: a => {
      const deq = a.deepEqual.bind(a);
      deq(tt('o'), ['o']);
      deq(tt('i'), ['i']);
      deq(tt('oi'), ['oi']);
      deq(tt(' 10'), ['10']);
      deq(tt(' asdf10'), ['asdf10']);
      deq(tt('o i'), ['o', 'i']);
      deq(tt('(o i)'), ['(', 'o', 'i', ')']);
      deq(tt('(o i)(o i)'), ['(', 'o', 'i', ')', '(', 'o', 'i', ')']);
      deq(tt('  o    i )(   ('), ['o', 'i', ')', '(', '(']);
    },

    testIsTriv: a => {
      a.ok(isTriv(null, 't', pt('t')));
      a.notOk(isTriv(null, 't', pt('o')));
      a.notOk(isTriv(null, 't', pt('o i')));
      a.throws(() => isTriv(null, 't', pt('(o t)')));
      a.notOk(isTriv(null, 't', pt('o i')));
    }

  };

  // Run them:

  QUnit.module('Unif');

  const todos = new Set();
  for (var name in tests) {
    var fn = tests[name];
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
