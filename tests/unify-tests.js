// Copyright Crispin Perdue.  All rights reserved.

'use strict';

+function() {

  const Bindings = Toy.Bindings;

  const pt = Toy.parseType;
  const unif2 = Toy.unif2;
  const isTriv = Toy.isTriv;
  const coreUnify = Toy.coreUnify;
  const resolve = Toy.resolve;
  const fullUnify = Toy.fullUnify;
  
  // This converts a Bindings result of unification into an array of
  // strings; if null, i.e. no bindings, an empty array.  If false,
  // then false.
  function asArray(bb) {
    if (bb === false) {
      return false;
    }
    const result = [];
    if (bb) {
      for (const [k, v] of bb) {
        // The first binding encountered was added last, so put it at
        // the end of the array.
        result.unshift([k, v && v.toString()]);
      }
    }
    return result;
  }

  // Builds and returns bindings from the given array of from, to
  // pairs, with both "from" and "to" given as strings.
  function newB(pairs) {
    let result = null;
    for (const [from, to] of pairs) {
      result = new Bindings(from, pt(to), result);
    }
    return result;
  }

  function unif2Array(a, b) {
    const bind = unif2(pt(a), pt(b));
    // console.log('' + bind);
    return asArray(bind);
  }

  const bind1 = new Bindings('t1', pt('i'));
  const bind2 = new Bindings('t2', pt('o i'));

  const tests = [

    function testTokenizing(a) {
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
      equal(tt('(o i)(o i)'),
            ['(', 'o', 'i', ')', '(', 'o', 'i', ')']);
      // Tokenize an ill-formed string.
      equal(tt('  o    i )(   ('),
            ['o', 'i', ')', '(', '(']);
    },

    function testTsubst(a) {
      const ts = (bind, termStr) => 'foo';
      a.ok(ts(1, 2));
    },

    function testNewB(a) {
      const a1 = [['t1', 'i'], ['t2', 't3']];
      const b1 = newB(a1);
      a.deepEqual(asArray(b1), a1);
      const a2 = [];
      const b2 = newB(a2);
      a.equal(b2, null);
      a.deepEqual(asArray(b2), a2);
    },

    function testIsTriv(a) {
      a.ok(isTriv(null, 't', pt('t')));
      a.notOk(isTriv(null, 't', pt('o')));
      a.notOk(isTriv(null, 't', pt('o i')));
      a.throws(() => isTriv(null, 't', pt('(o t)')));
      a.notOk(isTriv(null, 't', pt('o i')));
      a.notOk(isTriv(null, 't', pt('o t2')));
    },

    function testUnif2a(a) {
      const equal = a.deepEqual.bind(a);
      equal(unif2Array('i', 'i'), []);
      equal(unif2Array('t', 't'), []);
      equal(unif2Array('t', 'i'), [['t', 'i']]);
      equal(unif2Array('o', 't1'), [['t1', 'o']]);
      equal(unif2Array('t', 'o i'), [['t', '(o i)']]);

      // Ordering of the result pair can be treated as arbitrary,
      // but it may be useful to predict it.
      equal(unif2Array('t1', 't2'), [['t1', 't2']]);
      equal(unif2Array('t2', 't1'), [['t2', 't1']]);
    },

    function testUnif2b(a) {
      const equal = a.deepEqual.bind(a);
      // Constants mismatch
      equal(unif2Array('((o i) t1 t2)', '(i t2 t1)'), false);
      // Cyclic
      equal(unif2Array('t', 'o t'), false);
      equal(unif2Array('t t', 't (o t)'), false);
      equal(unif2Array('t t', 't (t o)'), false);


      equal(unif2Array('(o i) t1 t2', '(o i) t2 t1'), [['t1', 't2']]);
      equal(unif2Array('i t1 (i t2)', 'i (i t2) t1'),
            [['t1', '(i t2)']]);
      equal(unif2Array('i t1 (i t2)', 'i (i t3) t4'),
            [['t1', '(i t3)'], ['t4', '(i t2)']]);
    },

    // These give results that are not resolved.
    function testUnif2c(a) {
      const check = (t1, t2, expected) =>
            a.deepEqual(unif2Array(t1, t2), expected);

      check('t1 t1', 't2 i', [['t1', 't2'], ['t2', 'i']]);
      check('t2 i', 't1 t1', [['t2', 't1'], ['t1', 'i']]);
      check('t t t', 't1 (t2 t2) t1',
            [['t', 't1'], ['t1', '(t2 t2)']]);
      check('(t1 t2) (t2 t1)', 't3 t3',
            [['t3', '(t1 t2)'], ['t1', 't2']]);
    },

    // Like testUnif2c, but with results resolved.
    function testUnif2d(a) {
      const check = (t1, t2, expected) =>
            a.deepEqual(asArray(resolve (unif2(pt(t1), pt(t2)))),
                        expected);

      check('t1 t1', 't2 i', [['t1', 'i'], ['t2', 'i']]);
      check('t2 i', 't1 t1', [['t2', 'i'], ['t1', 'i']]);
      check('t t t', 't1 (t2 t2) t1',
            [['t', '(t2 t2)'], ['t1', '(t2 t2)']]);
      check('(t1 t2) (t2 t1)', 't3 t3',
            [['t3', '(t2 t2)'], ['t1', 't2']]);
    },

  ];

  // Run them:

  QUnit.module('Unif');

  for (var fn of tests) {
    const name = fn.name;
    if (typeof fn === 'function') {
      if (name.startsWith('TODO')) {
        QUnit.todo(name, fn);
      } else {
        QUnit.test(name, fn);
      }
    } else {
      console.log(name + ': not a function');
    }
  }

  // Support interactive testing (temporarily):

  window.aa = asArray;
  window.newB = newB;

  window.bind1 = bind1;
  window.bind2 = bind2;

}();
