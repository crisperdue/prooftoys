// Copyright Crispin Perdue.  All rights reserved.

'use strict';

+function() {

  const rules = Toy.rules;

  const Bindings = Toy.Bindings;
  const TypeVariable = Toy.TypeVariable;
  const FunctionType = Toy.FunctionType;

  const pt = Toy.parseType;
  const fullUnifTypes = Toy.fullUnifTypes;
  const coreUnifTypes = Toy.coreUnifTypes;
  const checkTriv = Toy.checkTriv;
  const unifTypesList = Toy.unifTypesList;
  const resolve = Toy.resolve;
  
  // This converts a Map result of unification into an array of pairs
  // of strings representing it.  If given a falsy value, returns it.
  function asArray(map) {
    if (!map) {
      return map;
    } else {
      const result = [];
      for (const [k, v] of map) {
        result.push([k, v.toString()]);
      }
      return result;
    }
  }

  function unif2Array(a, b) {
    const map = fullUnifTypes(pt(a), pt(b));
    // console.log(map);
    return asArray(map);
  }

  function unif2aArray(a, b) {
    const map = coreUnifTypes(pt(a), pt(b));
    // console.log(map);
    return asArray(map);
  }

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
      const check =
            (inStr, map, out) => a.equal('' + pt(inStr).tsubst(map), out);

      const map1 = new Map([['t1', pt('t2')]]);
      check('(o (t1 t2))', map1, '(o (t2 t2))');

      const map2 = new Map([['t1', pt('o t2')]]);
      check('(o (t1 t2))', map2,
            '(o ((o t2) t2))');

      const map3 = new Map([['t1', pt('o t2')],
                            ['t2', pt('i t3')]]);
      check('(o (t1 t2))', map3,
            '(o ((o t2) (i t3)))');
    },

    function testIsTriv(a) {
      a.ok(checkTriv(new Map(), 't', pt('t')));
      a.notOk(checkTriv(new Map(), 't', pt('o')));
      a.notOk(checkTriv(new Map(), 't', pt('o i')));
      a.equal(checkTriv(new Map(), 't', pt('(o t)')), null);
      a.notOk(checkTriv(new Map(), 't', pt('o i')));
      a.notOk(checkTriv(new Map(), 't', pt('o t2')));
    },

    function testUnifTypesList(a) {
      a.ok(true);
      const v1 = new TypeVariable();
      const v2 = new TypeVariable();
      const v3 = new TypeVariable();
      const pair0 = [v1, Toy.boolean];
      const pair1 = [new FunctionType(v2, v1), v3];
      const pair2 = [v2, new FunctionType(v3, v3)];
      let pairs = [pair0, pair1, pair2];
      // [[t1, o], [(t1 t2), t3], [t2, (t3 t3)]]
      const subst = new Map();
      const result = unifTypesList(subst, pairs);
      a.equal(result, null);
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
      equal(unif2Array('((o i) t1 t2)', '(i t2 t1)'), null);
      // Cyclic
      equal(unif2Array('t', 'o t'), null);
      equal(unif2Array('t t', 't (o t)'), null);
      equal(unif2Array('t t', 't (t o)'), null);

      equal(unif2Array('(o i) t1 t2', '(o i) t2 t1'), [['t1', 't2']]);
      equal(unif2Array('i t1 (i t2)', 'i (i t2) t1'),
            [['t1', '(i t2)']]);
      equal(unif2Array('i t1 (i t2)', 'i (i t3) t4'),
            [['t1', '(i t3)'], ['t4', '(i t2)']]);
    },

    // These give results that are not resolved.
    function testUnif2c(a) {
      const check = (t1, t2, expected) =>
            a.deepEqual(unif2aArray(t1, t2), expected);

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
            a.deepEqual(asArray(fullUnifTypes(pt(t1), pt(t2))),
                        expected);

      check('t1 t1', 't2 i', [['t1', 'i'], ['t2', 'i']]);
      check('t2 i', 't1 t1', [['t2', 'i'], ['t1', 'i']]);
      check('t t t', 't1 (t2 t2) t1',
            [['t', '(t2 t2)'], ['t1', '(t2 t2)']]);
      check('(t1 t2) (t2 t1)', 't3 t3',
            [['t3', '(t2 t2)'], ['t1', 't2']]);
    },

    function testAddTVars(a) {
      const check = (str, expected) => {
        var vars = new Set();
        pt(str)._addTVars(vars);
        return a.deepEqual(Array.from(vars).sort(), expected);
      };

      check('o i', []);
      check('t1 t2 t3', ['t1', 't2', 't3']);
      check('t3 t2', ['t2', 't3']);
      check('(o t3) (t2 i) (t2 t2)', ['t2', 't3']);
    },

    function testTypeVars(a) {
      const the = rules.definition('the');
      a.equal(the.typeVars().size, 1);

      const all = rules.definition('forall');
      a.equal(all.typeVars().size, 1);

      const fun = rules.axiom3();
      a.equal(fun.typeVars().size, 2);
    },

    function testSubsType(a) {
      const fun = rules.axiom3();
      const vars = Array.from(fun.typeVars());
      const pairs = [];
      vars.forEach((v, i) => pairs.push([v, new TypeVariable('t' + i)]));
      const textual =
            fun.show().replaceAll(pairs[0][0], pairs[0][1])
            .replaceAll(pairs[1][0], pairs[1][1]);

      const map = new Map(pairs);
      const result = fun.wff.subsType(map);
      a.equal(result.show(), textual);
    },

    function testDistinctifyTypes(a) {
      const a3 = rules.axiom3().wff;
      {
        const map = a3.typesDistinctifier(a3);
        a.ok(map.size, 'axiom3 changed');
      }
      const taut1 = rules.tautology('a => a').wff;
      {
        const map = taut1.typesDistinctifier(taut1);
        a.ok(map.size === 0, 'no type vars');
      }
      {
        const map = a3.typesDistinctifier(taut1);
        a.ok(map.size === 0, 'no conflicts')
      }
      {
        const xx = rules.eqSelf('x');
        const x1 = rules.eqSelf('x + 1');
        const map = xx.wff.typesDistinctifier(x1.wff);
        a.ok(map.size === 0, 'no conflicts');
      }
      {
        const xx = rules.eqSelf('x');
        const x1 = xx.andThen('instVar', 'x + 1', 'x');
        const map = xx.wff.typesDistinctifier(x1.wff);
        a.ok(map.size === 0, 'no conflicts');
      }
    },

    function testTypesUnifier(a) {
      const x1 = rules.eqSelf('x');
      const x2 = rules.eqSelf('y');
      const unifier = x1.wff.typesUnifier(x2.wff);
      a.ok(unifier instanceof Map);
      a.equal(unifier.size, 1);
    }
  ];

  // Run them:

  QUnit.module('Unif');

  for (var fn of tests) {
    const name = fn.name;
    if (typeof fn === 'function') {
      if (name.startsWith('TODO')) {
        QUnit.test.todo(name, fn);
      } else {
        QUnit.test(name, fn);
      }
    } else {
      console.log(name + ': not a function');
    }
  }

}();
