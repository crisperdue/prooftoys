// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

(function() {

// Run tests with all facts being proved.
Toy.assertFacts = false;

// Make some names visible throughout
var rules = Toy.rules;
var ruleData = Toy.ruleData;
var varify = Toy.varify;
var constify = Toy.constify;
var termify = Toy.termify;
var call = Toy.call;
var equal = Toy.equal;
var implies = Toy.implies;
var lambda = Toy.lambda;

var Atom = Toy.Atom;
var a = varify('a');
var b = varify('b');
var c = varify('c');
var x = varify('x');
var y = varify('y');
var z = varify('z');
var f = varify('f');
var g = varify('g');
var h = varify('h');
var p = varify('p');
var q = varify('q');
var r = varify('r');
var T = constify('T');
var F = constify('F');

var parse = Toy.parse;

// Define a constant 'posNum', known to be a number greater than 0,
// which is defined with an existential fact.
Toy.definex('posNum', rules.eQuantify(rules.fact('1 > 0'), '/left'));


// Assertion utilities:

function assertEqual(a, b) {
  if (typeof a === 'string' && b instanceof Toy.Expr) {
    // Crudely remove indications of bound variable IDs.
    // This could be done carefully on the structure of
    // b if necessary, or with a flag for toString.
    b = b.toString().replace(/[.][0-9]+/g, '');
  }
  return deepEqual(b, a);
}

function assertMatches(expected, actual, msg) {
  assert(termify(expected).matches(actual),
         msg +
         'Expected: ' + expected.toString() +
         '\ngot: ' + actual.toString());
}

function assertFails(fn) {
  var debug = Toy.debugAssertions;
  try {
    Toy.debugAssertions = false;
    throws(fn);
  } catch(e) {
    assert(e.isAssert, "Test threw, but not an assertion failure");
  } finally {
    Toy.debugAssertionss = debug;
  }
}

// Make "assert" a synonym for QUnit's ok function.
var assert = ok;

// For testing convenience automatically assert steps from wffs.
// TODO: Eliminate the need for this.
Toy.autoAssert = true;

/**
 * Check effect of a rewriter.  Null expected value means expected
 * null result.  Empty expected string means just log the result for
 * debugging.
 */
function checkRewriter(expected, input, rule) {
  var input = typeof input == 'string' ? Toy.parse(input) : input;
  var equation = rule(input);
  if (expected == null) {
    assertEqual(null, equation);
  } else {
    assert(equation);
    var actual = equation.getRight();
    if (expected) {
      assertEqual(expected, actual);
    } else {
      console.log(actual);
    }
  }
}

/**
 * Copy a value for presentation to QUnit.deepEqual, which looks in
 * too many places.
 */
function qUnitCopy(obj) {
  if (typeof obj !== 'object') {
    return obj;
  }
  if (obj === null) {
    return obj;
  }
  if (obj.qUnitCopy) {
    return obj.qUnitCopy();
  }
  if (Array.isArray(obj)) {
    return obj.map(x => qUnitCopy(x));
  }
  if (obj.constructor === Object) {
    var keys = Object.keys(obj);
    var copy = {};
    keys.forEach(k => copy[k] = qUnitCopy(obj[k]));
    return copy;
  }
  return obj;
}

// Customize copying of Exprs.
Toy.Expr.prototype.qUnitCopy = function() {
  return 'Expr ' + this.toUnicode();
};

// Customize copying of TermSets.
Toy.TermSet.prototype.qUnitCopy = function() {
  var members = [];
  this.each(x => void members.push(x.toUnicode()));
  return members.sort();
};

/**
 * Copies the object with qUnitCopy and logs the copy to the console.
 */
function logDeeply(obj) {
  console.log(JSON.stringify(qUnitCopy(obj), null, 1));
}

/**
 * Runs a test, providing opportunity for logging or other extra
 * activity.
 */
function runTest(name, fn) {
  // Uncomment this to log the start of each test function.
  // console.log('Running', name);
  return test(name, fn);
}


// Set up some useful constants and functions.

// Do not display source step info in toString.
Toy.trackSourceSteps = false;

// Example equation: x + x = 2 * x
var times2 = call('=', call('+', x, x), call('*', '2', x));

// Example WFF: x > 0 => x + x > x
var bigger = call('=>', call('>', x, '0'),
                  call('>', call('+', x, x), x));

// This is a bit different than standard QUnit style, but the content
// is the same.  The code block just below interprets all of these as
// qUnit tests.
var testCase = {

  // Warmups, to confirm what some assertions do.

  testTrue: function() {
    assertEqual(true, true);
  },
  test11: function() {
    assertEqual(1, 1);
  },

  // Utilities

  testGcd: function() {
    gcd = Toy.gcd;
    assertEqual(12, gcd(60, 24));
    assertEqual(0, gcd(1.5, .5));
    assertEqual(0, gcd(-1.5, -.3));
    assertEqual(6, gcd(240, 18));
    assertEqual(2, gcd(-16, 6));
    assertEqual(2, gcd(-16, -6));
  },

  testDiv: function() {
    var div = Toy.div;
    assertEqual(2, div(8, 3));
    assertEqual(-3, div(8, -3));
    assertEqual(-3, div(-8, 3));
    assertEqual(2, div(-8, -3));
  },

  testMod: function() {
    var mod = Toy.mod;
    assertEqual(2, mod(8, 3));
    assertEqual(-1, mod(8, -3));
    assertEqual(1, mod(-8, 3));
    assertEqual(-2, mod(-8, -3));
  },

  testGetPrimes: function() {
    var primes = Toy.getPrimes()
    assertEqual(2, primes[0]);
    assertEqual(3432, primes.length);
    assertEqual(31991, primes[primes.length - 1]);
  },

  testNextPrimeFactor: function() {
    var factor = Toy.nextPrimeFactor;
    assertEqual(5, factor(55, 0));
    assertEqual(11, factor(55, 5));
    assertEqual(null, factor(55, 11));
  },

  testNpd: function() {
    var npd = Toy.npd;
    assertEqual(null, npd(7, 12, 0));
    assertEqual(3, npd(30, 15, 0));
    assertEqual(5, npd(30, 15, 3));
    assertEqual(null, npd(30, 15, 5));
    assertEqual(null, npd(30, 15, 15));
    assertEqual(3, npd(15, 27, 0))
    assertEqual(null, npd(15, 27, 3));
  },

  testArrayEquals: function() {
    var a1 = [{b: 2}, 'asdf', 13];
    assert(Array.equals(a1, a1));
    var a2 = a1.concat();
    assert(Array.equals(a1, a2));
    assert(!Array.equals(a1, a1.concat([2])));
    assert(!Array.equals([], a1));
    assert(!Array.equals(a1, [1, 2, 3]));
  },

  testMemo: function() {
    var a = [];
    function f() {
      a.push(3);
      return 13;
    }
    var memo = Toy.memo(f);
    assertEqual(13, memo());
    assertEqual(1, a.length);
    assertEqual(13, memo());
    assertEqual(1, a.length);
  },

  // configure

  testConfigure: function() {
    var o = Toy.configure({}, {
        add: function(x) { this[x] = true; },
        list: [1, 2, 3],
        zero: 0,
        count: {value: 1, writable: true}
      });
    assert(typeof o.add === 'function');
    assert(o.list.constructor === Array);
    assert(typeof o.zero === 'number');
    assert(typeof o.count === 'number');
    try {
      o.add = 3;
      Y.assert.fail('Should fail');
    } catch(e){}
    try {
      o.zero = 3;
      Y.assert.fail('Should fail');
    } catch(e){}
    o.count = 3;
    assert(o.count === 3);
  },

  testFormat: function() {
    assertEqual('foo bar baz', Toy.format('foo {1} {2}', 'bar', 'baz'));
    var map = {a: 'bar', b: 'baz'};
    assertEqual('foo bazbar', Toy.format('foo {b}{a}', map));
  },

  testSortMap: function() {
    var map = {a: 3, b: 2, c: 0, d: 1};
    var pairs = Toy.sortMap(map, function(a, b) { return a.value - b.value; });
    assertEqual('cdba', pairs.map(function(v) { return v.key; }).join(''));
  },

  // Sets, TermSets

  testSet: function() {
    var set = new Toy.Set();
    // isEmpty
    assert(set.isEmpty());
    // size
    assertEqual(0, set.size());
    // add and has
    set.add('one');
    set.add(2);
    set.add('three');
    assert(set.has('one'));
    assert(set.has('2'));
    assert(set.has(2));
    assert(set.has('three'));
    // size
    assertEqual(3, set.size());
    // choose
    assert(set.has(set.choose()));
    // remove
    set.remove('three');
    assert(!set.has('three'));
    // each
    var items = [];
    var found = set.each(function(value) {
        items.push(value);
        if (value == 2) {
          return value;
        }
      });
    assertEqual(2, found);
    assert(items.indexOf(2) >= 0);
    // addAll
    var copy = new Toy.Set();
    copy.addAll(set);
    assertEqual(2, copy.size());
    copy.addAll([22]);
    assertEqual(3, copy.size());
    // values
    assertEqual([2, 22, 'one'], copy.values().sort());
  },

  testTermSet: function() {
    var set = new Toy.TermSet();
    var term = call(f, x);
    set.add(term);
    assert(set.has(term));
    assert(!set.has(call(f, y)));
    var items = [];
    set.each(function(value) { items.push(value); });
    assertEqual(1, items.length);
    assertEqual(term, items[0]);
    set.remove(term);
    assertEqual(0, set.size());
    assert(!set.has(term));
    assert(set.isEmpty());

    // Constructor with a term argument:
    term = Toy.parse('p x');
    set = new Toy.TermSet(term);
    assert(set.has(term));
  },

  // Maps, TermMaps

  testMap: function() {
    var map = new Toy.Map();
    var term = call(f, x);
    assert(map.isEmpty());
    assertEqual(0, map.size());
    assert(!map.has('toString'));
    map.set('foo', term);
    assert(map.has('foo'));
    assertEqual(term, map.get('foo'));
    assertEqual(1, map.size());
    var o = {a: 1};
    map.set('bar', o);
    assertEqual(o, map.get('bar'));
    assertEqual(2, map.size());
    map.remove('foo');
    assertEqual(1, map.size());
    map.remove('asdf');
    assertEqual(1, map.size());
    map.each(function(value, key) {
        assertEqual(o, value);
        assertEqual('bar', key);
      });
  },

  testMap0: function() {
    var map = new Toy.Map(String, 0);
    assert(map.isEmpty());
    assert(!map.has('foo'));
    assertEqual(0, map.get('foo'));
  },

  testTermMap: function() {
    var map = new Toy.TermMap();
    var term = Toy.infixCall(x, '=', x);
    var t2 = call(f, y);
    // has
    map._set(term, t2);
    assert(map.has(term));
    // get
    assertEqual(t2, map.get(term));
    // each
    var result = map.each(function(value, key) {
        assertEqual(t2, value);
        assertEqual(term.dump(), key);
        assert(term.toString() != key);
        return true;
      });
    assertEqual(true, result);
    // remove
    map.remove(term);
    assertEqual(0, map.size());
    assert(map.isEmpty());
  },

  testAddTerm: function() {
    var map = new Toy.TermMap();
    var term = Toy.infixCall(x, '=', x);
    var v = map.addTerm(term);
    assertEqual('a1', v);
    assertEqual('a1', map.addTerm(Toy.infixCall(x, '=', x)));
    assertEqual('a2', map.addTerm(call(p, x)));
    assert(map.has(call(p, x)));
    assertEqual('a2', map.get(call(p, x)));
  },

  // Tests for subtypes of Expr

  testVar: function() {
    assertEqual('x', x.toString());
  },

  testApp: function() {
    var app = call(f, x);
    assertEqual(f, app.fn);
    assertEqual(x, app.arg);
    assertEqual('(f x)', app.toString());
  },

  testLambda: function() {
    var abs = lambda(x, f);
    assertEqual(x, abs.bound);
    assertEqual(f, abs.body);
    assertEqual('{x. f}', abs.toString());

    assertEqual('{x. (f x)}', lambda(x, call(f, x)));
  },

  testDump: function() {
    assertEqual('T', T.dump());
    assertEqual('x', x.dump());
    assertEqual('(f x)', call(f, x).dump());
    assertEqual('{x. (f x)}', lambda(x, call(f, x)).dump());
    assertEqual('((= x) y)', call('=', x, y).dump());
  },

  testToUnicode: function() {
    assertEqual('T', T.toUnicode());
    assertEqual('a\u2081\u2080\u2089',  new Toy.Atom('a.109').toUnicode());
    assertEqual('a:R', Toy.varify('a:R').toUnicode());
    assertEqual('xx\u2083:RR', new Toy.Atom('xx.3:RR').toUnicode());
  },

  testExprIn: function() {
    assert(Toy.parse('x').in(['y', 'x']));
    assert(!Toy.parse('x').in(['y', 'z']));
  },

  // PARSER

  testTokenize: function() {
    var result = Toy.tokenize('a');
    assertEqual('a,(end)', result.toString());
    result = Toy.tokenize('(a > b)');
    assertEqual('(,a,>,b,),(end)', result.toString());
    result = Toy.tokenize('{x. x}');
    assertEqual('{,x,.,x,},(end)', result.toString());
    result = Toy.tokenize('(=>x*)');
    assertEqual('(,=>,x,*,),(end)', result.toString());
    result = Toy.tokenize('f "as\\"df" 2');
    assertEqual('f,"as\\"df",2,(end)', result.toString());
    assertEqual('as"df', result[1].getStringValue());
  },

  testParse: function() {
    var result = Toy.parse('a');
    assertEqual('a', result.dump());
    result = Toy.justParse('(xx)');
    assertEqual('xx', result.dump());
    result = Toy.parse('f x');
    assertEqual('(f x)', result.dump());
    result = Toy.parse('(not) = ((=) F)');
    assertEqual('((= not) (= F))', result.dump());
    assertEqual('((neg (neg a)) = a)', Toy.parse('neg (neg a) = a'));
    result = Toy.parse('{x. x} T');
    assertEqual('({x. x} T)', result);
    result = Toy.parse('a + b * c');
    assertEqual('(a + (b * c))', result);
    result = Toy.parse('a => a & c');
    assertEqual('(a => (a & c))', result);
    // Numbers
    assertEqual(42, Toy.parse('42').getNumValue());
    var expr = Toy.parse('x + 103');
    assertEqual(103, expr.getRight().getNumValue());
    assertFails(function() { expr.getLeft().getNumValue(); });
    assertEqual(-2, Toy.parse('-2').getNumValue());
    assert(Toy.parse('- 2') instanceof Toy.Call);
    assertEqual('(-1 + 1)', Toy.parse('-1 + 1'));
    // Strings
    var expr = Toy.justParse('f "asdf"')
    assertEqual('"asdf"', expr.arg.name);
    var expr = Toy.justParse('f "as\\"df"');
    assertEqual('"as\\"df"', expr.arg.name);
    assertEqual(8, expr.getRight().name.length);
  },

  testMathParse: function() {
    var p = Toy.mathParse;
    assertEqual('a', p('a'));
    assertEqual('(x = y)', p('x = y'));
    assertEqual('(((R x) & (R y)) => ((x + y) = (y + x)))',
                p('x + y = y + x'));
    assertEqual('(((R x) & (R y)) => ((x + y) = (y + x)))',
                p('@R x & R y => x + y = y + x'));
    assertEqual('((R x) => ((x + y) = (y + x)))',
                p('@R x => x + y = y + x'));
  },


  // Operations on Exprs.

  testNth: function() {
    var term = Toy.parse('(f x (p y))');
    assertEqual('f', term.nth(0));
    assertEqual('x', term.nth(1));
    assertEqual('(p y)', term.nth(2));
    assertEqual('x', x.nth(0));
  },

  testAsArray: function() {
    var term = Toy.parse('(f x (p y))');
    var array = term.asArray();
    assertEqual(3, array.length);
    assertEqual('f', array[0]);
    assertEqual('x', array[1]);
    assertEqual('(p y)', array[2]);
  },

  testIsNumeral: function() {
    var v = Toy.constify('-3');
    assert(v.isNumeral());
    v = Toy.varify('a1');
    assert(!v.isNumeral());
  },

  testIsString: function() {
    var v =  Toy.constify('"asdf"');
    assert(v.isString());
    v = Toy.varify('a');
    assert(!v.isString());
    v = Toy.constify('-3');
    assert(!v.isString());
  },

  testIsIdentifer: function() {
    var ident = Toy.isIdentifier;
    assert(ident('asdf'));
    assert(ident('axiomCommutativePlus'));
    assert(!ident('a+b'));
    assert(!ident('(a)'));
  },

  testUnparseString: function() {
    var ups = Toy.unparseString;
    assertEqual('"asdf"', ups('asdf'));
    assertEqual('"\\\\asdf"', ups('\\asdf'));
    assertEqual('"asdf\\""', ups('asdf"'));
    assertEqual('"asdf\\n"', ups('asdf\n'));
  },

  testEncodeSteps: function() {
    var step1 = rules.assume('x = y + 3');
    var step2 = rules.assume('x + y = 5');
    var step3 = rules.rplace(step1, step2, Toy.path('/main/left/left'));
    var saved = Toy.encodeSteps([step1, step2, step3]);
    var parsed = Toy.justParse(saved);
    var a = parsed.asArray();
    assertEqual(4, a.length);
    assertEqual('steps', a[0]);
    // Note that testDecodeSteps effectively tests more of this.
  },

  testDecodeArg: function() {
    var steps = [Toy.rules.assert('x = y + 1')];
    function check(expected, input) {
      input = typeof input == 'string' ? Toy.justParse(input) : input;
      var actual = Toy._decodeArg(input, steps);
      assertEqual(expected, actual.toString());
    }
    check('foo', '"foo"');
    check('/right', '(path "/right")');
    check('(x = (y + 1))', '(s 1)');
    check('(p (f x))', '(t (p (f x)))');
  },

  testDecodeSteps: function() {
    var step1 = rules.assume('x = y + 3');
    var step2 = rules.assume('x + y = 5');
    var step3 = rules.rplace(step1, step2, Toy.path('/main/left/left'));
    var saved = Toy.encodeSteps([step1, step2, step3]);
    var steps = Toy.decodeSteps(saved);
    assertEqual(3, steps.length);
    assertEqual('(((y + 3) + y) = 5)', steps[2].unHyp());
  },

  testSameAs: function() {
    var parse = Toy.parse;
    var e = parse('a = b + ({x. x + 1} 4)');
    assert(e.sameAs(e));
    assert(e.sameAs(new Toy.Call(e.fn, e.arg)));
    assert(!e.sameAs(parse('a = b + ({y. y + 1} 4)')));
    assert(!e.sameAs(parse('a = b')));
    assert(!(parse('x = x').sameAs(parse('x == x'))));
    assert(!(parse('(=)').sameAs(parse('(==)'))));
  },

  testFreeVars: function() {
    var wff = lambda(x, call(f, x));
    var map = wff.freeVars();
    assertEqual(true, map['f']);
    assertEqual(undefined, map['x']);
  },

  testBoundNames: function() {
    var wff = lambda(x, call(f, x));
    var map = wff.boundNames('');
    assertEqual('{}', Toy.debugString(map));
    var map = wff.boundNames('/body/arg');
    assertEqual('{x: true}', Toy.debugString(map));
  },

  testCopyForRendering: function() {
    // TODO: Test the rendering-related aspects.
    var source = '(x = x)';
    var target = Toy.parse(source);
    // Copy is equal to original
    assertEqual(source, target.copyForRendering());
    assert(target.matches(target.copyForRendering()));
    // But not identical.
    assert(target !== target.copyForRendering());
  },

  testSubFree: function() {
    var map = Toy.object0;
    var v = varify('v');
    var target = call(lambda(v, v), x);
    // Now substitute in 'a different v':
    var result = target.subFree({x: varify('v')});
    // We see that it replaces just the free occurrence.
    assertEqual('({v. v} v)', result);
    // A case where decapturing is needed.
    result = Toy.parse('{y. x} x').subFree({x: y});
    assertEqual('({y. y} y)', result);
    // A very similar case where it is not needed.
    result = Toy.parse('{y. T} x').subFree({x: y});
    assertEqual('({y. T} y)', result);
    // Multiple substitution.
    result = Toy.parse('x + y').subFree({y: x, x: y});
    assertEqual('(y + x)', result);
    // Failing case 10/2016
    result = Toy.parse('(f = g) == forall {x. f x = g x}').subFree({g: varify('f')});
    assertEqual('((f = f) == (forall {x. ((f x) = (f x))}))', result);
    // Request substitution for bound var.
    result = Toy.parse('({g. (g T T)} = g)').subFree({g: varify('f')});
    assertEqual('({g. (g T T)} = f)', result);
    result = Toy.parse('({g. (g p T)} = g)').subFree({g: varify('f'), p: T});
    assertEqual('({g. (g T T)} = f)', result);
  },

  testMathVars: function() {
    function check(expected, input) {
      input = typeof input == 'string' ? Toy.parse(input) : input;
      var actual = input.mathVars();
      assertEqual(expected, Toy.debugString(actual));
    }
    check('{}', 'x');
    check('{x: true}', 'x + 1');
    check('{x: true}', 'neg x + 1');
    check('{z: true}', '1 + (recip z)');
    check('{}', 'x = y');
    check('{x: true, y: true}', 'x = y + 1');
    check('{x: true, y: true}', 'x + ({z. z + y} 1)');
  },

  testMathVarConditions: function() {
    function check(expected, input) {
      input = typeof input == 'string' ? Toy.parse(input) : input;
      var actual = input.mathVarConditions();
      assertEqual(expected, actual + '');
    }
    check('undefined', 'x');
    check('(R x)', 'x + x');
    check('((R x) & (R y))', 'y + x * y');
    check('(((R x) & (R y)) & (R z))', 'z * y * x');
  },

  testConcat: function() {
    var result = Toy.parse('h').concat(Toy.parse('a'), '&');
    assertEqual('(h & a)', result);
    var result = Toy.parse('h1 & h2').concat(Toy.parse('a'), '&');
    assertEqual('((h1 & h2) & a)', result);
    var result = Toy.parse('h1 & h2').concat(Toy.parse('a & b'), '&');
    assertEqual('(((h1 & h2) & a) & b)', result);
    assertEqual('(((a & (R x)) & (R y)) & (R z))',
                (Toy.parse('a')
                 .concat(Toy.parse('R x & R y & R z'), '&')));
  },

  testIsCall1: function() {
    assertEqual(false, times2.isCall1('='));
    assertEqual(true, Toy.parse('f x').isCall1());
    assertEqual(true, Toy.parse('f x').isCall1('f'));
  },

  testIsCall2: function() {
    assert(times2.isCall2('='), 'Times2 not an equation?');
  },

  testFunc: function() {
    function check(expect, term) {
      assertEqual('' + expect, '' + termify(term).func());
    }
    check(null, '{x. x}');
    check(null, 'T');
    check('f', '(f x)');
    check('=', '0 = 1');
    check('g', 'g 1 2 3 4 5')
  },

  testArgs: function() {
    function check(expect, term) {
      assertEqual(expect.toString(), termify(term).args().$$);
    }
    check('', '{x. x}');
    check('', 'T');
    check('x', '(f x)');
    check('0,1', '0 = 1');
    check('1,2,3,4,5', 'g 1 2 3 4 5')
  },

  testTransformConjuncts: function() {
    function xform(expr) {
      return (expr.matchSchema('a | not a')) ? T : expr;
    }
    assertEqual('((a & b) & c)',
                Toy.parse('a & b & c').transformConjuncts(xform));
    assertEqual('(((T & T) & z) & w)',
                Toy.parse('(x | not x) & (y | not y) & z & w')
                  .transformConjuncts(xform));
  },

  testReplaceAt: function() {
    var y = varify('y');
    var e1 = call(lambda(x, call(f, x)), y);
    var path = Toy.path('/fn/body/arg');
    var result = e1.replaceAt(path, function(expr) { return call(f, x); });
    assertEqual('({x. (f (f x))} y)', result.toString());
    var target = Toy.parse('f x = y');
    result = target.replaceAt(Toy.path('/right'), function(expr) { return z; });
    assert(target.getLeft() === result.getLeft());
  },

  testPath: function() {
    var Path = Toy.Path;

    var p = '/a/b';
    var path = Toy.path(p);
    assertEqual(p, path.toString());
    assertEqual('a', path.segment);
    assert(Toy.path('/').isMatch());
    var p2 = '/left/binop';
    assertEqual('/left/binop', Toy.path(p2).toString());
    var p3 = '/arg/fn';
    assertEqual(p3 + p3, Toy.path(p3).concat(p3).toString());

    assertEqual('/fn', new Path('fn').toString());
    assertEqual('/left', new Path('left').toString());
    assertEqual('/right', new Path('right').toString());

    var parse = Toy.parse;
    var e = parse('(a + b) + c');
    var path = new Path('left', new Path('left'));
    assertEqual('/left/left', path.toString());
    assertEqual('a', e.get(path));

    var right2 = new Path('right', new Path('right'));
    assertEqual(null, e.get(right2));
  },

  testTraverse: function() {
    var result = [];
    function f(term) {
      result.push(term);
    }
    var x1 = Toy.parse('x + y');
    x1.traverse(f);
    assertEqual(5, result.length);
    assertEqual(x1, result[0]);
    assertEqual(x1.arg, result[1]);
    assertEqual(x1.fn, result[2]);
    assertEqual(x1.fn.arg, result[3]);
    assertEqual(x1.fn.fn, result[4]);

    var result = [];
    var x2 = Toy.parse('g {x. T}');
    x2.traverse(f);
    assertEqual(4, result.length);
    assertEqual(x2, result[0]);
    assertEqual(x2.arg, result[1]);
    assertEqual(x2.arg.body, result[2]);
    assertEqual(x2.fn, result[3]);
  },

  testSearch: function() {
    var xPlusX = call('+', x, x)
    var found =
      times2.search(function(expr) { return xPlusX.matches(expr); });
    assertEqual('(x + x)', found.toString());
  },

  testGet: function() {
    var expr = call('forall', lambda(x, call(p, x)));
    var body = expr.get(Toy.path('/arg/body'));
    assertEqual('(p x)', body.toString());
  },

  testPathTo: function() {
    function findX(expr) {
      return expr == x;
    }
    assertEqual('', '' + x.pathTo(findX));
    assertEqual('/fn', '' + call(x, y).pathTo(findX));
    assertEqual('/arg', '' + call(y, x).pathTo(findX));
    assertEqual('/body', '' + lambda(x, x).pathTo(findX));
    assertEqual('/arg/arg/arg',
                '' + call(f, call(f, call(g, x))).pathTo(findX));
  },

  testPrettyPathTo: function() {
    function finder(target) {
      target = Toy.termify(target);
      return function(expr) {
        return expr.matches(target);
      }
    }
    var pred = finder('x');
    function findPath(term, target) {
      return Toy.termify(term).prettyPathTo(finder(target)).toString();
    }
    assertEqual('/left', findPath('x = y', 'x'));
    assertEqual('/right', findPath('x = y', 'y'));
    assertEqual('/binop', findPath('x = y', '(=)'));
    assertEqual('/right', findPath('T == (T => T)', 'T => T'));
    assertEqual('/left/right', findPath('(x + y) + z', 'y'));
    assertEqual('/arg', findPath('not p', 'p'));
    assertEqual('/fn', findPath('not p', '(not)'))
    assertEqual('/right/arg', findPath('q => not p', 'p'));
    assertEqual('/arg/arg', findPath('not (not (not p))', 'not p'));
  },

  testLeftNeighborPath: function() {
    function leftPath(expr, path) {
      var e = Toy.termify(expr);
      return '' + e.leftNeighborPath(path, ['+', '-']);
    }
    assertEqual('null', leftPath('x + y', '/left'));
    assertEqual('/left', leftPath('x + y', '/right'));
    assertEqual('/left', leftPath('x - y', '/right'));
    assertEqual('null', leftPath('x * y', '/right'));
    assertEqual('null', leftPath('f x', '/arg'));
    assertEqual('/left/right', leftPath('x + y + z', '/right'));
    assertEqual('/left/right', leftPath('x - y + z', '/right'));
    assertEqual('/left/left/right', leftPath('x + y + z + w', '/left/right'));
  },

  testRightNeighborPath: function() {
    function rightPath(expr, path) {
      var e = Toy.termify(expr);
      return '' + e.rightNeighborPath(path, ['+', '-']);
    }
    assertEqual('null', rightPath('x + y', '/right'));
    assertEqual('/right', rightPath('x + y', '/left'));
    assertEqual('/right', rightPath('x - y', '/left'));
    assertEqual('null', rightPath('x * y', '/left'));
    assertEqual('null', rightPath('f x', '/arg'));
    assertEqual('/right', rightPath('x + y + z', '/left/right'));
    assertEqual('/right', rightPath('x - y + z', '/left/right'));
    assertEqual('/left/right', rightPath('x + y + z + w', '/left/left/right'));
  },

  testAncestors: function() {
    var expr = Toy.parse('a + neg (b * c)');
    var path = Toy.path('/right/arg/fn/arg');
    assertEqual('b', expr.get(path));

    var parents = expr.ancestors(path);
    assertEqual(5, parents.length);
    assertEqual('(a + (neg (b * c)))', parents[0]);
    assertEqual('(neg (b * c))', parents[1]);
    assertEqual('(b * c)', parents[2]);
    assertEqual('(b *)', parents[3]);
    assertEqual('b', parents[4]);
  },

  testFindParent: function() {
    var expr = Toy.parse('a + neg (b * c)');
    var path = Toy.path('/right/arg/left');
    assertEqual('b', expr.get(path));

    function test(term) { return term.isCall2('*'); }
    assertEqual('(b * c)', expr.get(expr.findParent(path, test)));
  },

  testNumBindings: function() {
    var nb = Toy.numBindings;
    var Bindings = Toy.Bindings;
    assertEqual(0, nb(null));
    var b = new Bindings('a', true);
    assertEqual(1, nb(b));
    var b2 = new Bindings('b', true, b);
    assertEqual(2, nb(b2));
  },

  testPathToBinding: function() {
    function isX(expr) {
      return expr == x;
    }
    assertEqual(null, x.pathToBinding(isX));
    assertEqual(null, call(x, y).pathToBinding(isX));
    assertEqual('', '' + lambda(x, x).pathToBinding(isX));
    assertEqual('/fn',
                '' + call(lambda(x, x), z).pathToBinding(isX));
  },

  testPrettifyPath: function() {
    var expr = Toy.parse('a + neg (b * c)');
    var p = Toy.path('/arg/arg/fn/arg');
    assertEqual('/right/arg/left', expr.prettifyPath(p).toString());
  },

  testPathExpand: function() {
    var wff = Toy.parse('x + y + z = w');
    var xPath = '/left/left/left';
    var x = wff.get(xPath);
    assertEqual('x', x.name);
    var pp = wff.prettyPathTo(x);
    assertEqual(xPath, pp.toString());
    var p = wff.pathTo(x);
    assertEqual(p.toString(), pp.expand().toString());

    var yPath = '/left/left/right';
    var y = wff.get(yPath);
    assertEqual('y', y.name);
    var pp = wff.prettyPathTo(y);
    assertEqual(yPath, pp.toString());
    var p = wff.pathTo(y);
    assertEqual(p.toString(), pp.expand().toString());

    var eqPath = '/binop';
    var eq = wff.get(eqPath);
    assertEqual('=', eq.name);
    var pp = wff.prettyPathTo(eq);
    assertEqual(eqPath, pp.toString());
    var p = wff.pathTo(eq);
    assertEqual(p.toString(), pp.expand().toString());
  },

  testPathParent: function() {
    var p = Toy.path('/left/right/fn/arg/body');
    var p1 = p.parent();
    assertEqual('/left/right/fn/arg', p1.toString());
    assertEqual('/left/right/fn', p1.parent().toString());
    assertEqual('', Toy.path('/arg').parent().toString());
  },

  testPathUpTo: function() {
    function check(expected, path, tail) {
      assertEqual(expected.toString(),
                  '' + Toy.path(path).upTo(Toy.path(tail)));
    }
    check('/left', '/left', '');
    check('/left/right', '/left/right', '');
    check('/left', '/left/right', '/right');
    check('', '/left/right', '/left/right');
    check('null', '/left', '/right');
    check('null', '/left/right', '/left/right/left');
  },

  testPathLast: function() {
    var p = Toy.path('/left/right/fn/arg/body');
    assertEqual('body', p.last());
    var parent = p.parent();
    assertEqual('arg', parent.last());
    assertEqual(null, Toy.path().last());
  },

  testMatchPattern: function() {
    function check(expected, pattern_arg, term_arg) {
      var term = termify(term_arg);
      var pattern = termify(pattern_arg);
      var subst = term.matchPattern(pattern);
      if (expected) {
        assertEqual(expected, Toy.debugString(subst));
      } else {
        console.log(Toy.debugString(subst));
      }
    }
    check('{p: (x = x)}', p, equal(x, x));
    check('{p: (x < 1), q: (x = 0)}',
          'p => q', 'x < 1 => (x = 0)');
    check('{a: 3, b: 2}', 'a + b', '3 + 2');
    check('{p: {x. (p x)}}', 'exists p', 'exists {x. (p x)}');
    check('null',
          'forall {x. p x}',
          'forall {x. x = 1 => x > 0}');
    check('{p: (q y), x: x}', 'forall {x. p}', 'forall {x. q y}');
    check('{p: (q x), x: x}', 'forall {x. p}', 'forall {x. q x}');
    check('{p: (x >= 0), x: x}', 'forall {x. p}', 'forall {x. x >= 0}');
    check('{p: (x >= 0), y: x}', 'forall {y. p}', 'forall {x. x >= 0}');
    check('null',
          'forall {x. forall {y. p x y}}',
          'forall {x. forall {y. x > y == y < x}}');
  },

  testMatchSchema: function() {
    function check(expected, schema, term, expectedExpansions) {
      term = typeof term == 'string' ? Toy.parse(term) : term;
      schema = typeof schema == 'string' ? Toy.parse(schema) : schema;
      var subst = term.matchSchema(schema);
      if (expected) {
        var expanded = (subst && subst['%expansions']) || '';
        if (expanded) {
          delete subst['%expansions'];
        }
        assertEqual(expectedExpansions || '',
                    Toy.debugString(expanded));
        assertEqual(expected, Toy.debugString(subst));
      } else {
        console.log(Toy.debugString(subst));
      }
    }
    check('{p: (x = x)}', p, equal(x, x));
    check('{p: (x < 1), q: (x = 0)}',
          implies(p, q), Toy.parse('x < 1 => (x = 0)'));
    check('{a: 3, b: 2}', 'a + b', '3 + 2');
    check('{p: {x. (p x)}}', 'exists p', 'exists {x. (p x)}');
    check('{p: {x. ((x = 1) => (x > 0))}}',
          'forall {x. p x}',
          'forall {x. x = 1 => x > 0}',
          '{p: 1}');
    check('{p: (q y)}', 'forall {x. p}', 'forall {x. q y}');
    check('null', 'forall {x. p}', 'forall {x. x >= 0}');
    check('{p: {x. {y. ((x > y) == (y < x))}}}',
          'forall {x. forall {y. p x y}}',
          'forall {x. forall {y. x > y == y < x}}',
          '{p: 2}');
  },

  testLocateFree: function() {
    function str(x) {
      return x.toString();
    }
    var a5 = Toy.rules.axiom5();
    var result = a5.locateFree('x');
    assertEqual([], result.map(str));
    result = a5.locateFree('y');
    assertEqual(["/arg/body/arg/arg/fn", "/arg"],
                result.map(str));

    var a3 = Toy.rules.axiom3();
    var result = a3.locateFree('x');
    assertEqual([], result.map(str));
    result = a3.locateFree('f');
    assertEqual(["/arg/fn/arg/fn",
                 "/fn/arg/fn/body/arg/arg"],
                result.map(str));
    result = a3.locateFree('g');
    assertEqual(["/arg/arg/fn",
                 "/fn/arg/body/arg/arg"],
                result.map(str));
  },

  testAlphaMatch: function() {
    assert(!Toy.parse('neg (x - 1)').alphaMatch('neg a'));
    assert(Toy.parse('neg (x - 1)').alphaMatch('neg (a - 1)'));
    assert(!Toy.parse('neg (x + y)').alphaMatch('neg (a + a)'));
    assert(!Toy.parse('neg (x + x)').alphaMatch('neg (a + b)'));
    assert(Toy.parse('neg (x + y)').alphaMatch('neg (a + b)'));
    assert(Toy.parse('neg (x + y)').alphaMatch('neg (x + y)'));
    assert(Toy.parse('neg (x + y)').alphaMatch('neg (y + x)'));

    var term = Toy.parse('neg (x + y)');
    var term2 = Toy.parse('neg (u + v)');
    var subst = term.alphaMatch(term2);
    var step = Toy.rules.eqSelf(term).andThen('instMultiVars', subst);
    assert(step.getRight().matches(term2));
  },

  testMatchSchemaPart: function() {
    // Given a boolean, a term, a path in the term, a schema, and a
    // schema part, checks that Expr.matchSchemaPart succeeds or fails
    // according to the boolean, and produces a suitable substitution
    // on success.
    function check(expectSuccess, term_arg, path, schema, name) {
      var term = Toy.termify(term_arg);
      var subst = term.matchSchemaPart(path, schema, name);
      if (expectSuccess) {
        if (subst) {
          var path = subst.path;
          delete subst.path;
          assertEqual(term.get(path).toString(),
                      Toy.termify(schema).subFree(subst));
        } else {
          assert(false, 'No match found');
        }
      } else {
        assertEqual(null, subst);
      }
    }
    check(true, '3 * x + z', '/left/right', 'a * b', 'b');
    check(true, '3 * x + z', '/left', 'a + b', 'a');
    check(false, '3 * x + z', '/left', 'a + b', 'b');
    check(true, 'x + y + z = x + (y + z)', '/right/right',
          'a + (b + c)', 'b + c');
  },

  testMatchFactPart: function() {
    var facts = ['a - b = neg b + a', 'a + b + c = a + (b + c)'];
    var step1 = rules.eqSelf('x + y + 10');
    var step2 = rules.eqSelf('x - 5 * y');
    var match = Toy.matchFactPart;
    var pathToY = '/main/right/left/right';
    assertEqual('y', step1.get(pathToY));
    var func = match(step1, pathToY, facts, 'b');
    assertEqual('function', typeof func);
    var result = func();
    assert(result instanceof Toy.Call, 'is an Expr');
    assertEqual('(x + (y + 10))', result.getMain().getRight());
    assertEqual(undefined, match(step2, '/main/right', facts, 'b'));
  },

  testSearchMost: function() {
    var names = [];
    var paths = [];
    var terms = [];
    function foo(term, pth) {
      if (term.fn instanceof Toy.Atom) {
        names.push(term.fn.pname || term.fn.name);
        paths.push(pth.reverse().toString());
      }
      if (term.matchSchema('a + b')) {
        terms.push(term);
      }
    }
    Toy.parse('2 * x + neg y = 12 == T').searchMost(foo);
    assertEqual(["==", "=", "neg", "+", "*"], names);
    assertEqual(["/fn",
                 "/fn/arg/fn",
                 "/fn/arg/fn/arg/arg",
                 "/fn/arg/fn/arg/fn",
                 "/fn/arg/fn/arg/fn/arg/fn"
                 ],
                paths);
    assertEqual(1, terms.length);
    assertEqual('((2 * x) + (neg y))', terms[0].toString());
  },

  testFindMatchingFact: function() {
    var facts = ['a + b = b + a',
                 {match: 'neg a', where: 'subst.a.isNumeral()'}
                 ];

    var result = Toy.findMatchingFact(facts, undefined,
                                       Toy.parse('neg 1'));
    assertEqual('(neg 1)', result.term);
    assertEqual(undefined, result.stmt);

    result = Toy.findMatchingFact(facts, undefined,
                                   Toy.parse('x + y'));
    assertEqual('(x + y)', result.term);
    assertEqual('(((R a) & (R b)) => ((a + b) = (b + a)))', result.stmt);
    assertEqual('y', result.subst.b.toString());

    var context = {factLists:
                   {organize:
                    [{stmt: 'a * b = b * a',
                      where: 'subst.b.isNumeral() && subst.a.isVariable()'},
                     {descend:
                      {schema: 'a * b',
                       parts: {a: 'organize'}}}
                    ]}};
    var info = (Toy.findMatchingFact('organize', context, Toy.parse('x*2*3')));
    assertEqual('(x * 2)', info.term);
  },

  testSearchTerms: function() {
    var searched = [];
    function failer(expr) {
      searched.push(expr.toString());
    }
    var term = Toy.parse('a + b = neg (c + d)');
    assert(!term.searchTerms(failer));
    assertEqual(['((a + b) = (neg (c + d)))',
                 '(neg (c + d))',
                 '(a + b)',
                 'b',
                 'a'],
                searched);
    function finder(expr) {
      return expr.name === 'b' ? 'yo' : false;
    }
    assertEqual('yo', term.searchTerms(finder));
  },

  testGeneralizeTF: function() {
    var gen = Toy.parse('p T = T').generalizeTF(Toy.parse('p F = F'), x);
    assertEqual('((p x) = x)', gen + '');
    try {
      Toy.parse('p T = x').generalizeTF(Toy.parse('p F = F'), x);
      Y.Assert.fail('generalizeTF should have failed');
    } catch(e) {}
    try {
      Toy.parse('p T').generalizeTF(Toy.parse('p T F'), x);
      Y.Assert.fail('generalizeTF should have failed');
    } catch(e) {}
  },

  testHasArgs: function() {
    assert(Toy.parse('f x').hasArgs(1));
    assert(!Toy.parse('f x').hasArgs(2));
    assert(Toy.parse('x + 1').hasArgs(1));
    assert(Toy.parse('x + 1').hasArgs(2));
    assert(!Toy.parse('x + 1').hasArgs(3));
  },

  testHypLocater: function() {
    var rules = Toy.rules;
    function check(expected, step, hyp) {
      hyp = typeof hyp === 'string' ? Toy.parse(hyp) : hyp;
      var actual = step.getLeft().hypLocater(hyp);
      assertEqual(expected, actual);
    }
    var step1 = rules.axiomCommutativePlus();
    check('(h & h1)', step1, 'R x');
    check('(h2 & h)', step1, 'R y');

    var step2 = rules.axiomAssociativePlus();
    check('((h & h2) & h1)', step2, 'R x');
    check('((h3 & h) & h1)', step2, 'R y');
  },

  testHypMover: function() {
    var rules = Toy.rules;
    function check(expected, step, hyp) {
      hyp = typeof hyp === 'string' ? Toy.parse(hyp) : hyp;
      var actual = step.getLeft().hypMover(hyp);
      assertEqual(expected, actual);
    }
    var step1 = rules.axiomAssociativePlus();
    check('(((h & h2) & h3) = ((h2 & h3) & h))',
          step1, 'R x');
    check('(((h1 & h) & h3) = ((h1 & h3) & h))',
          step1, 'R y');
    var h3 = rules.assume('p');
    var step2 = rules.appendStepHyps(step1, h3);
    check('((((h & h2) & h3) & h4) = (((h2 & h3) & h4) & h))',
          step2, 'R x');
    check('((((h1 & h) & h3) & h4) = (((h1 & h3) & h4) & h))',
          step2, 'R y');
  },

  testScanConjuncts: function() {
    function scan(needle, haystack) {
      var x1 = termify(needle);
      var x2 = termify(haystack);
      function test(x) { 
        return x.matches(x1) && x1;
      }
      return x2.scanConjuncts(test);
    }
    assertEqual('(a = b)', scan('a = b', 'T & (a = b)'));
    assertEqual(false, scan('a = b', 'T & (b = c)'));
  },

  testScanDisjuncts: function() {
    function scan(needle, haystack) {
      var x1 = termify(needle);
      var x2 = termify(haystack);
      function test(x) { 
        return x.matches(x1) && x1;
      }
      return x2.scanDisjuncts(test);
    }
    assertEqual('b', scan('b', 'T | a | b'));
    assertEqual(false, scan('a', 'T | (a = b)'));
    assertEqual(false, scan('b', 'T & (b | c)'));
  },

  testAsmLess: function() {
    var step1 = Toy.rules.assume('p T');
    var step2 = Toy.rules.assume('p F');
    // Which step came earlier?
    assert(Toy.asmLess(step1.getLeft(), step2.getLeft()));
    assert(!Toy.asmLess(step2.getLeft(), step1.getLeft()));
  },

  testAsmComparator: function() {
    var compare = Toy.asmComparator;
    var step1 = Toy.rules.assume('p T');
    var l1 = step1.getLeft();
    var step2 = Toy.rules.assume('p F');
    var l2 = step2.getLeft();
    // Which step came earlier?
    assert(compare(l1, l2) < 0);
    assertEqual(0, compare(l1, l1));
    assert(compare(l2, l1) > 0);
    assert(compare(x, l2) < 0);
    assert(compare(l2, x) > 0);
  },

  testConjunctionsMerger: function() {
    var rules = Toy.rules;
    function check(expected, input) {
      var expr = typeof input == 'string' ? Toy.parse(input) : input;
      var actual = rules.conjunctionsMerger(expr).getRight();
      assertEqual(expected, actual);
    }
    check('(x & y)', 'y & x');
    check('(y & z)', 'y & z & z');
    check('((x & y) & z)', 'x & (y & z)');
    check('((p x) & (p y))', 'p x & p y');

    // With sourceSteps:
    var h1 = rules.assert('p x');
    h1.sourceStep = h1;
    var h2 = rules.assert('p y');
    h2.sourceStep = h2;
    var conj = rules.makeConjunction(h1, h2);
    var h3 = rules.assert('p z');
    h3.sourceStep = h3;
    var conj2 = rules.makeConjunction(h2, h3);
    check('((p x) & (p y))', Toy.infixCall(conj, '&', conj));
    check('(((p x) & (p y)) & (p z))', Toy.infixCall(conj, '&', conj2));
    check('(((p x) & (p y)) & (p z))', Toy.infixCall(conj2, '&', conj));
  },

  testRepeatedCall: function() {
    try {
      Toy.repeatedCall('&', []);
      Y.Assert.fail('repeatedCall should throw here');
    } catch(e) {}
    assertEqual('x1', Toy.repeatedCall('&', [1]));
    assertEqual('(x3 & x5)', Toy.repeatedCall('&', [3, 5]));
    assertEqual('((x3 & x5) & x19)',
                Toy.repeatedCall('&', [3, 5, 19]));
  },

  testBoolSchema: function() {
    function check(expected_arg, term) {
      var expected = termify(expected_arg).toString();
      assertEqual(expected, Toy.boolSchema(termify(term)).toString());
    }
    check('(a1 == a2)', 'x = y + 1 == y + 1 = x');
    check('(((a1 => a2) & (a2 => a3)) => (a1 => a3))',
          '(a => b) & (b => c) => (a => c)');
    check('((a1 & a2) => a3)', '(a > b) & (b > c) => (a > c)');
    check('(a1 => (a2 => a1))', 'p => (q => p)');
  },

  testStandardVars: function() {
    function check(expected_arg, term) {
      var expected = termify(expected_arg).toString();
      assertEqual(expected, Toy.standardVars(termify(term)).toString());
    }
    check('((a1 = (a2 + 1)) == ((a2 + 1) = a1))',
          'x = y + 1 == y + 1 = x');
    check('(a1 => (a2 => a1))',
          'p => (q => p)');
    check('(((a1 > a2) & (a2 > a3)) => (a1 > a3))',
          '(a > b) & (b > c) => (a > c)');
    check('((a1 = ({a2. a2} a1)) & ((a3 + 1) = (a1 - 1)))',
          'x = {x. x} x & y + 1 = x - 1');
  },

  // ALIASES

  testAliases: function() {
    var parse = Toy.parse;
    // Printing and parsing should be inverses.
    assertEqual('(a == b)', parse('a == b'));
    // Aliases should not affect meanings of expressions.
    assert(parse('a == b').matches(parse('a = b')));
  },


  // UTILITIES

  testGetNumValue: function() {
    var n = Toy.parse('42');
    assertEqual(42, n.getNumValue());
    try {
      T.getNumValue();
      Y.Assert.fail('Should throw');
    } catch(e) {}
  },

  testCheckRange: function() {
    assertEqual(42, Toy.checkRange(42));
    try {
      Toy.checkRange(-Math.pow(2, 53));
      Y.Assert.Fail('Should throw');
    } catch(e) {}
  },


  // CONSTANTS AND DEFINITIONS

  // Actually "proof support" function:
  testIsConstantName: function() {
    assert(Toy.isConstantName('T'));
    assert(T.isConst());
    assert(Toy.isConstantName('=>'));
    assert(Toy.isConstantName('neg'));
    assert(!equal(x, x).isConst());
  },

  testIsNamedConst: function() {
    var jp = Toy.justParse;
    assert(jp('xx').isNamedConst());
    assert(jp('forall').isNamedConst());
    assert(jp('0').isNamedConst());
    assert(jp('1').isNamedConst());
    assert(!jp('2').isNamedConst());
    assert(!jp('x').isNamedConst());
  },

  testIsDefined: function() {
    assert(!Toy.isDefined('T'));
    assert(!Toy.isDefined(T));
    assert(!Toy.isDefinedSimply('=>'));
    assert(Toy.isDefined('=>'));
    assert(Toy.isDefined('forall'));
    assert(Toy.isDefinedSimply('forall'));
    assert(Toy.isDefined(Toy.constify('forall')));
    try {
      Toy.isDefined(equal(x, x));
      Y.Assert.fail('Name not a variable or string');
    } catch(e) {}
  },

  testIsFunDef: function() {
    const check = Toy.isFunDef;
    assert(!check('T'));
    assert(!check('&'));
    assert(check('neg'));
    assert(!check('posNum'));
  },

  testAlreadyProved: function() {
    assert(Toy._alreadyProved('axiomCommutativePlus'));
    // This one is a rule, but not a theorem.
    assert(!Toy._alreadyProved('rplace'));
  },

  // Also tests rules.eQuantify.
  testDefinex: function() {
    assertEqual('(posNum > 0)', Toy.getDefinition('posNum'));
  },

  // TYPES

  testParseType: function() {
    function check(expected, input) {
      assertEqual(expected, Toy.parseType(input).toString());
    }
    check('i', 'i');
    check('o', 'o');
    check('R', 'R');
    check('t12', 't12');
    check('(o i)', 'o i');
    check('i', '(i)');
    check('((o R) R)', 'o R R');
    check('((o i) i)', '(o i i)');
    check('(o (o i))', 'o (o i)');
  },

  // TYPE INFERENCE

  testFindType: function() {
    var rules = Toy.rules;
    assertEqual('o', Toy.findType(T).toString());
    assertEqual('o', Toy.findType(Toy.parse('x = x')).toString());
    assertFails(function() {
      Toy.findType(Toy.parse('f f'));
      });
    // The identity function, problematic for some algorithms.
    var type = Toy.findType(Toy.parse('{x. x}'));
    assert(type instanceof Toy.FunctionType, 'Not a FunctionType');
    assert(type.types[0] instanceof Toy.TypeVariable, 'Not a TypeVariable');
    assertEqual(type.types[0], type.types[1]);
    assertEqual('o', Toy.findType(rules.axiom1()).toString());
    assertEqual('o', Toy.findType(rules.axiom2()).toString());
    assertEqual('o', Toy.findType(rules.axiom3()).toString());
    assertEqual('o',
                Toy.findType(rules.axiom4(Toy.parse('({x. x} y)'))).toString());
    assertEqual('o', Toy.findType(rules.axiom5()).toString());

    function check(expected, expr) {
      expr = (typeof expr == 'string') ? Toy.parse(expr) : expr;
      var type = Toy.findType(expr);
      // for debugging:
      // Y.log(expected + '/' + type);
      // replace type variables with just "t".
      assertEqual(expected, type.toString().replace(/t[0-9]*/, 't'));
    }
    // Note that all the "> 0" conditions below force variables to
    // be individual variables.
    //
    // From two reals to boolean:
    check('((o i) i)', '{x. {y. x > y & y > 0}}');
    // From set to boolean:
    check('(o (o i))', '{x. x = {y. y > 0}}');
    // From set to individual:
    check('(i (o i))',
          // Max of a set having at least one positive number.
          '{p. iota {x. p x & x > 0 & forall {y. p y => x >= y}}}');
    // From set and individual to boolean, note how the
    // first argument type appears last when written out.
    //         y  x
    check('((o i) (o i))', '{x. {y. (x = ((=) y)) & (y > 0)}}');
    check('((o i) (o i))', '{x. {y. (x = ((>) y)) & (y > 0)}}');
    // Successful typing of the identity function
    check('o', '({x. x} p) = p');

    check('(o o)', 'not');
    check('(o (o t))', '(!=) {x. F}');
    check('(o (o t))', '{x. x != {y. F}}');

    // An example where the type check in Rule R catches improper
    // use of types.
    var step1 = Toy.parse('p (f g) => p g').assert();
    // This is pathological in that p and f each appear on just
    // one side of the equation, which means the value of the
    // expressions containing them are not affected by their
    // values.
    var step2 = Toy.parse('p g = g f').assert();
    try {
      Toy.rules.r(step2, step1, '/right');
      Y.Assert.fail('Rule R should prohibit this step');
    } catch(e) {}
  },


  // RULE DESCRIPTIONS

  testEachArgType: function() {
    var each = Toy.eachArgType;
    info = [];
    each('implyForallGen', function(index, type) {
        info[index] = type;
      });
    assertEqual(info[0], 'varName');
    assertEqual(info[1], 'bool');
    assertEqual(info[2], 'bool');
  },


  // PROOFS

  testRuleR: function() {
    var path = Toy.path('/right/left');
    var result = Toy.rules.r(times2, bigger, path);
    assertEqual('((x > 0) => ((2 * x) > x))', result);
  },

  testAxiom4: function() {
    var app = call(lambda(x, call(f, x)), y);
    var result = Toy.rules.axiom4(app);
    assert(result instanceof Toy.Call);
    assertEqual('=', result.fn.fn.name);
    assertEqual('(({x. (f x)} y) = (f y))', result);
  },

  testAxioms: function() {
    assertEqual('(((g T) & (g F)) == (forall {a. (g a)}))',
                Toy.rules.axiom1());
    assertEqual('((x = y) => ((h x) = (h y)))',
                Toy.rules.axiom2());
    assertEqual('((f = g) == (forall {x. ((f x) = (g x))}))',
                Toy.rules.axiom3());
    assertEqual('((iota {x. (x = y)}) = y)',
                Toy.rules.axiom5());
  },

  testAxiomArithmetic: function() {
    function check(expected, expr) {
      if (typeof expr == 'string') {
        expr = Toy.parse(expr);
      }
      var result = Toy.rules.axiomArithmetic(expr);
      // Y.log(result);
      assertEqual(expected, result);
    }
    var neg5 = Toy.rules.axiomArithmetic(Toy.parse('neg 5')).getRight();
    check('((2 + 2) = 4)', '2 + 2');
    check('((5 * 4) = 20)', '5 * 4');
    check('((5 - 4) = 1)', '5 - 4');
    check('((neg 5) = -5)', 'neg 5');
    check('((5 > 4) = T)', '5 > 4');
    check('((5 >= 4) = T)', '5 >= 4');
    check('((5 < 4) = F)', '5 < 4');
    check('((5 <= 4) = F)', '5 <= 4');
  },

  testAsHypotheses: function() {
    var step1 = Toy.rules.assert('p = p');
    try {
      Toy.rules.asHypotheses(step1);
      Y.Assert.fail('Should throw');
    } catch(e) {}
    var step2 = Toy.rules.assert('p => p');
    var step3 = Toy.rules.assume('p');
    var step4 = Toy.rules.assert('p => q');
    var step5 = Toy.rules.modusPonens(step3, step4);
    var step6 = Toy.rules.asImplication(step5);
    var result = Toy.rules.asHypotheses(step6);
    assertEqual('(p => q)', result);
    assert(result.hasHyps);
  },

  testApplyBoth: function() {
    assertEqual('((f x) = (g x))', Toy.rules.applyBoth(call('=', f, g), x));
  },

  testApplyToBoth: function() {
    var inf = Toy.rules.applyToBoth(p, rules.assert(call('=', q, r)));
    assertEqual('((p q) = (p r))', inf);
    var step = Toy.rules.assume('x = y + 1');
    var result = Toy.rules.applyToBoth(Toy.parse('{x. x - 1}'), step);
    assertEqual('((x - 1) = ((y + 1) - 1))', result.getRight());
  },

  testEqSelf: function() {
    var result = Toy.rules.eqSelf(call(f, y));
    assertEqual('((f y) = (f y))', result);
    assertEqual('(x = x)', Toy.rules.eqSelf(x));
  },

  testEquivSelf: function() {
    var result = rules.equivSelf(call(p, y));
    assertEqual('((p y) == (p y))', result);
    assertEqual('(F == F)', Toy.rules.equivSelf(F));
  },

  testR5201b: function() {
    var inf = Toy.rules.eqnSwap(call('=', p, q));
    assertEqual('(q = p)', inf);
  },

  testR5201c: function() {
    var inf = Toy.rules.eqnChain(call('=', p, q), call('=', q, r));
    assertEqual('(p = r)', inf);
  },

  testR5201d: function() {
    var inf = Toy.rules.applyBySides(call('=', p, q), call('=', 'a', 'b'));
    assertEqual('((p a) = (q b))', inf);
  },

  testR5201e: function() {
    var inf = Toy.rules.applyBoth(call('=', p, q), r);
    assertEqual('((p r) = (q r))', inf);
  },

  testApply: function() {
    var rules = Toy.rules;
    // Apply a call to a lambda.
    var step1 = rules.axiom4('{x. x} 2');
    var result = rules.apply(step1, '/left');
    assertEqual('(2 = 2)', result);
    // Apply a call to 1-arg function:
    var step1 = rules.eqSelf('neg x');
    var result = rules.apply(step1, '/right');
    assertEqual('((neg x) = (-1 * x))', result);
    // Apply a call to a 2-arg function:
    var step1 = rules.assume('x != y');
    var result = rules.apply(step1, '/right');
    assertEqual('((x != y) => (not (x = y)))', result);
  },

  testUseDefinition: function() {
    var inf =
      Toy.rules.useDefinition(call('not', equal(p, equal(F, p))), '/fn');
    assertEqual('(F = (p = (F = p)))', inf);
  },

  testInstEqn: function() {
    var c = Toy.varify('c');
    var inf = Toy.rules.instEqn(Toy.parse('g y = c'),
                              Toy.parse('f x'),
                              'y');
    assertEqual('((g (f x)) = c)', inf);

    var ff = rules.instEqn(rules.axiom3(), 'f', 'g');
    assertEqual('((f = f) = (forall {x. ((f x) = (f x))}))', ff);
  },

  testEqT: function() {
    assertEqual('(T = (b = b))', Toy.rules.eqT('b'));
    var step = Toy.rules.eqT(call(f, x));
    assertEqual('(T = ((f x) = (f x)))', step);
    var controller = new Toy.ProofDisplay();
    // or controller.setSteps(Toy.unrenderedDeps(step));
    controller.addStep(step);
    var step2 = Toy.rules.instVar(step, y, x);
    // Add a step and immediately remove it.  See that at least
    // there are no exceptions.
    controller.addStep(step2);
    controller.removeStepAndFollowing(step2.rendering);
  },

  testR5211: function() {
    assertEqual('((T & T) = T)', Toy.rules.r5211());
  },

  testRuleT: function() {
    assertEqual('T', Toy.rules.t());
  },

  testR5212: function() {
    assertEqual('(T & T)', Toy.rules.r5212());
  },

  testEqnIsTrue: function() {
    var inf = Toy.rules.toTIsEquation(call('=', p, q));
    assertEqual('(T = (p = q))', inf);
  },

  testR5213: function() {
    var inf = Toy.rules.r5213(call('=', p, q),
                            call('=', q, r));
    assertEqual('((p = q) & (q = r))', inf);
  },

  testChangeVar: function() {
    var expr = equal(lambda(z, z), lambda(y, y));
    var result = Toy.rules.changeVar(expr, '/left', x);
    assertEqual('({x. x} = {y. y})', result);
  },

  testBindEqn: function() {
    var inf = Toy.rules.bindEqn(call('=', f, g), x);
    assertEqual('({x. f} = {x. g})', inf);
  },

  testInstForall: function() {
    var result = Toy.rules.instForall(call('forall', lambda(y, call(p, y))),
                                      '',
                                      call(f, y))
    assertEqual('(p (f y))', result);

    // Hypotheses
    var hyps = Toy.rules.assume('p y');
    var step1 = Toy.rules.assert('forall {y. p y}');
    var step2 = Toy.rules.appendStepHyps(step1, hyps);
    var result = Toy.rules.instForall(step2, '/right', call(f, y));
    assertEqual('((p y) => (p (f y)))', result)
    assert(result.hasHyps);
  },

  testR5214: function() {
    var inf = Toy.rules.r5214();
    assertEqual('((T & F) = F)', inf);
  },

  testAndTBook: function() {
    var inf = Toy.rules.andTBook(p);
    assertEqual('((T & p) == p)', inf);
  },

  testAndT: function() {
    var inf = Toy.rules.andT(p);
    assertEqual('((T & p) = p)', inf);
  },

  testR5217Book: function() {
    assertEqual('((T = F) = F)', Toy.rules.r5217Book());
  },

  testEquationCases: function() {
    var inf = Toy.rules.equationCases(equal(T, T), equal(F, F), 'z');
    assertEqual('(z = z)', inf);
  },

  testR5218: function() {
    var inf = Toy.rules.r5218(p);
    assertEqual('((T = p) = p)', inf);
  },

  testToTIsA: function() {
    var inf = Toy.rules.toTIsA(p);
    assertEqual('(T = p)', inf);
    // Hyps
    var step1 = Toy.rules.assume(p);
    var result = Toy.rules.toTIsA(step1);
    assertEqual('(p => (T = p))', result);
  },

  testFromTIsA: function() {
    var inf = rules.fromTIsA(rules.equivSelf('T'));
    assertEqual('T', inf);
    // Assumptions
    var step1 = Toy.rules.assume(p);
    var step2 = Toy.rules.toTIsA(step1);
    var result = Toy.rules.fromTIsA(step2);
    assertEqual('(p => p)', result);
  },

  testReplaceT: function() {
    var actual = rules.replaceT0(rules.tautology('T | p'), '/left',
                                 rules.axiom2());
    assertEqual('(((x = y) => ((h x) = (h y))) | p)', actual);
  },

  testToForall: function() {
    var inf = Toy.rules.toForall(call(p, y), y);
    assertEqual('(forall {y. (p y)})', inf);

    // Hypotheses
    var step1 = Toy.rules.assume(Toy.parse('x = 0'));
    var wff = Toy.rules.assert('x = 0 => y > x').andThen('asHypotheses');
    // wff.getLeft().sourceStep = step1;
    assertEqual('((x = 0) => (forall {y. (y > x)}))',
                Toy.rules.toForall(wff, 'y'));
  },

  testInstVar: function() {
    var result = Toy.rules.instVar(call(p, y), call(f, x), y);
    assertEqual('(p (f x))', result);

    // Hypotheses
    // TODO: Make this really test with hypotheses.
    var step1 = Toy.rules.axiom2();
    result = Toy.rules.instVar(step1, call(p, x), x);
  },

  testInstiateVar: function() {
    var result =
      Toy.rules.instantiateVar(call(p, y), '/arg', call(f, x));
    assertEqual('(p (f x))', result);

    // Hypotheses
    // TODO: Make this really test with hypotheses.
    var step1 = Toy.rules.axiom2();
    result = Toy.rules.instVar(step1, call(p, x), x);
  },

  testInstMultiVars: function() {
    var map = {p: Toy.parse('forall {x. T | b}'),
               q: Toy.parse('forall {x. b}')
    };
    var result = Toy.rules.instMultiVars(implies(p, call('|', T, q)), map);
    assertEqual('((forall {x. (T | b)}) => (T | (forall {x. b})))',
                result);

    // Hypotheses
    // TODO: Make this really test with hypotheses.
    var step = Toy.rules.axiom2();
    var map2 = {x: call(p, x),
                y: call(p, y)};
    var result = Toy.rules.instMultiVars(step, map2);
    assertEqual('(((p x) = (p y)) => ((h (p x)) = (h (p y))))', result);
  },

  testCasesTF: function() {
    var ident = Toy.parse('{x. x}');
    var trueCase = rules.axiom4(call(ident, T));
    var falseCase = rules.axiom4(call(ident, F));
    var result = Toy.rules.casesTF(trueCase,
                                   falseCase,
                                   x);
    assertEqual('(({x. x} x) = x)', result);
  },

  testModusPonens: function() {
    var result = Toy.rules.modusPonens(p, implies(p, q));
    assertEqual('q', result);

    // Hypotheses
    var step1 = Toy.rules.assume('p => not p');
    // A tautology, but don't rely on the tautology rule here.
    var step2 = Toy.rules.assert('(p => not p) => not p');
    result = Toy.rules.modusPonens(step1, step2);
    assertEqual('((p => (not p)) => (not p))', result);
    assert(result.hasHyps);
  },

  testTIsXIsX: function() {
    assertEqual('((T = x) = x)', rules.tIsXIsX());
  },

  testR5230FT_alternate: function() {
    assertEqual('((F = T) = F)', Toy.rules.r5230FT_alternate());
  },

  testR5231T: function() {
    assertEqual('((not T) = F)', Toy.rules.r5231T());
  },

  testR5231F: function() {
    assertEqual('((not F) = T)', Toy.rules.r5231F());
  },

  testFalseEquals: function() {
    assertEqual('((F =) = not)', Toy.rules.falseEquals());
  },

  testTrueEquals: function() {
    assertEqual('((T =) = {x. x})', Toy.rules.trueEquals());
  },

  testEvalBool: function() {
    var inf = Toy.rules.evalBool(call('not', T));
    assertEqual('((not T) = F)', inf);
    inf = Toy.rules.evalBool(call('&', F, T));
    assertEqual('((F & T) = F)', inf);
    inf = Toy.rules.evalBool(Toy.parse('(p (F | T))'));
    assertEqual('((p (F | T)) = (p T))', inf);
    taut = Toy.parse('(p => not p) => not p');
    inf = Toy.rules.evalBool(taut.subFree1(T, p));
    assertEqual('T', inf.getRight());
    inf = Toy.rules.evalBool(taut.subFree1(F, p));
    assertEqual('T', inf.getRight());
  },

  testTautology: function() {
    var wff = T;
    var inf = Toy.rules.tautology(wff);
    assertEqual(wff.toString(), inf);

    var inf = Toy.rules.tautology('x == x');
    assertEqual('(x == x)', inf);

    // TODO: Find a good way to make examples like this work even
    //   though lookup may correctly find a tautology 'x = x' rather
    //   than 'x == x'.
    // var inf = Toy.rules.tautology('x == x');
    // assertEqual('(x == x)', inf);

    var wff = Toy.parse('(p => not p) => not p');
    var inf = Toy.rules.tautology(wff);
    assertEqual(wff.toString(), inf);

    var wff = Toy.parse('(p & q => r) == (p => (q => r))');
    var proved = Toy.rules.tautology(wff);
    assertEqual(wff.toString(), proved);
    var proved = Toy.rules.tautology(wff);
  },

  testMakeConjunction: function() {
    var result = Toy.rules.makeConjunction(p, q);
    assertEqual('(p & q)', result);

    // With hypotheses:
    var step1 = Toy.rules.assume(p);
    var step2 = Toy.rules.assume(q);
    result = Toy.rules.makeConjunction(step1, step2);
    assertEqual('((p & q) => (p & q))', result);
  },

  testTautInst: function() {
    var b = call(p, x);
    var map1 = {
      p: Toy.parse('forall {x. T | p x}'),
      q: Toy.parse('forall {x. p x}')
    };
    var result = Toy.rules.tautInst(Toy.parse('p => T | q'), map1);

    var h_taut = rules.tautology('p => (q => p)');
    var result = Toy.rules.tautInst(h_taut, {p: 'x > 0'});
    assertEqual('((x > 0) => (q => (x > 0)))', result);
  },

  testSourceStepTracking: function() {
    var taut = rules.tautology('p => (h => p)');
    var step1 = rules.assume('forall {y. p y}');
    var step2 = rules.eqSelf('{x. T} (f x)');
    var step3 = rules.tautInst(taut, {p: step2, h: step1.getLeft()});
    var step4 = rules.modusPonens(step2, step3);
    var step5 = rules.asHypotheses(step4);
    Toy._flagHyps(step5, step1);
    assert(step5.hasHyps);
    assert(step5.getLeft().sourceStep);
    Toy.trackSourceSteps = true;
    Toy.trackSourceSteps = false;
  },

  testR5235: function() {
    var inf = Toy.rules.r5235(x, p, call(q, x));
    var wff =
      '((forall {x. (p | (q x))}) => (p | (forall {x. (q x)})))';
    assertEqual(wff, inf);
  },

  testToImplyForall: function() {
    var result = Toy.rules.toImplyForall(x, Toy.parse('p => q x'));
    assertEqual('(p => (forall {x. (q x)}))', result);

    // With hypotheses:
    var step1 = Toy.rules.assert('R y => (p => q x)');
    var step2 = Toy.rules.assume('R y');
    var step3 = Toy.rules.modusPonens(step2, step1);
    result = Toy.rules.toImplyForall(x, step3);
    assertEqual('((R y) => (p => (forall {x. (q x)})))', result);
  },

  testForwardChain: function() {
    var step = (rules.axiom1()
                .andThen('forwardChain', '(a == b) => (a => b)'));
    assertEqual('(((g T) & (g F)) => (forall {a. (g a)}))', step);
    
   var step1 = rules.assert('p x & (p x => q x)');
    var mpTaut = rules.tautology('a & (a => b) => b');
    var inf = rules.forwardChain(step1, mpTaut);
    assertEqual('(q x)', inf);

    var step1 = rules.fact('neg a = 0 - a');
    var step2 = rules.rewrite(step1, '/left/fn', 'f = {x. f x}');
    var step3 = rules.instVar(step2, '5', 'x');
    var step4 = rules.rewrite(step3, '/left/fn', '{x. f x} = f');
    assertEqual('((R a) => ((neg a) = (0 - a)))', step4);
  },

  testBackwardChain: function() {
    expect(0);
    // TODO: Implement me.
  },

  testSubgoal: function() {
    var input = Toy.parse('a & b => c');
    var theorem = rules.tautology('(p == q) => (p => q)');
    var result = rules.subgoal(input, theorem);
    assertEqual('(((a & b) == c) => ((a & b) => c))', result);
  },

  testR5238a: function() {
    var inf = Toy.rules.r5238a(y, call(p, y), call(q, y));
    var wff =
      '(({y. (p y)} = {y. (q y)}) = (forall {y. ((p y) = (q y))}))';
    assertEqual(wff, inf);
  },

  testR5238: function() {
    var result = Toy.rules.r5238(['x', 'y'],
                               Toy.parse('p x'),
                               Toy.parse('p y'));
    var wff =
      ('(({x. {y. (p x)}} = {x. {y. (p y)}}) = '
       + '(forall {x. (forall {y. ((p x) = (p y))})}))');
    assertEqual(wff, result);
  },

  testR5239: function() {
    var inf = Toy.rules.r5239(equal(r, p), '/right', equal(p, q));
    assertEqual('((p = q) => ((r = p) == (r = q)))', inf);

    inf = Toy.rules.r5239(lambda(p, equal(q, p)), '/body/right', equal(p, q));
    var expected =
      '((forall {p. (p = q)}) => ({p. (q = p)} == {p. (q = q)}))';
    assertEqual(expected, inf);

    // Here 'y' is bound in C and free in A = B.
    inf = Toy.rules.r5239(Toy.parse('{y. T}'), '/body',
                          Toy.parse('(T = (y > x))'));
    var expected =
      '((forall {y. (T = (y > x))}) => ({y. T} == {y. (y > x)}))';
    assertEqual(expected, inf);
  },

  testR5239a: function() {
    var result = rules.r5239a(parse('x + y = 5'),
                              Toy.path('/left/left'),
                              parse('x = y + 1'));
    var fml = 'x + y = 5 & x = y + 1 == y + 1 + y = 5 & x = y + 1';
    assertEqual(parse(fml).toString(), result);
  },

  testRplace: function() {
    var rules = Toy.rules;
    var rule = (rules.assert('x > 0 => (x = (abs x))')
                .andThen('asHypotheses'));
    var target = (rules.assert('x > 0 => ((x + x) > x)')
                  .andThen('asHypotheses'));
    var result = rules.rplace(rule, target, '/right/right');
    assertEqual('((x > 0) => ((x + x) > (abs x)))', result);
  },

  testRemoveLet: function() {
    var given = rules.given('x + 2 = 5');
    var added = rules.andAssume(given, 'y = 8');
    var removed = rules.removeLet(added, '/left');
    assertEqual(given.toString(), removed);

    var given = (rules.given('x + 2 = 5')
                 .andThen('rewriteOnly', '/right/left', 'x + y = y + x'));
    var added = rules.andAssume(given, 'y = 8');
    var p = added.wff.pathTo(termify('y = 8'));
    var removed = rules.removeLet(added, p);
    assert(removed.wff.matchSchema('R v => (a == b)'));
  },

  testRemoveTypeAsm: function() {
    var given = rules.given('x + 2 = 5');
    var added = rules.andAssume(given, 'R y');
    var removed = rules.removeTypeAsm(added, '/left');
    assertEqual(given.toString(), removed);

    var given = (rules.given('x + 2 = 5')
                 .andThen('rewriteOnly', '/right/left', 'x + y = y + x'));
    var added = rules.andAssume(given, 'R y');
    var p = added.wff.pathTo(termify('R y'));
    var removed = rules.removeTypeAsm(added, p);
    assert(removed.wff.matchSchema('R v => (a == b)'));
  },

  // This tests beta-expansion of "p x" during matching, and automatic
  // beta reduction before replacement in rewriting.
  testRewriteExpansion: function() {
    var step = (rules.fact('p x => exists p')
                .andThen('instVar', '{x. x > 0}', 'p')
                .andThen('simpleApply', '/left')
                .andThen('toForall0', 'x'));
    var result = rules.rewriteOnly(step, '', 'existImplies');
    assertEqual('((exists {x. (x > 0)}) => (exists {x. (x > 0)}))',
                result);
  },

  testDeepTermReplacer: function() {
    // Leverages the code for testConjunctsSimplifier.
    // 
    // First a no-op transformation.
    var taut = rules.tautology('a | not a == T');
    assertEqual('(((a & b) & c) = ((a & b) & c))',
                rules.deepTermReplacer(Toy.parse('a & b & c'),
                                       [taut]));
    // A simple transformation
    var expected =
      '(((((x | (not x)) & (y | (not y))) & z) & w) = (((T & T) & z) & w))';
    var term = Toy.parse('(x | not x) & (y | not y) & z & w');
    assertEqual(expected,
                rules.deepTermReplacer(term,
                                       [taut]));
    // Transformation, with transform of the results of
    // transforming the subexpressions.
    expected =
      '(((((x | (not x)) & (y | (not y))) & z) & w) = (((T & T) & z) & w))';
    var taut2 = rules.tautology('T & T == T');
    assertEqual(expected,
                rules.deepTermReplacer(term,
                                       [taut2, taut]));
    var expected =
      '(((R x) & (R y)) => (((x * y) != 0) = ((x != 0) & (y != 0))))'
    assertEqual(expected,
                rules.deepTermReplacer(Toy.parse('x * y != 0'),
                                       [rules.factNonzeroProduct()]));
  },

  testRewriteInDepth: function() {
    expect(0);
    // TODO: implement me.
  },

  testConjunctsSimplifier: function() {
    // First a no-op transformation.
    var taut = rules.tautology('a | not a == T');
    assertEqual('(((a & b) & c) = ((a & b) & c))',
                rules.conjunctsSimplifier(Toy.parse('a & b & c'),
                                          [taut]));
    // A simple transformation
    var expected =
      '(((((x | (not x)) & (y | (not y))) & z) & w) = (((T & T) & z) & w))';
    var term = Toy.parse('(x | not x) & (y | not y) & z & w');
    assertEqual(expected,
                rules.conjunctsSimplifier(term,
                                          [taut]));
    // Transformation, with transform of the results of
    // transforming the subexpressions.
    expected =
      '(((((x | (not x)) & (y | (not y))) & z) & w) = ((T & z) & w))';
    var taut2 = rules.tautology('T & T == T');
    assertEqual(expected,
                rules.conjunctsSimplifier(term,
                                          [taut, taut2]));
    var expected =
      '(((R x) & (R y)) => (((x * y) != 0) = ((x != 0) & (y != 0))))'
    assertEqual(expected,
                rules.conjunctsSimplifier(Toy.parse('x * y != 0'),
                                          [rules.factNonzeroProduct()]));
  },

  testBubbleLeft: function() {
    function less(a, b) {
      return a.toString() < b.toString();
    }
    function bubble(string) {
      return Toy.rules.bubbleLeft(Toy.parse(string), less);
    }
    var result = bubble('a & b');
    assertEqual('(a & b)', result.getRight());
    var result = bubble('b & a');
    assertEqual('((b & a) = (a & b))', result);

    result = bubble('a & b & c');
    assertEqual('((a & b) & c)', result.getRight());
    result = bubble('a & c & b');
    assertEqual('((a & b) & c)', result.getRight());
    result = bubble('b & c & a');
    assertEqual('((a & b) & c)', result.getRight());

    result = bubble('b & c & d & a');
    assertEqual('(((a & b) & c) & d)', result.getRight());
    result = bubble('a & c & d & b');
    assertEqual('(((a & b) & c) & d)', result.getRight());

    // With simplification.
    var result = bubble('a & a');
    assertEqual('a', result.getRight());
    var result = bubble('a & b & b');
    assertEqual('(a & b)', result.getRight());
    result = bubble('a & c & d & a');
    assertEqual('((a & c) & d)', result.getRight());
    result = bubble('b & a & d & a');
    assertEqual('((a & b) & d)', result.getRight());
  },

  testMergeRight: function() {
    var result = Toy.rules.mergeRight(Toy.parse('l == (a & b) & (c & d)'));
    assertEqual('(l == (a & ((c & d) & b)))', result);
    var result = Toy.rules.mergeRight(Toy.parse('l == a & (b & c & d)'));
    assertEqual('(l == (((b & c) & d) & a))', result);
  },

  testMergeConj: function() {
    function less(a, b) {
      return a.toString() < b.toString();
    }
    function merge(string) {
      return Toy.rules.mergeConj(Toy.rules.assert(string), less).getRight();
    }
    var result = merge('(a & b) & (c & d)');
    assertEqual('(((a & b) & c) & d)', result);
    var result = merge('a & (c & d)');
    assertEqual('((a & c) & d)', result);
    var result = merge('(a & b & c) & (a & b & c)');
    assertEqual('((a & b) & c)', result);
    var result = merge('(b & b & a) & (a & b & c)');
    assertEqual('((a & b) & c)', result);
  },

  testExtractHypothesis2: function() {
    var rules = Toy.rules;
    var step = rules.axiomCommutativePlus();
    var expected =
      '(((R x) & (R y)) => ((R x) => ((x + y) = (y + x))))';
    var result = rules.extractHypothesis2(step, Toy.parse('R x'));
    assertEqual(expected, result);
    expected =
      '(((R x) & (R y)) => ((R y) => ((x + y) = (y + x))))';
    result = rules.extractHypothesis2(step, Toy.parse('R y'));
    assertEqual(expected, result);
  },

  testIsolateHypAt: function() {
    var step = rules.axiomCommutativePlus();
    var actual = rules.extractHypAt(step, '/left/left');
    assertEqual('((R y) => ((R x) => ((x + y) = (y + x))))', actual);
  },

  testIsolateHyp: function() {
    var step = rules.axiomCommutativePlus();
    var actual = rules.extractHyp(step, 'R x');
    assertEqual('((R y) => ((R x) => ((x + y) = (y + x))))', actual);
  },

  testConjunctionDeduper: function() {
    function rule(term) {
      return rules.conjunctionArranger(term, Toy.asmComparator);
    }
    checkRewriter('((R x) & (R y))', '(R y) & (R x)', rule);
    checkRewriter('(R x)', '(R x) & (R x)', rule);
    checkRewriter('(R x)', 'R x & T', rule);
    checkRewriter('((R x) & (R y))', 'R x & R y & R x', rule);
    checkRewriter('((R x) & (R y))',
                  '(R x) & (R y) & T & R y & R x', rule);
  },

  testConjunctsImplyConjunct: function() {
    var rule = rules.conjunctsImplyConjunct;
    function check(conjuncts, conjunct) {
      conjuncts =
        typeof conjuncts == 'string' ? Toy.parse(conjuncts) : conjuncts;
      conjunct =
        typeof conjunct == 'string' ? Toy.parse(conjunct) : conjunct;
      // Y.log(rule(conjuncts, conjunct));
      var result = rule(conjuncts, conjunct);
      assertEqual(Toy.infixCall(conjuncts, '=>', conjunct) + '',
                  result);
    }
    check('a', 'a');
    check('a & b', 'b');
    check('a & b', 'a');
    check('a & b & c', 'b');
    check('(R x) & (R y)', '(R x)');
  },

  testArrangeAsms: function() {
    expect(0);
    // TODO: Implement.
  },

  testEqualConjunctions: function() {
    var input = Toy.parse('R x & T == T & R x');
    var proved = rules.equalConjunctions(input);
    assert(proved.matches(input));
    input = Toy.parse('R x == R x & R x');
    proved = rules.equalConjunctions(input);
    assert(proved.matches(input));
    input = Toy.parse('R x & R x & R (x + y) == R (x + y) & R x');
    proved = rules.equalConjunctions(input);
    assert(proved.matches(input));
  },

  testArithmetic: function() {
    var input = rules.assume('x = 2 + 2');
    var result = rules.arithmetic(input, '/right/right');
    assertEqual('(x = 4)', result.getRight());
    input = rules.assume('T == 2 != 0');
    // Apply arithmetic to the "2 != 0" part of the instantiated axiom.
    var location = '/left/right';
    var result = rules.arithmetic(input, location);
    assertEqual('T', result.get(location));
  },

  testSimplifyStep: function() {
    var step1 = rules.consider('2 * 3 * x');
    var step2 = rules.simplifyStep(step1);
    assertEqual('(6 * x)', step2.get('/main/right'));
  },

  testOperateOnBoth: function() {
    var eqn = rules.eqSelf(x);
    var x5 = Toy.parse('x + 5');
    assertEqual('((R x) => ((x + (x + 5)) = (x + (x + 5))))',
                rules.addToBoth(eqn, '', x5));
    assertEqual('((R x) => ((x - (x + 5)) = (x - (x + 5))))',
                rules.subtractFromBoth(eqn, '', x5));
    assertEqual('((((x + 5) != 0) & (R x)) => ((x * (x + 5)) = (x * (x + 5))))',
                rules.multiplyBoth(eqn, '', x5));
    assertEqual('((((x + 5) != 0) & (R x)) => ((x / (x + 5)) = (x / (x + 5))))',
                rules.divideBoth(eqn, '', x5));
  },

  testConsider: function() {
    function check(expected, input) {
      input = typeof input == 'string' ? Toy.parse(input) : input;
      var actual = rules.consider(input);
      assertEqual(expected, actual + '');
    }
    check('(x = x)', 'x');
    check('((x + y) = (x + y))', 'x + y');
  },

  testFlattenTerm: function() {
    function check(expected, input) {
      var step = rules.consider(input);
      var right = Toy.path('/main/right');
      var result = rules.flattenTerm(step, right);
      assertEqual(expected, result.getMain().getRight());
    }

    check('((x * 2) * 3)', 'x * (2 * 3)');
    check('((2 / 4) / 3)', '2 / (4 * 3)');
    check('((2 / 3) / 4)', '2 / 3 / 4');
    check('((x / -1) / x)', 'x / (neg x)');
  },

  testIsDistribFact: function() {
    assert(true, Toy.isDistribFact('a * (b + c) = a * b + a *c'));
    assert(!Toy.isDistribFact('a + (b + c) = a + b + c'));
  },

  testTransformApplyInvert: function() {
    var ai = Toy.transformApplyInvert;
    var result = ai('a / b / c',
                    'a / b = a * recip b',
                    'a * b * c = a * c * b');
    assertEqual('(((a / b) / c) = ((a / c) / b))', result.getRight());
  },

  // Utility functions for proofs.

  testTermGetRightVariable: function() {
    function getRight(term) {
      return Toy.termGetRightVariable(Toy.termify(term));
    }
    assertEqual('x', getRight('x'));
    assertEqual(null, getRight('2'));
    assertEqual(null, getRight('T'));
    assertEqual('z', getRight('neg z'));
    assertEqual('y', getRight('x * y'));
    assertEqual('v', getRight('2 * v'));
  },

  testVarFactorCounts: function() {
    // Note that varFactorCounts exercises Expr.walkPatterns.
    function check(expected, term) {
      deepEqual(Toy.varFactorCounts(Toy.parse(term)), expected);
    }
    check({x: 1}, 'x');
    check({}, '2');
    check({x: 1}, 'x * 2');
    check({x: 2, y: 1}, 'x * y * x * 5');
    check(null, 'z + 1');
    check(null, 'x * (y + 1)');
    check({x: 2}, 'x * neg x');
  },

  testTermLeftThan: function() {
    function left(a, b) {
      return Toy.termLeftThan(Toy.termify(a), Toy.termify(b));
    }
    assert(left('x', '2'));
    assert(!left('x', 'x * 2'));
    assert(!left('x + 1', '2'));
    assert(left('x * 2 * x', '3 * x'));
    assert(left('x * y', 'y'));
    assert(left('x * y', 'y * y * y'));
    assert(!left('2', 'x'));
  },

  testBuildHypSchema: function() {
    var rules = Toy.rules;
    var bs = Toy._buildHypSchema;
    var map = new Toy.TermMap();
    var schema = bs(rules.axiomAssociativePlus().getLeft(), map);
    assertEqual('((a1 & a2) & a3)', schema);
    assertEqual('a3', map.get(Toy.parse('R z')));
  },

  testPathToConjunct: function() {
    function compute(x, f) {
      return Toy._pathToConjunct(termify(x), f) + '';
    }
    assertEqual('/left/left', compute('a & b & c', e => e.name == 'a'));
  },

  testConjunctionSchema: function() {
    var result = Toy._conjunctionSchema(Toy.parse('2<3 & (3<4 & (b => c))')).$$
    assertEqual('(a1 & (a2 & a3))', result);
    assertEqual('a1', Toy._conjunctionSchema(Toy.parse('a => b')).$$);
  },

  testEQuantify: function() {
    var result = rules.fact('1 > 0').andThen('eQuantify', '/left');
    assertEqual('(exists {x. (x > 0)})', result);
  },

  // END OF RULES AND THEOREMS

  // ProofEditor - solution status

  testEqnStatus: function() {
    var givenVars = {
      x: true,
      y: true
    }
    function status(eqn) {
      return Toy._eqnStatus(termify(eqn), givenVars);
    }
    assertEqual(null, status('R x'));
    assertEqual({}, status('x = 5'));
    assertEqual({}, status('y = 5'));
    assertEqual(null, status('z = 5'));
    assertEqual(null, status('x = 5 * z'));
    assertEqual({y: true}, status('x = 5 + y'));
    assertEqual(null, status('x = 5 + y - x'));
    assertEqual({x: true}, status('y = 5 - x'));
  },

  testAnalyzeConditions: function() {
    var analyze = Toy._analyzeConditions;
    var TermSet = Toy.TermSet;
    function ts(a) {
      var set = new TermSet();
      a.forEach(x => set.add(x));
      return set;
    }
    var gg = ['R x', 'x + y = 5', 'x - y = 3'].map(parse);
    var problemGivens = ts(gg);
    function check(expected, expr) {
      var result = qUnitCopy(analyze(expr, problemGivens));
      deepEqual(result, qUnitCopy(expected), 'Woot?');
    }
    var expr = parse('R x & x + y = 5 & x > 3');
    var expect = {};
    expect.tcs = ts([gg[0]]);
    expect.givens = ts([gg[1]]);
    expect.others = ts([parse('x > 3')]);
    check(expect, expr);
  },

  testAnalyzeSolutions: function() {
    var analyze = Toy._analyzeSolutions;
    var givenVars = {x: true, y: true, z: true};
    var disj = parse('x = 1 / y');
    var result = analyze(disj, givenVars);
    var actual = qUnitCopy(result);
    var expected = [{
        byVar: {
          x: {
            eqn: 'Expr (x = (1 ∕ y))',
            swapped: false,
            using: {
              y: true
            }
          }
        },
        eqns: ['Expr (x = (1 ∕ y))'],
        others: [],
        overages: {},
        tcs: []
      }
      ];
    deepEqual(actual, expected);

    disj = parse('x = 3 & x = 5 & y > z');
    result = analyze(disj, givenVars);
    expected = [{
        byVar: {},
        eqns: ['Expr (x = 3)', 'Expr (x = 5)'],
        others: ['(y > z)'],
        overages: {x: true},
        tcs: []
      }
      ];
    deepEqual(qUnitCopy(result), expected);
  },

  testProofStatusInfo: function() {
    var ed = new Toy.ProofEditor();
    ed.givens = ['x + y = 5', 'x - y = 3'];
    var formulas = {
      a: 'x + y = 5 & x - y = 3 == x = y - 5 & x - y = 3',
      b: 'x = 3 & x = 5 == x = 3 & x = 5'
    };
    var step = rules.assert(formulas.a);
    ed.addStep(step);
    var stats = ed.statusInfo(step);
    var expected = {
      structure: "equiv",
      tcInfo: null,
      givensInfo: {
        tcs: [],
        givens: ["((x + y) = 5)", "((x − y) = 3)"],
        others: []
      },
      solutionsInfo: [{
          byVar: {
            x: {
              eqn: "Expr (x = (y − 5))",
              swapped: false,
              using: {
                y: true
              }
            }
          },
          eqns: ['Expr (x = (y − 5))'],
          overages: {},
          tcs: [],
          others: ["((x − y) = 3)"]
        }
        ]
    };
    deepEqual(qUnitCopy(stats), expected);

    var step2 = rules.assert(formulas.b);
    ed.addStep(step2);
    var stats2 = ed.statusInfo(step2);
    var expected2 = {
      structure: 'equiv',
      tcInfo: null,
      givensInfo: {
        tcs: [],
        givens: [],
        others: ['(x = 3)', '(x = 5)']
      },
      solutionsInfo: [{
          byVar: {},
          eqns: ['Expr (x = 3)', 'Expr (x = 5)'],
          overages: {x: true},
          tcs: [],
          others: []
        }
        ]
    };
    deepEqual(qUnitCopy(stats2), expected2);
  },

  testSolutionStatus: function() {
    var ed = new Toy.ProofEditor();
    ed.givens = ['x + y = 5', 'x - y = 3'];
    var formulas = {
      a: 'x + y = 5 & x - y = 3 == x = y - 5 & x - y = 3',
      b: 'x + y = 5 & x - y = 3 == x = 4 & x - y = 3',
      c: 'x = 3 & y = 5 == x = 3 & y = 5'
    };
    var step = rules.assert(formulas.a);
    ed.addStep(step);
    var stats = ed.solutionStatus(step);
    var expected = {
      type: "equiv",
      extras: [],
      solutions: [{
          byVar: {
            x: {
              eqn: 'Expr (x = (y − 5))',
              swapped: false,
              using: {y: true}
            }
          },
          eqns: ['Expr (x = (y − 5))'],
          overages: {},
          tcs: [],
          others: ['((x − y) = 3)']
        }],
      absentGivens: []
    };
    deepEqual(qUnitCopy(stats), expected);

    step  = rules.assert(formulas.b);
    stats = ed.solutionStatus(step);
    expected = {
      type: "equiv",
      extras: [],
      solutions: [{
          byVar: {
            x: {
              eqn: "Expr (x = 4)",
              swapped: false,
              using: {}
            }
          },
          eqns: ['Expr (x = 4)'],
          overages: {},
          tcs: [],
          others: ["((x − y) = 3)"]
        }],
      absentGivens: []
    };
    deepEqual(qUnitCopy(stats), expected);

    ed = new Toy.ProofEditor();
    ed.givens = ['x = 3', 'y = 5'];
    step = rules.assert(formulas.c);
    // This time don't even add the step to the proof.
    stats = ed.solutionStatus(step);
    expected = {
      type: "equiv",
      extras: [],
      solutions: [{
          byVar: {
            x: {
              eqn: "Expr (x = 3)",
              swapped: false,
              using: {}
            },
            y: {
              eqn: "Expr (y = 5)",
              swapped: false,
              using: {}
            }
          },
          eqns: ['Expr (x = 3)', 'Expr (y = 5)'],
          overages: {},
          tcs: [],
          others: []
        }],
      absentGivens: []
    };
    deepEqual(qUnitCopy(stats), expected);

    ed = new Toy.ProofEditor();
    ed.givens = ['x - 3 = 2'];
    step = rules.assert('x = 5 => x - 3 = 2');
    stats = ed.solutionStatus(step);
    expected = {
      type: "confirmation",
      givens: ["((x − 3) = 2)"],
      solution: {
        x: {
          eqn: "Expr (x = 5)",
          swapped: false,
          using: {}
        }
      }
    };
    deepEqual(qUnitCopy(stats), expected);

    // Simultaneous linear equations:
    ed = new Toy.ProofEditor();
    ed.givens = ['x = y + 3', 'x + y = 7'];
    var wff = 'x = y + 3 & R y => (x + y = 7 == y = 2)';
    step = rules.assert(wff);
    stats = ed.solutionStatus(step);
    expected = {
      absentGivens: [],
      extras: [],
      solutions: [{
          byVar: {
            y: {
              eqn: 'Expr (y = 2)',
              swapped: false,
              using: {}
            }
          },
          eqns: [
                   'Expr (y = 2)'
                   ],
          others: [],
          overages: {},
          tcs: []
        }
        ],
      type: 'equiv'
    };
    deepEqual(qUnitCopy(stats), expected);
  },

  testReplaceConjunct: function() {
    var step = rules.given('x + y = 5 & x = y + 3');
    var result = rules.replaceConjunct(step, Toy.path('/right/left/left/left'));
    var expect = ('((((x + y) = 5) & (x = (y + 3))) == ' +
                  '((((y + 3) + y) = 5) & (x = (y + 3))))');
    assertEqual(expect, result)
    step = rules.given('x = y + 3 & x + y = 5');
    result = rules.replaceConjunct(step, Toy.path('/right/right/left/left'));
    expect = ('(((x = (y + 3)) & ((x + y) = 5)) == ' +
              '((x = (y + 3)) & (((y + 3) + y) = 5)))');
    assertEqual(expect, result);
  },

  // Looking at what can be done with Andrews' definition of "and".
  // From here you can get counterexamples to the possibilities
  // that ordered pairs other than TT satisfy the definition.
  testFunWithAnd: function() {
    expect(0);
    var result = Toy.rules.funWithAnd();
  },

  // Tell the profiler we are done profiling the tests.
  testDoneTesting: function() {
    expect(0);
    console.profileEnd();
    // console.log('Profiling session ended.');
  }

};

Toy.testCase = testCase;

//// RUN TESTS

// Run tests "soon", but after the event system returns to idle,
// allowing Prooftoys initializations to complete.  In jQuery 3.1.1
// the initializations seem to run only after the event loop has
// returned to idle, at least when running tests.
window.setTimeout(function() {

  // Set this to an array of theorem names, test case names, and fact
  // statements to be specifically tested.  Fact statements usually
  // will be strings here.
  // A null value means "test all".
  var toTest = null;
  // An array of test keys runs all tests.
  // toTest = ['testConjunctsImplyConjunct'];

  // Runs the named test case or warns if there is none such.
  function doTestCase(name) {
    var fn = testCase[name];
    if (typeof fn === 'function') {
      // It would be nice to log the name of each test here, but
      // running "test" only queues the test.
      runTest(name, fn);
    } else {
      console.warn(name + ': not a function');
    }
  }
  if (toTest) {
    toTest.forEach(function(name) {
        if (testCase[name]) {
          doTestCase(name);
        }
      });
  } else {
    for (var name in testCase) {
      doTestCase(name);
    }
  }
  var rules = Toy.rules;
  var nTheorems = 0;
  // Set up an object/map of rules to test; the elements of toTest
  // that name rules, if toTest is an array, otherwise all rules.
  var ruleTests = {};
  if (toTest) {
    toTest.forEach(function(name) {
        if (name in rules) {
          ruleTests[name] = true;
        }
      });
  } else {
    ruleTests = rules;
  }
  for (var name in ruleTests) {
    var prover = rules[name];
    // Prover is a function and its length is its number of args.
    if (prover.length == 0) {
      runTest(name, function(prover, name) {
          var result = prover();
          var stmt = prover.info.statement;
          // Check that the statement of the theorem matches
          // what was proved.
          if (stmt) {
            // TODO: Use rules.equalConjunctions to compare goal
            //   assumptions with assumptions in proved results.
            assert(stmt.matches(result),
                   'For ' + name +
                   '\nexpected: ' + stmt +
                   '\ngot: ' + result);
          } else {
            // This lets most theorems pass if they do not have
            // a statement.
            // TODO: Consider requiring a statement for every theorem.
            assert(result, 'Proof of ' + name + ' failed.');
            if (result) {
              console.warn('No statement for', name, '- proved', result.$$);
            } else {
              Toy.fail('Proof of ' + name + ' failed.');
            }
          }
        }.bind(null, prover, name));
      nTheorems++;
    }
  }
  console.log('Queued', nTheorems, 'theorems to test.');
  // Tests one fact given its fact info.
  function testFact(info) {
      runTest(info.synopsis, function() {
          assert(Toy.getResult(info.goal).ruleName);
        });
      nFacts++;
  }
  var nFacts = 0;
  if (toTest) {
    toTest.forEach(function(key) {
        if (!Toy.isIdentifier(key)) {
          var info = Toy.lookupFactInfo(key);
          if (info) {
            testFact(info);
          }
        }
      });
  } else {
    Toy.eachFact(testFact);
  }
  console.log('Queued', nFacts, 'facts to test.');
  runTest('End of tests', function() {
      assert(true, 'End of tests at ' + new Date());
      console.log('End of test run at ', new Date());
    });
  // When the next lines run, the tests run with profiling.
  // console.log('Running tests with profiling');
  // console.profile('Tests');
  // If the delay is much longer the web page display will initially
  // show a very short run with no tests, then correct itself later.
  }, 10);

})();
