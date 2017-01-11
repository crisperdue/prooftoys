
var parse = Toy.parse;

// Note that there are more parser tests in the main tests file.
// TODO: Consider moving them here.
var tests = {

  hello: function(a) {
    a.ok(true) ;
  },

  atoms: function(a) {
    a.equal(parse('x').toString(), 'x');
    a.equal(parse('(x)').toString(), 'x');
  },

  infix: function(a) {
    a.equal(parse('a + b').toString(), '(a + b)');
    a.equal(parse('(a + b)').toString(), '(a + b)');
    a.equal(parse('a + b = b + a').toString(), '((a + b) = (b + a))');
  },

  unary: function(a) {
    a.equal(parse('neg neg a = a').toString(), '((neg (neg a)) = a)');
    a.equal(parse('-x = -1 * x').toString(), '((neg x) = (-1 * x))');
  },

  specials: function(a) {
    a.equal(parse('(not) = ((=) F)').dump(), '((= not) (= F))');
  }

};

for (var name in tests) {
  var fn = tests[name];
  if (typeof fn === 'function') {
    QUnit.test(name, fn);
  } else {
    console.log(name + ': not a function');
  }
}
