
var parse = Toy.parse;

var tests = {

  hello: function(a) {
    a.ok(true) ;
  },

  atoms: function(a) {
    a.equal(parse('x').str, 'x');
    a.equal(parse('(x)').str, 'x');
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
