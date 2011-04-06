// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

//// Rules (public)

// Map from inference rule name to a JavaScript procedure that
// implements it.
var ruleFns = {

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R.  The subexpression must match
   * the equation's LHS.
   */
  r: function(equation, target, path) {
    if (typeof path == 'string') {
      path = Y.path(path);
    }
    if (equation.isCall2('=')) {
      function replacer(expr) {
        if (expr.matches(equation.getLeft())) {
          return equation.getRight();
        } else {
          assert(false, 'Rule R: subexpression ' + expr +
                        '\n of ' + target +
                        '\n must match ' + equation.getLeft());
        }
      }
      var result = target.replace(path, replacer);
      return result;
    } else {
      throw new Error('Must be an equation: ' + equation);
    }
  },

  axiom1: function() {
    return call('=', call('&&', call(g, T), call(g, F)),
                call('forall', lambda(x, call(g, x))));
  },

  // (--> (= x y) (= (h x) (h y)))
  axiom2: function() {
    return call('-->', call('=', x, y), call('=', call(h, x), call(h, y)));
  },

  // (= (= f g) (= {x : (= (f x) (g x))} {x : T}))
  axiom3: function() {
    return call('=', call('=', f, g),
                call('=', lambda(x, call('=', call(f, x), call(g, x))),
                     lambda(x, T)));
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: function(app) {
    if (app instanceof Y.Call && app.fn instanceof Y.Lambda) {
      var lambdaExpr = app.fn;
      return call('=', app,
                  Y.subFree(app.arg, lambdaExpr.bound, lambdaExpr.body));
    } else {
      throw new Error('Axiom 4 needs ({X : B} A), got: ' + app.toString());
    }
  },

  axiom5: function() {
    return call('=', call('the', call('=', y)), y);
  },

  // Takes an arbitrary expression A, concluding that it is equal
  // to itself.
  r5200: function(a) {
    var step1 = rules.axiom4(call(lambda(x, x), a));
    return rules.r(step1, step1, Y.path('/left'));
  },

  r5201a: function(a, ab) {
    var aa = rules.r5200(a);
    var b = ab.getRight();
    var result = rules.r(ab, a, '/');
    return result;
  },

  r5201b: function(ab) {
    var a = ab.getLeft();
    var aa = rules.r5200(a);
    var ba = rules.r(ab, aa, '/left');
    return ba;
  },

  r5201c: function(ab, bc) {
    var ac = rules.r(bc, ab, '/right');
    return ac;
  },

  r5201d: function(ab, cd) {
    var a = ab.getLeft();
    var b = ab.getRight();
    var c = cd.getLeft();
    var d = cd.getRight();
    var ac = call(a, c);
    var acac = rules.r5200(ac);
    var acbc = rules.r(ab, acac, '/right/fn');
    var acbd = rules.r(cd, acbc, '/right/arg');
    return acbd;
  },

  r5201e: function(ab, c) {
    var a = ab.getLeft();
    var b = ab.getRight();
    var ac = call(a, c);
    var acac = rules.r5200(ac);
    var acbc = rules.r(ab, acac, '/right/fn');
    return acbc;
  },

  r5201f: function(bc, a) {
    var abab = rules.r5200(call(a, bc.getLeft()));
    var abac = rules.r(bc, abab, '/right/arg');
    return(abac);
  },

  /**
   * Substitutes term "a" for variable "v" in equation b_c,
   * with the result a consequence of b_c.
   */
  r5209: function(b_c, a, v) {
    var b = b_c.getLeft();
    var c = b_c.getRight();
    var ba_ba = rules.r5200(call(lambda(v, b), a));
    var ba_ca = rules.r(b_c, ba_ba, '/right/fn/body');
    var ba_sab = rules.axiom4(call(lambda(v, b), a));
    var ca_sac = rules.axiom4(call(lambda(v, c), a));
    var step5a = rules.r(ba_sab, ba_ca, '/left');
    var step5b = rules.r(ca_sac, step5a, '/right');
    return step5b;
  },

  // thm: T = [B = B]
  r5210: function(b) {
    var a3 = rules.axiom3();
    var identity = lambda(y, y);
    var step1a = rules.r5209(a3, identity, f);
    Y.log(step1a);
    var step1b = rules.r5209(step1a, identity, g);
    Y.log(step1b);
    var step2a = rules.r5200(identity);
    Y.log(step2a);
    var step2b = rules.r(step1b,step2a, '/');
    Y.log(step2b);
    var a4 = rules.axiom4(call(lambda(y, y), x));
    Y.log(a4);
    var step2c = rules.r(a4, step2b, '/left/body/left');
    Y.log(step2c);
    var step2d = rules.r(a4, step2c, '/left/body/right');
    Y.log(step2d);
    var step3 = rules.r5201e(step2d, b);
    Y.log(step3);
    var left = rules.axiom4(step3.getLeft());
    var step4a = rules.r(left, step3, '/left');
    Y.log(step4a);
    var right = rules.axiom4(step3.getRight());
    var step4b = rules.r(right, step4a, '/right');
    Y.log(step4b);
    var step4c = rules.r5201b(step4b);
    return step4c;
  },

  forall: function() {
    return call('=', 'forall', lambda(f, call('=', f, lambda(x, T))));
  },

  r5211: function() {
    var step1a = rules.r5209(rules.axiom1(), lambda(y, T), f);
    var step1b = rules.r5209(step1a, lambda(y, T), g);
    Y.log(step1b);
    var reduce1 = rules.axiom4(step1b.getLeft().getLeft());
    // Note: Make a "reduce" rule that beta-reduces a subexpression.
    var reduce2 = rules.axiom4(step1b.getLeft().getRight());
    var step2b = rules.r(reduce1, step1b, '/left/left');
    var step2c = rules.r(reduce2, step2b, '/left/right');
    Y.log(step2c);
    var step3a = rules.r(rules.forall(), step2c, '/right/fn');
    Y.log(step3a);
    var reduce3 = rules.axiom4(step3a.getRight());
    Y.log(reduce3.getRight());
    // et cetera.
  }

};

// Stack of Inferences.  At each step, applyRule starts a new list for
// its detailed steps, and when done, pops that list, remembers those
// as its details and pushes its own record.
var proofStack = [];

function applyRule(key, stack, assumptions, params) {
  stack.push([]);
  var arguments = params == null ? assumptions : assumptions.concat(params);
  var result = ruleFns[key].apply(null, arguments);
  var step = new Inference(key, arguments, result, stack.pop());
  stack[stack.length].push(step);
  return result;
}

// Actual rule functions to call from other code.
var rules = {};

for (var key in ruleFns) {
  (function(k) {
    rules[k] = function() {
      return ruleFns[k].apply(null, arguments);
    }
  })(key);
};

//// Applying an inference rule

function Inference(name, assumes, args, result, details) {
  this.name = name;
  this.assumes = assumes;
  this.args = args;
  this.result = result;
  this.details = details;
}

/**
 * Returns a list of all hypotheses directly or indirectly used by
 * this Inference.  The same hypothesis occurs only once in the
 * result, but this does not deduplicate copies.
 */
Inference.prototype.allHypotheses = function() {
  var allHyps = [];
  function addHyps(proofStep) {
    for (var i = 0; i < this.args.length; i++) {
      var arg = this.args[i];
      if (arg instanceof Inference) {
        if (arg.name == 'assume') {
          var assumption = arg.args[0];
          if (Y.Array.indexOf(allHyps, assumption) < 0) {
            allHyps.push(arg.args[0]);
          }
        } else {
          addHyps(arg);
        }
      }
    }
  }
  addHyps(this, allHyps);
  return allHyps;
};


//// Internal utility functions

function equateToSelf(expr) {
  var e = call(lambda(x, x), expr);
  var step1 = axiom4(e);
  var lamb = step1.getLeft();
  var step2 = replaceLeft(step1, step1);
  return step2;
}

function assert(condition, message) {
  if (!condition) {
    Y.log(message);
    break_here();
  }
}


//// Export public names.

Y.Inference = Inference;
Y.rules = rules;



}, '0.1', {use: ['array-extras', 'expr']});
