// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

//// Applying an inference rule

function ProofStep(ruleName, ruleArgs) {
  this.ruleName = ruleName;
  this.ruleArgs = ruleArgs;
  this.result = rules[ruleName].apply(null, ruleArgs);
}

/**
 * Returns a list of all hypotheses directly or indirectly used by
 * this ProofStep.  The same hypothesis occurs only once in the
 * result, but this does not deduplicate copies.
 */
ProofStep.prototype.allHypotheses = function() {
  var allHyps = [];
  function addHyps(proofStep) {
    for (var i = 0; i < this.ruleArgs.length; i++) {
      var arg = this.ruleArgs[i];
      if (arg instanceof ProofStep) {
        if (arg.ruleName == 'assume') {
          var assumption = arg.ruleArgs[0];
          if (Y.Array.indexOf(allHyps, assumption) < 0) {
            allHyps.push(arg.ruleArgs[0]);
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


//// Rules (public)

// Map from inference rule name to a JavaScript procedure that
// implements it.
var rules = {

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R'.  The subexpression must match
   * the equation's LHS.
   */
  r: function(target, path, equation) {
    if (equation.isCall2('=')) {
      function replacer(expr) {
        if (expr.matches(equation.getLeft())) {
          return equation.getRight();
        } else {
          throw new Error('Rule R: expressions must match');
        }
      }
      return target.replace(path, replacer);
    } else {
      throw new Error('Not an equation: ' + target.toString());
    }
  },

  a1: function() {
    return call('=', call('&&', call(g, T), call(g, F)),
                call('forall', lambda(x, call(g, x))));
  },

  // (--> (= x y) (= (h x) (h y)))
  a2: function() {
    return call('-->', call('=', x, y), call('=', call(h, x), call(h, y)));
  },

  // (= (= f g) (= {x : (= (f x) (g x))} {x : T}))
  a3: function() {
    return call('=', call('=', f, g),
                call('=', lambda(x, call('=', call(f, x), call(g, x))),
                     lambda(x, T)));
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  a4: function(app) {
    if (app instanceof Y.Call && app.fn instanceof Y.Lambda) {
      var lambdaExpr = app.fn;
      return call('=', app,
                  Y.subFree(app.arg, lambdaExpr.bound, lambdaExpr.body));
    } else {
      throw new Error('Axiom 4 needs ({X : B} A): ' + app.toString());
    }
  },

  a5: function() {
    return call('=', call('the', call('=', y)), y);
  },

  r5200: function(a) {
    var step1 = rules.a4(call(lambda(x, x), a));
    return rules.r(step1, Y.path('/left'), step1);
  },

  r5201a: function(a, ab) {
    var aa = rules.r5200(a);
    var b = ab.getRight();
    var result = rules.r(a, Y.path('/'), ab);
    return result;
  },

  r5201b: function(ab) {
    var a = ab.getLeft();
    var aa = rules.r5200(a);
    Y.log('aa: ' + aa);
    var ba = rules.r(aa, Y.path('/left'), ab);
    return ba;
  }

};

//// Internal utility functions

function equateToSelf(expr) {
  var e = call(lambda(x, x), expr);
  var step1 = axiom4(e);
  var lamb = step1.getLeft();
  var step2 = replaceLeft(step1, step1);
  return step2;
}


//// Export public names.

Y.ProofStep = ProofStep;
Y.rules = rules;



}, '0.1', {use: ['array-extras', 'expr']});
