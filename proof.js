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

//// Applying an inference rule

// Stack of Inferences.  At each step, applyRule starts a new list for
// its detailed steps, and when done, pops that list, remembers those
// as its details and pushes its own record.
var proofStack = [];

/**
 *
 */
function applyRule(key, stack, arguments) {
  // In Java probably implement this with Callables and a method
  // to get the arguments of each.  Each item in rules becomes
  // a Callable.
  //
  // Each rule runs with a new list available for any steps within it.
  stack.push([]);
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

/**
 * Inference object: Immutable record of an inference step, either
 * primitive or composite.
 */
function Inference(name, inputs, result, details) {
  // Rule name
  this.name = name;
  // Inputs: a list of expressions or inference steps with result
  // expressions used by this step.  For composite inferences this
  // should be null.
  this.inputs = inputs;
  // The conclusion Expr of the inference..
  this.result = result;
  // List of component steps (Inferences), empty if not composite.
  this.details = details;
  // Used by findAssumptions to prevent infinite loops.
  this.marked = false;
}

/**
 * Returns a set of all of the expressions that this inference relies
 * on to be true in order to produce its result, indexed by repr.
 */
Inference.prototype.assumptions = function() {
  // Databases of input and output expressions of applications of
  // primitive rules, indexed by repr.
  var inputs  = {};
  var outputs = {};
  // Accumulates the inputs and outputs of this inference.
  function accumulate(inference) {
    // Whether rule R, an axiom, or a composite, the result
    // is always an output.
    outputs[inference.result.repr()] = inference.result;
    if (this.name == 'r') {
      var args = this.args;
      for (var i = 0; i < args.length; i++) {
        inputs[args[i].repr()] = args[i];
      }
    } else {
      var details = this.details;
      for (var i = 0; i < details.length; i++) {
        accumulate(details[i]);
      }
    }
  }
  accumulate(this);
  for (var key in outputs) {
    delete inputs[key];
  }
  return inputs;
};


/// Proof

function Proof() {
  this.steps = [];
}

Proof.prototype.insert = function(step, index) {
  step.index = index;
  var steps = this.steps;
  for (var i = index; i < steps.length; i++) {
    steps[i].index = index;
  }
  steps.splice(index, 0, step);
};


// ProofStep

function ProofStep(proof) {
  this.proof = proof;
  this.index = null;
  this.tactic = null;
  this.inference = null;
  this.deps = [];
}

/**
 * Sets the inference of this step.  The dependencies are a list of
 * ProofSteps this claims to depend on.  The results of those steps
 * should match the assumptions of the new inference, or else this
 * method inserts new steps that make the needed assertions.
 * Making new steps is a policy decision that could change.
 */
ProofStep.prototype.setInference = function(inference, dependencies) {
  this.inference = inference;
  // This will be a set of the dependencies, indexed by the repr of
  // the result of each one's inference.
  fromDeps = {};
  for (var i = 0; i < dependencies.length; i++) {
    var dep = dependencies[i];
    var result = dep.inference.result;
    fromDeps[result.repr()] = dep;
  }
  this.deps = [];
  var assumptions = inference.assumptions();
  // Connect the inputs needed by this step to other proof steps
  for (var repr in assumptions) {
    var assumption = assumptions[repr];
    var provided = fromDeps[repr];
    if (provided) {
      this.deps.push(dep);
    } else {
      var step = new ProofStep(this.proof);
      step.setInference(new Inference('assume', [], assumption), []);
      this.proof.insert(step, this.index);
    }
  }
};

/**
 * Returns a list of all inferences directly or indirectly used by
 * the given inference step.
 */
function findAssumptions(inference, database) {
}


//// Internal utility functions

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
