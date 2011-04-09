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
   * The name "TBD" is used in Inferences to indicate that
   * the result of the inference is to be proven.
   */
  TBD: function(assumption) {
    return assumption;
  },

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R.  The subexpression must match
   * the equation's LHS.
   */
  r: function(equation, target, path) {
    path = Y.path(path);
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

  /**
   * Same as Rule R, but replaces an occurrence in target of the right
   * side of the equation with its left side.
   */
  rRight: function(equation, target, path) {
    path = Y.path(path);
    var rev = rules.r5201b(equation);
    return rules.r(rev, target, path);
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
    return rules.r(step1, step1, '/left');
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
    var step1b = rules.r5209(step1a, identity, g);
    var step2a = rules.r5200(identity);
    var step2b = rules.r(step1b,step2a, '/');
    var a4 = rules.axiom4(call(lambda(y, y), x));
    var step2c = rules.r(a4, step2b, '/left/body/left');
    var step2d = rules.r(a4, step2c, '/left/body/right');
    var step3 = rules.r5201e(step2d, b);
    var left = rules.axiom4(step3.getLeft());
    var step4a = rules.r(left, step3, '/left');
    var right = rules.axiom4(step3.getRight());
    var step4b = rules.r(right, step4a, '/right');
    var step4c = rules.r5201b(step4b);
    return step4c;
  },

  forall: function(v, a) {
    return call('=', lambda(v, a), lambda(x, T));
  },

  defForall: function() {
    return call('=', 'forall', call('=', lambda(x, T)));
  },

  /**
   * Beta-reduce an application of a lambda expression to an argument,
   * with the subexpression identified by a path.
   */
  reduce: function(expr, path) {
    path = Y.path(path);
    var target = expr.locate(path);
    assert(target, 'Path ' + path + ' not found in ' + target);
    assert(target instanceof Y.Call && target.fn instanceof Y.Lambda);
    var equation = rules.axiom4(target);
    var result = rules.r(equation, expr, path);
    return result;
  },

  r5211: function() {
    var step1a = rules.r5209(rules.axiom1(), lambda(y, T), f);
    var step1b = rules.r5209(step1a, lambda(y, T), g);
    var step2a = rules.reduce(step1b, '/left/left');
    var step2b = rules.reduce(step2a, '/left/right');
    var step2c = rules.reduce(step2b, '/right/arg/body');
    var step3a = rules.r5210(lambda(x, T));
    var step3b = rules.rRight(rules.defForall(), step3a, '/right/fn');
    var step4 = rules.rRight(step3b, step2c, '/right');
    return step4;
  },

  /**
   * "T" is a theorem.
   */
  ruleT: function() {
    var step1 = rules.r5200(T);
    var step2 = rules.r5210(T);
    var step3 = rules.rRight(step2, step1, '/');
    return step3;
  },

  r5212: function() {
    var step1 = rules.rRight(rules.r5211(), rules.ruleT(), '/');
    return step1;
  }

};

//// Inferences

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
}

Inference.prototype.toString = function() {
  var result = debugString(this);
  if (result.length <= 200) {
    return result;
  } else {
    function detailer(details) {
      result = '[';
      for (var i = 0; i < details.length; i++) {
        if (i > 0) {
          result += ', ';
        }
        result += details[i].name;
      }
      return result + ']';
    }
    return debugString(this, {details: detailer});
  }
}

function debugString(o, specials) {
  var result = '{';
  for (var key in o) {
    if (o.hasOwnProperty(key)) {
      result += key + ': ';
      var value = o[key];
      var f = specials && specials[key];
      if (f) {
        result += f(value);
      } else if (typeof value == 'string')
        result += '"' + o[key] + '"';
      else if (value.concat) {
        vString = o[key].toString();
        if (vString.length > 40) {
          result += '[\n';
          for (var i = 0; i < value.length; i++) {
            result += value[i] + '\n';
          }
          result += ']\n';
        } else {
          result += '[' + o[key] + ']';
        }
      } else {
        result += o[key].toString();
      }
      result += ' ';
    }
  }
  return result + '}'
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
    // For axioms, definitions, and rule R the result is an output.
    if (this.name.match(/^axiom|^def[A-Z]/)) {
      outputs[inference.result.repr()] = inference.result;
    }
    if (this.name == 'r') {
      outputs[inference.result.repr()] = inference.result;
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

/**
 * Applies the rule with the given name to the arguments,
 * pushing a record of its inference onto the given stack (array),
 * and returning the result of the Inference, an expression.
 * If there no such rule, returns null and has no effect.
 */
function applyRule(name, arguments, stack) {
  // In Java probably implement this with Callables and a method
  // to get the arguments of each.  Each item in rules becomes
  // a Callable.
  //
  // Each rule runs with a new list available for any steps within it.
  var rule = ruleFns[name];
  if (rule) {
    stack.push([]);
    var result = ruleFns[name].apply(null, arguments);
    var step = new Inference(name, arguments, result, stack.pop());
    stack[stack.length - 1].push(step);
    return result;
  } else {
    return null;
  }
}

/**
 * Makes and returns an inference by running the named rule with the
 * given arguments.
 */
function makeInference(name, arguments) {
  inferenceStack.push([]);
  applyRule(name, arguments, inferenceStack);
  var inf = inferenceStack.pop().pop();
  return inf;
}

var inferenceStack = [[]];

// Actual rule functions to call from other code.
// Maybe each set of rules could have its own inference stack???
var rules = {};

for (var key in ruleFns) {
  (function(k) {
    rules[k] = function() {
      return applyRule(k, arguments, inferenceStack);
    }
  })(key);
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
  if (inference.name == 'TBD') {
    if (dependencies && dependencies.length > 0) {
      assert(false, 'TBD inference cannot have dependencies');
    }
    return;
  }
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
      step.setInference(new Inference('TBD', [], assumption), []);
      this.proof.insert(step, this.index);
    }
  }
};


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
Y.ruleFns = ruleFns;
Y.inferenceStack = inferenceStack;
Y.makeInference = makeInference;

}, '0.1', {use: ['array-extras', 'expr']});
