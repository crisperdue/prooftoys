// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

var identity = lambda(x, x);

var allT = lambda(x, T);

/// Rules (public)

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
    var rev = rules.eqnSwap(equation);
    return rules.r(rev, target, path);
  },

  axiom1: function() {
    return equal(call('&&', call(g, T), call(g, F)),
                 call('forall', lambda(x, call(g, x))));
  },

  // (--> (= x y) (= (h x) (h y)))
  axiom2: function() {
    return call('-->', equal(x, y), equal(call(h, x), call(h, y)));
  },

  // (= (= f g) (= {x : T} {x : (= (f x) (g x))}))
  axiom3: function() {
    return equal(equal(f, g),
                 call('forall',
                      lambda(x, equal(call(f, x), call(g, x)))));
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: function(app) {
    if (app instanceof Y.Call && app.fn instanceof Y.Lambda) {
      var lambdaExpr = app.fn;
      return equal(app,
                  Y.subFree(app.arg, lambdaExpr.bound, lambdaExpr.body));
    } else {
      throw new Error('Axiom 4 needs ({X : B} A), got: ' + app.toString());
    }
  },

  axiom5: function() {
    return equal(call('the', equal(y)), y);
  },

  defForall: function() {
    return equal('forall', equal(lambda(x, T)));
  },

  defNot: function() {
    return equal('not', equal(F));
  },

  defAnd: function() {
    return equal('&&', lambda(x, lambda(y, equal(lambda(g, call(g, T, T)),
                                                 lambda(g, call(g, x, y))))));
  },

  // Added by Cris instead of definition of F in book.
  // F = [T = F]
  axiomTIsNotF: function() {
    return call('not', equal(T, F));
  },

  // Note this can be proved like 5211.
  defAndTrue: function() {
    return equal(call('&&', T, p), p);
  },

  defAndFalse: function() {
    return equal(call('&&', F, p), F);
  },

  defOrTrue: function() {
    return allT;
    // TODO: here and below.
  },

  defOrFalse: function() {
    return identity;
  },

  defImpliesTrue: function() {
    return allT;
  },

  defImpliesFalse: function() {
    return lambda(x, equal(x, F));
  },

  // Takes an arbitrary expression A, concluding that it is equal
  // to itself. (5200)
  eqSelf: function(a) {
    var step1 = rules.axiom4(call(lambda(x, x), a));
    return rules.r(step1, step1, '/left');
  },

  // r5201a
  replaceWhole: function(a, ab) {
    var aa = rules.eqSelf(a);
    var b = ab.getRight();
    var result = rules.r(ab, a, '/');
    return result;
  },

  // r5201b
  eqnSwap: function(ab) {
    var a = ab.getLeft();
    var aa = rules.eqSelf(a);
    var ba = rules.r(ab, aa, '/left');
    return ba;
  },

  // r5201c
  eqnChain: function(ab, bc) {
    var ac = rules.r(bc, ab, '/right');
    return ac;
  },

  // r5201d
  applyBySides: function(ab, cd) {
    var a = ab.getLeft();
    var b = ab.getRight();
    var c = cd.getLeft();
    var d = cd.getRight();
    var ac = call(a, c);
    var acac = rules.eqSelf(ac);
    var acbc = rules.r(ab, acac, '/right/fn');
    var acbd = rules.r(cd, acbc, '/right/arg');
    return acbd;
  },

  // r5201e
  applyBoth: function(eqn, a) {
    var step1 = rules.eqSelf(call(eqn.locate('/left'), a));
    var step2 = rules.r(eqn, step1, '/right/fn');
    return step2;
  },

  // r5201f
  applyToBoth: function(a, bc) {
    var abab = rules.eqSelf(call(a, bc.getLeft()));
    var abac = rules.r(bc, abab, '/right/arg');
    return(abac);
  },

  /**
   * Substitutes term "a" for variable "v" in equation b_c,
   * with the result a consequence of b_c.  5209
   */
  instEqn: function(b_c, a, v) {
    var b = b_c.getLeft();
    var c = b_c.getRight();
    var ba_ba = rules.eqSelf(call(lambda(v, b), a));
    var ba_ca = rules.r(b_c, ba_ba, '/right/fn/body');
    var ba_sab = rules.axiom4(call(lambda(v, b), a));
    var ca_sac = rules.axiom4(call(lambda(v, c), a));
    var step5a = rules.r(ba_sab, ba_ca, '/left');
    var step5b = rules.r(ca_sac, step5a, '/right');
    return step5b;
  },

  // thm: T = [B = B] (5210)
  eqT: function(b) {
    var a3 = rules.r(rules.defForall(), rules.axiom3(), '/right/fn');
    var identity = lambda(y, y);
    var step1a = rules.instEqn(a3, identity, f);
    var step1b = rules.instEqn(step1a, identity, g);
    var step2a = rules.eqSelf(identity);
    // Eliminate the LHS of step2a:
    var step2b = rules.r(step1b, step2a, '/');
    var step2c = rules.reduce(step2b, '/right/body/left');
    var step2d = rules.reduce(step2c, '/right/body/right');
    var step3 = rules.applyBoth(step2d, b);
    var step4a = rules.reduce(step3, '/left');
    var step4b = rules.reduce(step4a, '/right');
    return step4b;
  },

  /**
   * Beta-reduce an application of a lambda expression to an argument,
   * with the subexpression identified by a path.
   */
  reduce: function(expr, path) {
    path = Y.path(path);
    var target = expr.locate(path);
    assert(target, 'Path ' + path + ' not found in ' + target);
    assert(target instanceof Y.Call && target.fn instanceof Y.Lambda,
           'Reduce needs a call to a lambda, got: ' + target);
    var equation = rules.axiom4(target);
    var result = rules.r(equation, expr, path);
    return result;
  },

  r5211: function() {
    var step1 = rules.instEqn(rules.axiom1(), lambda(y, T), g);
    var step2a = rules.reduce(step1, '/left/left');
    var step2b = rules.reduce(step2a, '/left/right');
    var step2c = rules.reduce(step2b, '/right/arg/body');
    var step3a = rules.eqT(lambda(x, T));
    var step3b = rules.rRight(rules.defForall(), step3a, '/right/fn');
    var step4 = rules.rRight(step3b, step2c, '/right');
    return step4;
  },

  /**
   * "T" is a theorem.
   */
  t: function() {
    var step1 = rules.eqSelf(T);
    var step2 = rules.eqT(T);
    var step3 = rules.rRight(step2, step1, '/');
    return step3;
  },

  r5212: function() {
    var step1 = rules.rRight(rules.r5211(), rules.t(), '/');
    return step1;
  },

  r5213: function(a_b, c_d) {
    assertEqn(a_b);
    var a = a_b.locate('/left');
    var b = a_b.locate('/right');
    assertEqn(c_d);
    var c = c_d.locate('/left');
    var d = c_d.locate('/right');
    var step1 = rules.eqT(a);
    var step2 = rules.r(a_b, step1, '/right/right');
    var step3 = rules.eqT(c);
    var step4 = rules.r(c_d, step3, '/right/right');
    var step5 = rules.r(step2, rules.r5212(), '/left');
    var step6 = rules.r(step4, step5, '/right');
    return step6;
  },

  /**
   * From an equation, infers a similar equation with each
   * side wrapped in a binding of the given variable.
   */
  bindEqn: function(eqn, v) {
    assert(eqn.isBinOp() && eqn.getBinOp() == '=',
           'Not an equation: ' + eqn);
    assert(v instanceof Y.Var, 'Not a variable: ' + v);
    var step1 = rules.eqSelf(lambda(v, eqn.getLeft()));
    var step2 = rules.r(eqn, step1, '/right/body');
    return step2;
  },

  r5214: function() {
    // This uses Cris's definition of T, so different proof than
    // in the book.
    var step1 = rules.instEqn(rules.defAndTrue(), F, p);
    return step1;
  },

  // TODO: remove
  // Asserts "forall A = {x : T} = A"
  forall: function(a) {
    return rules.r(rules.defForall(a), a, '/fn');
    // return rules.applyBoth(rules.defForall(), a, '/fn');
  },

  forallInst: function(target, expr) {
    assert(target.fn instanceof Y.Var && target.fn.name == 'forall',
           "Must be 'forall': " + target.fn);
    assert(target.arg instanceof Y.Lambda,
           "Must be lambda expression: " + target.arg);
    var step1 = rules.forall(target);
    var step2 = rules.applyBoth(step1, expr);
    var step3 = rules.reduce(step2, '/left');
    var step4 = rules.reduce(step3, '/right');
    var step5 = rules.r(step4, rules.t(), '/');
    return step5;
  },

  // 5216 by the book.
  andTBook: function(a) {
    var step1 = rules.axiom1();
    var step2 =
      rules.instEqn(step1, lambda(x, equal(call('&&', T, x), x)), g);
    var step3 = rules.reduce(step2, '/left/left');
    var step4 = rules.reduce(step3, '/left/right');
    var step5 = rules.reduce(step4, '/right/arg/body');
    var step6 = rules.r5213(rules.r5211(), rules.r5214());
    var step7 = rules.r(step5, step6, '/');
    var step8 = rules.forallInst(step7, a);
    return step8;
  },

  // 5216, using defAndTrue.
  andT: function(a) {
    var step1 = rules.instEqn(rules.defAndTrue(), a, p);
    return step1;
  },

  // Book only.  We use axiomTIsNotF instead of defining F.
  r5217: function() {
    var step1 = rules.instEqn(rules.axiom1(), lambda(x, equal(T, x)), g);
    var step2 = rules.reduce(step1, '/left/left');
    var step3 = rules.reduce(step2, '/left/right');
    var step4 = rules.reduce(step3, '/right/arg/body');
    var step5 = rules.rRight(rules.eqT(T), step4, '/left/left');
    var step6 = rules.andT(equal(T, F));
    var step7 = rules.r(step6, step5, '/left');
    var step8 = rules.instEqn(rules.axiom3(), lambda(x, T), f);
    var step9 = rules.reduce(step8, '/right/arg/body/left');
    var step10 = rules.instEqn(step9, lambda(x, x), g);
    var step11 = rules.reduce(step10, '/right/arg/body/right');
    // TODO: finish this using something like definition of F.
  },

  // 5218: [T = A] = A
  addTrue: function(a) {
    var step1 = rules.instEqn(rules.axiom1(),
                              lambda(x, equal(equal(T, x), x)),
                              g);
    var step2 = rules.reduce(step1, '/left/left');
    var step3 = rules.reduce(step2, '/left/right');
    var step4 = rules.reduce(step3, '/right/arg/body');
    var step5a = rules.eqT(T);
    var step5 = rules.eqnSwap(step5a);
    var step6a = rules.r(rules.defNot(), rules.axiomTIsNotF(), '/fn');
    var step6 = rules.eqnSwap(step6a);
    var step7 = rules.r5213(step5, step6);
    var step8 = rules.r(step4, step7, '/');
    var step9 = rules.forallInst(step8, a);
    return step9;
  },

  // 5219
  toTIsA: function(a) {
    var step1 = rules.addTrue(a);
    var step2 = rules.rRight(step1, a, '/');
    return step2;
  },

  // also 5219
  fromTIsA: function(t_a) {
    assertEqn(t_a);
    assert(t_a.locate('/left') == T,
           'Input should be [T = A]: ' + t_a);
    var a = t_a.locate('/right');
    var step2 = rules.r(rules.addTrue(a), t_a, '/');
    return step2;
  },

  // 5220, proved here by extensionality, not using 5206.
  uGen: function(a, v) {
    var step1 = rules.bindEqn(rules.eqT(T), x);
    var step2 = rules.instEqn(rules.axiom3(), lambda(v, T), g);
    var step3 = rules.instEqn(step2, lambda(x, T), f);
    var step4 = rules.reduce(step3, '/right/arg/body/left');
    var step5 = rules.reduce(step4, '/right/arg/body/right');
    var step6 = rules.r(rules.defForall(), step5, '/right/fn');
    var step7 = rules.rRight(step6, step1, '/');
    var step8 = rules.rRight(rules.defForall(), step7, '/fn');
    var step9 = rules.toTIsA(a);
    var step10 = rules.r(step9, step8, '/arg/body');
    return step10;
  },

  // 5221 (one variable), substitute A for v in B.
  sub: function(b, a, v) {
    var step1 = rules.uGen(b, v);
    var step2 = rules.forallInst(step1, a);
    return step2;
  },

  cases: function(v, a) {
    var step1a = rules.axiom4(call(lambda(v, a), T));
    var step1b = rules.toTIsA(step1a.locate('/right'));
    var step1c = rules.rRight(step1a, step1b, '/right');
    var step2a = rules.axiom4(call(lambda(v, a), F));
    var step2b = rules.toTIsA(step2a.locate('/right'));
    var step2c = rules.rRight(step2a, step2b, '/right');
    var step3 = rules.r5212();
    var step4a = rules.r(step1c, step3, '/left');
    var step4b = rules.r(step2c, step4a, '/right');
    var step5 = rules.sub(rules.axiom1(), lambda(v, a), g);
    var step6 = rules.r(step5, step4b, '/');
    var step7a = rules.forallInst(step6, v);
    var step7b = rules.reduce(step7a, '/');
    return step7b;
  },

  // Experiment with Andrews' definition of "and".
  funWithAnd: function() {
    var fa = rules.defForall();
    var a2 = rules.axiom2();
    var a3 = rules.axiom3();
    var step1 = rules.applyBoth(rules.defAnd(), T);
    var step2a = rules.reduce(step1, '/right');
    var step2b = rules.applyBoth(step2a, F);
    var step2c = rules.reduce(step2b, '/right');
    var step3 = rules.instEqn(a3, step2c.locate('/right/left'), f);
    var step4 = rules.instEqn(step3, step2c.locate('/right/right'), g);
    var step5 = rules.reduce(step4, '/right/arg/body/left');
    var step6 = rules.reduce(step5, '/right/arg/body/right');
    var step7 = rules.applyBoth(fa, step6.locate('/right/arg'));
    var step8 = rules.instEqn(a3, step7.locate('/right/left'), f);
    var step9 = rules.instEqn(step8, step7.locate('/right/right'), g);
    var step10 = rules.reduce(step9, '/right/arg/body/left');
    var step11 = rules.reduce(step10, '/right/arg/body/right');
    var step12 = rules.addTrue(step11.locate('/right/arg/body/right'));
    var step13 = rules.r(step12, step11, '/right/arg/body');
    return step12;
  }

};

//// Inferences

/**
 * Inference object: Immutable record of an inference step, either
 * primitive or composite.  The constructor is private; use
 * makeInference to create inferences in client code.
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
  if (typeof o == 'object') {
    var result = '{';
    for (var key in o) {
      if (o.hasOwnProperty(key)) {
        result += key + ': ';
        var value = o[key];
        var f = specials && specials[key];
        if (f) {
          result += f(value);
        } else if (typeof value == 'string') {
          result += '"' + o[key] + '"';
        } else if (value && value.concat) {
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
          result += '' + o[key];
        }
        result += ' ';
      }
    }
    return result + '}';
  } else {
    return o.toString();
  }
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
  assert(typeof name == 'string', 'Name must be a string: ' + name);
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
  arguments = arguments || [];
  inferenceStack.push([]);
  applyRule(name, arguments, inferenceStack);
  var inf = inferenceStack.pop().pop();
  return inf;
}

// Maybe each set of rules could have its own inference stack???
var inferenceStack = [[]];

// Actual rule functions to call from other code.
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

function assertEqn(expr) {
  assert(expr instanceof Y.Call
         && expr.fn instanceof Y.Call
         && expr.fn.fn instanceof Y.Var
         && expr.fn.fn.name == '=',
         'Must be an equation: ' + expr);
}


//// Export public names.

Y.rules = rules;
Y.ruleFns = ruleFns;
Y.inferenceStack = inferenceStack;
Y.makeInference = makeInference;

}, '0.1', {use: ['array-extras', 'expr']});
