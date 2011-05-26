// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

//// PROOF

function Proof() {
  // Steps in order.
  this.steps = [];
}

/**
 * Add an inference to this proof, optionally specifying its
 * index.  Default location is at the end.
 */
Proof.prototype.add = function(inference, index) {
  if (index == null) {
    this.steps.push(inference);
  } else {
    this.steps.splice(index, 0, inference);
  }
};

/**
 * Used by makeInference.  TODO: eliminate the use and remove?
 */
Proof.prototype.pop = function() {
  return this.steps.pop();
};

/**
 * Check that the proof is legal.
 */
Proof.prototype.check = function() {
  var inputs = this.assumptions();
  // Confirm that there are no assumptions required.
  for (var key in inputs) {
    return false;
  }
  return true;
}

/**
 * Like Inference.assumptions, for a proof.
 */
Proof.prototype.assumptions = function() {
  var inputs = {};
  var outputs = {};
  var steps = this.steps;
  for (var i = 0; i < steps.length; i++) {
    var inference = steps[i];
    outputs[inference.result.asString()] = inference.result;
    var assumes = steps[i].assumptions();
    for (var key in assumes) {
      inputs[key] = assumes[key];
    }
  }
  for (var key in outputs) {
    delete inputs[key];
  }
  return inputs;
};

Proof.prototype.stepNumber = function(inference) {
  var index = Y.Array.indexOf(this.steps, inference);
  assert(index >= 0, 'Inference not found in proof');
  return index + 1;
};

/**
 * Renders the steps of the proof into the given DOM node.
 */
Proof.prototype.renderSteps = function(node) {
  var steps = this.steps;
  // Map from inference result string to inference.
  var allSteps = {};
  for (var i = 0; i < steps.length; i++) {
    var inf = steps[i];
    var text = '<div class="proofStep">' + (i + 1) + '. </div>';
    var stepNode = node.appendChild(text);
    // See appendSpan in expr.js.
    var wffNode = stepNode.appendChild('<span class=expr></span>');
    // Record the annotated expression as the inference result.
    inf.result = inf.result.render(wffNode);
    // Add the name to the display.
    var stepName = inf.name == 'axiom' ? inf.arguments[0] : inf.name;
    stepNode.appendChild('&nbsp;&nbsp;' + stepName);
    // Map to inference, from its result expression as string.
    // Represents steps depended on by the inference.
    // Attach the result as the inference "deps" property.
    inf.deps = {};
    var assumptions = inf.assumptions();
    // Remember dependencies between inference steps as we go.
    for (var aString in assumptions) {
      var step = allSteps[aString];
      if (step) {
        inf.deps[aString] = step;
      } else {
        Y.log('No prior step: ' + aString);
      }
    }
    if (inf.name == 'axiom') {
      // Do nothing here, see above.
    } else if (inf.name == 'theorem') {
      stepNode.appendChild('&nbsp;' + inf.arguments[0]);
    } else {
      var firstDep = true;
      for (var key in inf.deps) {
        if (firstDep) {
          firstDep = false;
          stepNode.appendChild('&nbsp;' + this.stepNumber(inf.deps[key]));
        } else {
          stepNode.appendChild(', ' + this.stepNumber(inf.deps[key]));
        }
      }
    }
    stepNode.on('hover',
                // Call "hover" adding extra arguments at the end.
                Y.rbind(hover, stepNode, inf, 'in'),
                Y.rbind(hover, stepNode, inf, 'out'));
    allSteps[inf.result.asString()] = inf;
  }
};


//// INFERENCE

/**
 * Inference object: Immutable record of an inference step, either
 * primitive or composite.  The constructor is private; use
 * makeInference to create inferences in client code.
 */
function Inference(name, ruleArgs, result, proof) {
  // Rule name
  this.name = name;
  // RuleArgs: a list of expressions or inference steps with result
  // expressions used by this step.  For composite inferences this
  // should be null.
  this.arguments = ruleArgs;
  // The conclusion Expr of the inference..
  this.result = result;
  // Proof of the result (Inferences), empty for a primitive inference.
  this.proof = proof;
  // If rendered, has a "deps" property, a map from result string
  // to the premises of this inference, themselves inferences.
  //
  // TODO: Specify deps explicitly rather than computing it.
  //   The same thing may be proved more than once, especially when using
  //   proof procedures, so be specific about which dep is intended.
}

Inference.prototype.getStepNode = function() {
  return this.result.node.get('parentNode');
};

Inference.prototype.toString = function() {
  var result = debugString(this);
  if (result.length <= 200) {
    return result;
  } else {
    function detailer(proof) {
      if (proof == null) {
        return '' + proof;
      }
      var steps = proof.steps;
      result = '[';
      for (var i = 0; i < steps.length; i++) {
        if (i > 0) {
          result += ', ';
        }
        result += steps[i].name;
      }
      return result + ']';
    }
    return debugString(this, {proof: detailer});
  }
};

/**
 * Returns a set of wffs this inference relies on to be true in order
 * to produce its result, as a map indexed by their string
 * representations.
 */
Inference.prototype.assumptions = function() {
  // Accumulates the inputs and outputs of this inference.
  // For axioms, definitions, and rule R the result is an output.
  if (this.name.match(/^axiom|^def[A-Z]/)) {
    // Axioms and definitions need no inputs.
    return {};
  } else if (this.name == 'r') {
    var args = this.arguments;
    var inputs = {};
    inputs[args[0].asString()] = args[0];
    inputs[args[1].asString()] = args[1];
    return inputs;
  } else {
    return this.proof.assumptions();
  }
};

/**
 * Applies the rule with the given name to the arguments,
 * pushing a record of its inference onto the given stack (array),
 * and returning the result of the Inference, an expression.
 * If there no such rule, throws an exception.
 */
function applyRule(name, ruleArgs, stack) {
  assert(typeof name == 'string', 'Name must be a string: ' + name);
  var rule = rules[name].innerFn;
  assert(rule, 'No such rule: ' + name);
  stack.push(new Proof());
  var result = rule.apply(null, ruleArgs);
  var step = new Inference(name, ruleArgs, result, stack.pop());
  result.inference = step;
  stack[stack.length - 1].add(step);
  return result;
}

/**
 * Makes and returns an inference by running the named rule with the
 * given arguments, or an empty list if none are given.
 *
 * TODO: In Java build proofs directly in "rules" code, and eliminate
 * the inferenceStack.  Each rule returns a Proof (Inference?), and
 * each fule function makes a new Proof and adds steps to it, using
 * a function that adds to the proof and returns the result.
 * e.g. var step3 = myProof.addStep(ruleR( ... ));
 */
function makeInference(name, ruleArgs) {
  ruleArgs = ruleArgs || [];
  inferenceStack.push(new Proof());
  applyRule(name, ruleArgs, inferenceStack);
  var inf = inferenceStack.pop().pop();
  return inf;
}


//// THEOREMHOOD

// Private to addTheorem, getTheorem, and the initializations
// at the bottom of this file.
var _theoremsByName = {};

function addTheorem(name, inference) {
  assert(inference.proof.check(), 'Proof is not valid');
  assert(!_theoremsByName[name], 'Theorem already exists');
  _theoremsByName[name] = inference;
}

function getTheorem(name) {
  return _theoremsByName[name];
}


//// DEFINITIONS

// TODO: Support simplel definition and definition by cases.


//// RENDERING AND EVENTS

function renderSteps(inference, node) {
  if (node == null) {
    node = new Y.Node(document.body)
      .appendChild('<div style="margin: 1em; font-family: monospace"></div>');
  }
  node.appendChild('<div style="margin: .5em"><b>Proof of '
                   + inference.name + '</b></div>');
  var assumptions = inference.assumptions();
  // Map to inference from its result as string.  Each result will be
  // annotated with links into the DOM.  Starts with the assumptions.
  // Add the assumptions to the proof before rendering it.
  for (var key in assumptions) {
    var wff = assumptions[key];
    inference.proof.add(makeInference('given', [wff]), 0);
  }
  inference.proof.renderSteps(node);

}

/**
 * Event handler for "hover" events.
 */
function hover(event, inference, direction) {
  var op = direction == 'in' ? 'addClass' : 'removeClass';
  var deps = inference.deps;
  var handler = hoverHandlers[inference.name];
  if (handler) {
    handler(inference, op);
  } else {
    this[op]('hover');
    for (var key in deps) {
      deps[key].result.node[op]('dep');
    }
  }
}

var hoverHandlers = {
  r: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var eqn = deps[args[0].asString()].result;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    target.node[op]('hover');
    target.locate(path).node[op]('old');
    inf.getStepNode()[op]('hover');
    inf.result.locate(path).node[op]('new');
    eqn.getLeft().node[op]('old');
    eqn.getRight().node[op]('new');
  },
  rRight: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var eqn = deps[args[0].asString()].result;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    target.node[op]('hover');
    target.locate(path).node[op]('old');
    inf.getStepNode()[op]('hover');
    inf.result.locate(path).node[op]('new');
    eqn.getRight().node[op]('old');
    eqn.getLeft().node[op]('new');
  },
  reduce: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var target = deps[args[0].asString()].result;
    var path = args[1];
    target.node[op]('hover');
    target.locate(path).node[op]('new');
    inf.getStepNode()[op]('hover');
    inf.result.locate(path).node[op]('new');
  }
};


//// UTILITY FUNCTIONS

function assert(condition, message) {
  if (!condition) {
    if (typeof message == 'function') {
      message = message();
    }
    console.log(message);
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

/**
 * Returns a string showing the top-level properties
 * of an object, and their values.
 */
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

// Maybe each set of rules could have its own inference stack???
var inferenceStack = [new Proof()];

// Map from rule name to function.  The function runs the
// core rule code, wrapped in more code that makes potentially
// nested inferences using makeInference.
var rules = {};

/**
 * Take a "rule info" object and produce a "rules" object
 * that manages the inference stack so makeInference can work
 * properly.
 */
function createRules(ruleInfo) {
  for (var key in ruleInfo) {
    // Each call to infer will get the key and inferenceStack
    // from here, plus whatever args were passed by the caller.
    rules[key] = Y.bind(infer, null, key, inferenceStack);
    // Each function in rules has its action function as
    // the value of its innerFn property.
    rules[key].innerFn = ruleInfo[key];
  }
}

function infer(name, stack, etc) {
  var ruleArgs = [];
  for (var i = 2; i < arguments.length; i++) {
    ruleArgs.push(arguments[i]);
  }
  return applyRule(name, ruleArgs, stack);
}


//// Export public names.

Y.inferenceStack = inferenceStack;
Y.makeInference = makeInference;
Y.addTheorem = addTheorem;
Y.getTheorem = getTheorem;
Y.renderSteps = renderSteps;
Y.assert = assert;
Y.assertEqn = assertEqn;
Y.createRules = createRules;
// TODO: Consider getting rid of this global variable.
Y.rules = rules;

}, '0.1', {use: ['array-extras', 'expr']});
