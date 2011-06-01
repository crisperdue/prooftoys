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
  Y.assert(index >= 0, 'Inference not found in proof');
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

    // Render the WFF and record the rendered copy as the inference
    // result.
    inf.result = inf.result.render(wffNode);

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
        throw new Error('Need prior step: ' + aString);
      }
    }
    var stepInfo = this.computeStepInfo(inf);
    stepNode.appendChild('<span class=stepInfo>' + stepInfo + '</span>');
    stepNode.on('hover',
                // Call "hover" adding extra arguments at the end.
                Y.rbind(hover, stepNode, inf, 'in'),
                Y.rbind(hover, stepNode, inf, 'out'));
    allSteps[inf.result.asString()] = inf;
  }
};

/**
 * Computes and returns a string of HTML with information about
 * the given proof step.
 */
Proof.prototype.computeStepInfo = function(inf) {
  // Add the name and other info to the display.
  var stepInfo = (inf.name == 'axiom') ? inf.arguments[0] : inf.name;
  if (inf.name == 'axiom') {
    // Do nothing here, see above.
  } else if (inf.name == 'definition') {
    var text = ' of ';
    if (inf.arguments.length == 2) {
      text += inf.arguments[1] + ' ';
    }
    stepInfo += text + inf.arguments[0];
  } else if (inf.name == 'theorem') {
    stepInfo += ' ' + inf.arguments[0];
  } else {
    // It is a (derived) rule of inference.
    var firstDep = true;
    for (var key in inf.deps) {
      if (firstDep) {
        firstDep = false;
        stepInfo += ' ' + this.stepNumber(inf.deps[key]);
      } else {
        stepInfo += ', ' + this.stepNumber(inf.deps[key]);
      }
    }
    var args = inf.arguments;
    var varInfo = '';
    for (var j = 0; j < args.length; j++) {
      if (args[j] instanceof Y.Var) {
        if (varInfo) {
          varInfo += ' ';
        }
        varInfo += args[j].name;
      }
    }
    if (varInfo) {
      stepInfo += ' (' + varInfo + ')';
    }
  }
  return stepInfo;
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
  // The values of the deps have always been rendered.
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
  Y.assert(typeof name == 'string', 'Name must be a string: ' + name);
  var rule = rules[name].innerFn;
  Y.assert(rule, 'No such rule: ' + name);
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

/**
 * Checks that the theorem is not already in the database,
 * verifies that the inference's proof is valid, then
 * adds it to the set of theorems, which are indexed by
 * theorem name.
 */
function addTheorem(name, inference) {
  Y.assert(!_theoremsByName[name], 'Theorem already exists');
  Y.assert(inference.proof.check(), 'Proof is not valid');
  _theoremsByName[name] = inference;
}

/**
 * Gets an existing theorem from the theorems database, or
 * returns null if there is none.
 */
function getTheorem(name) {
  return _theoremsByName[name];
}


//// DEFINITIONS

// Indexed by the name defined.  Value is an expression if
// the definition is simple.  If by cases, the value is a
// map from 'T' and 'F' to the definition for each case.
var definitions = {};

/**
 * Add a simple abbreviation-like definition, e.g.
 * define('forall', equal(lambda(x, T))).
 */
function define(name, definition) {
  var free = definition.freeNames();
  Y.assert(!free[name], 'Definition is not simple: ' + name);
  Y.assert(!definitions[name], 'Already defined: ' + name);
  definitions[name] = equal(name, definition);
}

/**
 * Add a simple definition with true/false cases.  A call could
 * be something like defineCases('not', F, T).
 */
function defineCases(name, ifTrue, ifFalse) {
  Y.assert(!definitions[name], 'Already defined: ' + name);
  var freeTrue = ifTrue.freeNames();
  Y.assert(!freeTrue[name], 'Definition by cases is not simple: ' + name);
  var freeFalse = ifFalse.freeNames();
  Y.assert(!freeFalse[name], 'Definition by cases is not simple: ' + name);
  definitions[name] = {T: equal(call(name, T), ifTrue),
                       F: equal(call(name, F), ifFalse)};
}

/**
 * Fetch a simple or by-cases definition from the definitions
 * database.  Throws an exception if an appropriate definition
 * is not found.  Pass true or false to get the appropriate part
 * of a definition by cases.
 */
function getDefinition(name, tOrF) {
  var defn = definitions[name];
  Y.assert(defn, 'Not defined: ' + name);
  if (tOrF == null) {
    Y.assert(defn instanceof Y.Expr, 'Definition is not simple: ' + name);
    return defn;
  } else {
    if (tOrF == true || (tOrF instanceof Y.Var && tOrF.name == 'T')) {
      tOrF = 'T';
    } else if (tOrF == false || (tOrF instanceof Y.Var && tOrF.name == 'F')) {
      tOrF = 'F';
    }
    Y.assert(!(defn instanceof Y.Expr),
             'Definition is not by cases: ' + name);
    return defn[tOrF];
  }
}


//// RENDERING AND EVENTS

/**
 * Renders the proof steps of an inference and a header by appending
 * them to a container Node, which defaults to the document body.  The
 * first child is the header, rendered with class proofHeader.  The
 * second is the proof display, with class proofDisplay.
 */
function renderSteps(inference, node) {
  if (node == null) {
    node = new Y.Node(document.body);
  }
  var assumptions = inference.assumptions();
  var pruf = 'Proof of ';
  for (var assume in assumptions) {
    pruf = 'Rule ';
    break;
  }
  var argInfo = inference.arguments.join(', ');
  if (argInfo) {
    argInfo =
      ': <span style="font-weight: normal; font-family: monospace">'
      + argInfo + '</span>';
  }
  var comment = rules[inference.name].info.comment || '';
  node.appendChild('<div class=proofHeader><b>' + pruf
                   + inference.name + '</b>' + argInfo + '<br>'
                   + '<i>' + comment + '</i>'
                   + '</div>');
  var proofNode = node.appendChild('<div class=proofDisplay></div>');
  // Map to inference from its result as string.  Each result will be
  // annotated with links into the DOM.  Starts with the assumptions.
  // Add the assumptions to the proof before rendering it.
  for (var key in assumptions) {
    var wff = assumptions[key];
    inference.proof.add(makeInference('given', [wff]), 0);
  }
  inference.proof.renderSteps(proofNode);
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

// Arguments to the handler functions are an inference
// and the operation is "addClass" or "removeClass".
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
  },
  instEqn: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = args[2].name;
    inf.getStepNode()[op]('hover');
    input.node[op]('hover');
    input.findAll(varName,
                  function(_var) { _var.node[op]('new'); },
                  inf.result,
                  function(expr) { expr.node[op]('new'); });
  },
  sub: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = args[2].name;
    inf.getStepNode()[op]('hover');
    input.node[op]('hover');
    input.findAll(varName,
                  function(_var) { _var.node[op]('new'); },
                  inf.result,
                  function(expr) { expr.node[op]('new'); });
  },
  forallInst: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = input.arg.bound.name;
    inf.getStepNode()[op]('hover');
    input.node[op]('hover');
    input.arg.body.findAll(varName,
                           function(_var) { _var.node[op]('new'); },
                           inf.result,
                           function(expr) { expr.node[op]('new'); });
  }
};


//// UTILITY FUNCTIONS

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
//
// TODO: It is really roundabout to have both ruleInfo and rules.
// Simplify them.
var rules = {};

/**
 * Use a "rule info" object and add its rules to the "rules" object
 * that manages the inference stack so makeInference can work
 * properly.
 */
function createRules(ruleInfo) {
  for (var key in ruleInfo) {
    // Each call to infer will get the key and inferenceStack
    // from here, plus whatever args were passed by the caller.
    rules[key] = Y.bind(infer, null, key, inferenceStack);
    // Remember ALL of the info as well, redundantly.  See the "to do"
    // above.
    var info = ruleInfo[key];
    rules[key].info = info;
    var fn = (typeof info == 'function') ? info : info.action;
    // Each function in rules has its action function as
    // the value of its innerFn property.
    rules[key].innerFn = fn;
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
Y.define = define;
Y.defineCases = defineCases;
Y.getDefinition = getDefinition;
Y.getTheorem = getTheorem;
Y.renderSteps = renderSteps;
Y.createRules = createRules;
// TODO: Consider getting rid of this global variable.
Y.rules = rules;

// For testing:
Y.definitions = definitions;


}, '0.1', {use: ['array-extras', 'expr']});
