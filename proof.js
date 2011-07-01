// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

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
  // Or alternatively, its ancestor that has the proofStep CSS class.
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
// at the bottom of this file.  Maps from name to an inference
// containing a proof of the theorem.
var _theoremsByName = {};

/**
 * Checks that the theorem is not already in the database, then adds a
 * function to prove it to the set of theorems, which are indexed by
 * theorem name.
 */
function addTheorem(name) {
  Y.assert(!_theoremsByName[name], 'Theorem already exists');
  _theoremsByName[name] = true;
}

/**
 * Gets an existing theorem from the theorems database, or returns
 * null if there is none.  Runs the proof if it has not already run.
 */
function getTheorem(name) {
  var value = _theoremsByName[name];
  if (value == true) {
    value = _theoremsByName[name] = makeInference(name);
    Y.assert(value.proof.check(), 'Proof is not valid');
  }
  return value;
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


//// PROOFS

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


//// RENDERING AND EVENT HANDLING

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

/**
 * Returns the step number to be used for referencing a given proof
 * step (inference).  First number is 1.
 */
Proof.prototype.stepNumber = function(inference) {
  var index = Y.Array.indexOf(this.steps, inference);
  Y.assert(index >= 0, 'Inference not found in proof');
  return index + 1;
};

/**
 * Renders the steps of the proof into the given DOM node,
 * first clearing the node.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression has a "node" property that refers
 *   to a YUI node with its rendering.
 * - Each proofStep YUI node has a proofStep property that refers
 *   to the Inference (proof step) it represents.
 */
Proof.prototype.renderSteps = function(proofNode) {
  proofNode.setContent('');
  var steps = this.steps;
  // Map from inference result string to inference.
  var allSteps = {};
  for (var i = 0; i < steps.length; i++) {
    var inf = steps[i];
    var text = '<div class=proofStep><span class=stepNumber>'
      + (i + 1) + '.</span> </div>';
    var stepNode = proofNode.appendChild(text);
    stepNode.setData('proofStep', steps[i]);
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
    // Set up "hover" event handling on the stepNode.
    stepNode.on('hover',
                // Call "hover", passing these arguments as well as the event.
                Y.rbind(hover, null, this, i, 'in', proofNode),
                Y.rbind(hover, null, this, i, 'out', proofNode));
    allSteps[inf.result.asString()] = inf;
    // Caution: passing null to Y.on selects everything.
    var target = stepNode.one('span.ruleName');
    if (target) {
      Y.on('click',
           Y.rbind(renderSubProof, null, inf, proofNode),
           target);
    }
  }
};

/**
 * Renders the given inference and a header after
 * the given proof Node, clearing any other subproofs
 * that currently follow the proof node.
 */
function renderSubProof(event, inference, proofNode) {
  var parent = proofNode.get('parentNode');
  var next = proofNode.get('nextSibling');
  while (next) {
    next.remove();
    next = proofNode.get('nextSibling');
  }
  if (inference.name == 'theorem') {
    renderSteps(getTheorem(inference.arguments[0]), parent);
  } else {
    renderSteps(inference, parent);
  }
}

/**
 * Computes and returns a string of HTML with information about
 * the given proof step.
 */
Proof.prototype.computeStepInfo = function(inf) {
  // Add the name and other info to the display.
  var stepInfo;
  if (inf.name == 'axiom') {
    stepInfo = inf.arguments[0];
  } else if (inf.name == 'definition') {
    stepInfo = 'definition of ';
    if (inf.arguments.length == 2) {
      stepInfo += inf.arguments[1] + ' ';
    }
    stepInfo += inf.arguments[0];
  } else if (inf.name == 'theorem') {
    stepInfo = fancyName(inf, this);
  } else {
    if (inf.proof.steps.length == 0) {
      stepInfo = inf.name;
    } else {
      // It is a (derived) rule of inference.
      stepInfo = fancyName(inf, this);
    }
    var firstDep = true;
    for (var key in inf.deps) {
      if (firstDep) {
        firstDep = false;
      } else {
        stepInfo += ',';
      }
      stepInfo += ' ' + fancyStepNumber(this.stepNumber(inf.deps[key]));
    }
    var args = inf.arguments;
    var varInfo = '';
    // Display arguments that are variables.
    // TODO: Just showing variables is only a heuristic.
    //   do something better.
    for (var j = 0; j < args.length; j++) {
      if (args[j] instanceof Y.Var || typeof args[j] == 'string') {
        var str = '' + args[j];
        // Don't include path strings.
        if (str[0] != '/') {
          if (varInfo) {
            varInfo += ', ';
          }
          // Cover Var and string here.
          varInfo += str;
        }
      }
    }
    if (varInfo) {
      stepInfo += ' (' + varInfo + ')';
    }
  }
  return stepInfo;
};

/**
 * Renders an inference step name in a fancy way, currently
 * with a tooltip that briefly describes it.
 */
function fancyName(inference, proof) {
  var name = inference.name;
  if (name == 'theorem') {
    name = inference.arguments[0];
  }
  var info = rules[name].info;
  var comment = info.comment || '';
  var index = proof.stepNumber(inference) - 1;
  return '<span class=ruleName index=' + index
    + ' title="' + comment + '">' + name + '</span>';
}

/**
 * Renders a step number in a fancy way, currently in a SPAN
 * with class "stepNumber".
 */
function fancyStepNumber(n) {
  return '<span class=stepNumber>' + n + '</span>';
}


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
  var pruf = inference.arguments.length ? 'Rule ' : 'Proof of ';
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
  var assumptions = inference.assumptions();
  for (var key in assumptions) {
    var wff = assumptions[key];
    inference.proof.add(makeInference('given', [wff]), 0);
  }
  inference.proof.renderSteps(proofNode);
  Y.on('mouseover', exprHandleOver, proofNode);
  Y.on('mouseout', exprHandleOut, proofNode);
}

/**
 * Handle mouseovers on subexpressions.  The event target can
 * be any part of a proof node.
 */
function exprHandleOver(event) {
  var target = event.target;
  function isTarget(expr) {
    return expr.node == target;
  }
  target.addClass('hovered');
  var stepNode = target.ancestor('.proofStep');
  if (stepNode) {
    var proofStep = stepNode.getData('proofStep');
    var path = proofStep.result.pathTo(isTarget);
    hoverExpr(proofStep.result, path);
  }
};

/**
 * Defines what to when an expr is hovered.  Highlighting of the
 * DOM node is handled elsewhere, this is the Expr and Path part.
 */
function hoverExpr(wff, path) {
  var displayNode = Y.one('#hoverPath');
  if (displayNode) {
    // If there is no bottom panel, do nothing.
    // Y.log('Hover ' + (path ? path.toString() : ''));
    var expr = wff.locate(path);
    var pathStr = path ? path.toString() : '';
    displayNode.setContent(pathStr);
  }
}

/**
 * Handle mouseouts on subexpressions.
 */
function exprHandleOut(event) {
  event.target.removeClass('hovered');
  var displayNode = Y.one('#hoverPath');
  if (displayNode) {
    // Y.log('Unhover');
    // Do nothing if there is no bottom panel.
    displayNode.setContent('');
  }
};

/**
 * Event handler for "hover" events on proof steps.
 * Adds or removes highlighting for the step.
 *
 * <p>Event is the mouse event.  Proof is the containing proof,
 * index is the step index, direction is "in" or "out", and
 * proofNode is the DOM node of the proof.
 */
function hover(event, proof, index, direction, proofNode) {
  var inference = proof.steps[index];
  var iString = '' + (index + 1);
  var op = direction == 'in' ? 'addClass' : 'removeClass';
  var deps = inference.deps;
  var handler = hoverHandlers[inference.name];
  // Always add or remove the "hover" class to the step node
  // as the mouse goes in or oiut.
  inference.getStepNode()[op]('hover');
  
  // When entering a step, highlight all references to it.
  // When leaving remove highlights from all references.
  proofNode.all('span.stepNumber').each(function(node) {
      if (direction == 'in') {
        if (node.get('innerHTML') == iString) {
          node.addClass('referenced');
        }
      } else {
        node.removeClass('referenced');
      }
    });
  if (handler) {
    // If there is a hover handler for this type of inference, apply it.
    handler(inference, op);
  } else {
    // If no handler apply or remove default highlighting.
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
    inf.result.locate(path).node[op]('new');
    eqn.getRight().node[op]('old');
    eqn.getLeft().node[op]('new');
  },
  axiom4: function(inf, op) {
    var call = inf.result.getLeft();
    call.arg.node[op]('new');
    var target = call.fn.body;
    target.node[op]('scope');
    inf.result.getRight().node[op]('scope');
    var varName = call.fn.bound;
    target.findAll(varName,
                   function(v) { v.node[op]('occur'); },
                   inf.result.getRight(),
                   function(expr) { expr.node[op]('new'); });
  },
  reduce: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var dep = deps[args[0].asString()].result;
    var path = args[1];
    var call = dep.locate(path);
    var target = call.fn.body;
    var varName = call.fn.bound.name;
    var result = inf.result.locate(path);
    dep.node[op]('hover');
    call.arg.node[op]('new');
    target.node[op]('scope');
    result.node[op]('scope');
    target.findAll(varName,
                   function(v) { v.node[op]('occur'); },
                   result,
                   function(expr) { expr.node[op]('new'); });
  },
  useDefinition: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    target.node[op]('hover');
    target.locate(path).node[op]('old');
    inf.result.locate(path).node[op]('new');
  },
  instEqn: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = args[2].name;
    input.node[op]('hover');
    input.findAll(varName,
                  function(_var) { _var.node[op]('occur'); },
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
    input.node[op]('hover');
    input.arg.body.findAll(varName,
                           function(_var) { _var.node[op]('occur'); },
                           inf.result,
                           function(expr) { expr.node[op]('new'); });
  }
};


//// PARSING

/**
 * A token is a sequence of characters that are each alphanumeric
 * or ":", or a sequence that is none of these and not whitespace.
 * Returns an array of tokens in the input string, followed by
 * an "(end)" token.
 */
function tokenize(str) {
  var match;
  var pattern = /[(){}]|[:a-zA-Z0-9]+|[^:a-zA-Z0-9(){}\s]+/g;
  var result = [];
  while (match = pattern.exec(str)) {
    result.push(new Y.Var(match[0], match.index));
  }
  result.push(new Y.Var('(end)', str.length));
  return result;
}

// Input will be a tree in the form of a nested array
// of strings and arrays.  Explicit parentheses in the
// input become arrays in the input.  This parses prefix
// and infix operators into additional trees.
// This parses destructively, replacing structure in the
// input.
//
// Parse a subexpression of "a" starting at "pos"
// in the context of an operator to the left with a binding
// power of "leftPower", replacing the token at "pos"
// with a parsed tree.
//
// If just one argument is given, parse the whole array
// and return the parsed result.
//
// Reduces operators with greater than leftPower, replacing
// the token at "a" with the parsed subtree.  Otherwise
// leaves the token at "pos" unchanged.
//
function parse(tokens) {
  function next() {
    return tokens.length ? tokens.shift() : end;
  }

  function peek() {
    return tokens[0] || end;
  }

  function expect(expected) {
    var token = next();
    if (token.name != expected) {
      // Report somehow.
      var error = new Error('Expected ' + expected + ', got ' + token.name);
      error.position = token.pos;
      throw error;
    }
  }

  /**
   * Keep reducing leading parts into subtrees until the next token is
   * an infix operator with precedence not greater than lastPower.
   * Returns null if it consumes no input.
   */
  function parseAbove(lastPower) {
    var left = null;
    while (true) {
      var token = peek();
      var nextPower = getPrecedence(token);
      if (nextPower != null && nextPower <= lastPower) {
        return left;
      }
      next();
      // If an atomic expression or unary/nullary expression is
      // next, this will have it.
      var expr = null;
      if (token.name == '(') {
        expr = mustParseAbove(0);
        expect(')');
      } else if (token.name == '{') {
        var id = next();
        Y.assert(isId(id), 'Expected identifier, got ' + id.name);
        expect(peek().name == ':' ? ':' : '|');
        var body = mustParseAbove(0);
        expr = new Y.Lambda(id, body);
        expect('}');
      } else if (!left || nextPower == null) {
        // Treat the token as an atomic expression.
        expr = token;
      }
      // At this point expr and left are not both null.
      if (expr) {
        left = left ? new Y.Call(left, expr) : expr;
      } else {
        // Token is an infix operator of higher precedence than the last.
        // At this point there is always an expression in "left".
        left = new Y.Call(token, left);
        var right = parseAbove(nextPower);
        if (right) {
          left = new Y.Call(left, right);
        }
      }
    }
  }

  function mustParseAbove(lastPower) {
    var result = parseAbove(lastPower);
    if (!result) {
      throw new Error('Empty expression at ' + peek().pos);
    }
    return result;
  }

  // Do the parse!
  if (typeof tokens == 'string') {
    tokens = tokenize(tokens);
  }
  // The ending token.
  var end = tokens.pop();
  if (tokens.length < 1) {
    // There should be at least one real token.
    throw new Error('No parser input');
  }
  return parseAbove(0);
};

/**
 * Checks the name of the token at the location and removes
 * it from the input if it is the same, else throws an Error
 * with message and position of the token.
 */
function expect(a, pos, str) {
  if (a[pos].name == str) {
    a.splice(pos, 1);
  } else {
    // Report somehow.
    var error = new Error('Expected ' + str + ', got ' + a[pos]);
    error.position = a[pos].pos;
    throw error;
  }
}

/**
 * Is it a legal identifier?
 */
function isId(token) {
  return token instanceof Y.Var
    && token.name.match(/^[A-Za-z:$][A-Za-z0-9:$]*$/);
}

/**
 * Get a precedence value: null for symbols, defaults to
 * 1 for unknown non-symbols, the lowest infix precedence.
 */
function getPrecedence(token) {
  var name = token.name;
  var v = precedence[name];
  if (f) {
    return v;
  } else {
    return isId(name) ? null : 1;
  }
}

// Precedence table for infix operators.
var precedence = {
  // Closing tokens have power 0 to make infix parsing return.
  '(end)': 0,
  ')': 0,
  '}': 0,
  // Implication binds tighter than equality, as in the book.
  '=': 11,
  '-->': 12,
  '||': 13,
  '&&': 14,
  '<': 20,
  '<=': 20,
  '>': 20,
  '>=': 20,
  '+': 30,
  '-': 30,
  '*': 40,
  '/': 40,
  // Specials
  '(': 1000,
  '{': 1000
};

//// UTILITY FUNCTIONS

function addBottomPanel(node) {
  node = node || new Y.Node(document.body);
  var style = ('position: fixed; width: 100%; background-color: white; '
               + 'bottom:0px; left: 0em; border-top: 1px solid black');
  var html = '<div id="bottomPanel" style="' + style + '"></div>';
  var div = node.appendChild(html);
  div.appendChild('Path: <span id=hoverPath></span>');
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

// A stack of proofs currently in progress.
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
Y.getTheorem = getTheorem;
Y.define = define;
Y.defineCases = defineCases;
Y.getDefinition = getDefinition;
Y.renderSteps = renderSteps;
Y.createRules = createRules;
Y.addBottomPanel = addBottomPanel;
Y.tokenize = tokenize;
Y.parse = parse;
// TODO: Consider getting rid of this global variable.
Y.rules = rules;

// For testing:
Y.definitions = definitions;


}, '0.1', {use: ['array-extras', 'expr']});
