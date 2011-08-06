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
  // If rendered, the YUI node (proof step node) for this step.
  this.node = null;
  // If rendered, may have a "selection" property or a "selections"
  // property indicating any expressions in it currently selected
  // in the UI:
  this.selections = [];
  this.selection = null;
  //
  // If rendered, has a "deps" property, a map from result string
  // to the premises of this inference, themselves inferences.
  // The values of the deps have always been rendered.
  //
  // TODO: Specify deps explicitly rather than computing it.
  //   The same thing may be proved more than once, especially when using
  //   proof procedures, so be specific about which dep is intended.
}

/**
 * Returns the proof step DOM node for this Inference.  Assumes
 * the inference has been rendered.
 */
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


//// CONSTANTS

// The built-in constants.
var _constants = {T: true, F: true, '=': true, the: true};

/**
 * Return a true value iff the given expression is a Var
 * and is a built-in constant or has a definition.
 */
function isConstant(name) {
  if (name instanceof Y.Var) {
    name = name.name;
  }
  if (!(typeof name == 'string')) {
    return false;
  }
  return _constants[name] || !!definitions[name];
}


//// PROOFS

function Proof() {
  // Steps in order.
  this.steps = [];
  // A rendered proof can have a single selected step or
  this.control = null;
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

/**
 * Returns the step number to be used for referencing a given proof
 * step (inference).  First number is 1.
 */
Proof.prototype.stepNumber = function(inference) {
  var index = Y.Array.indexOf(this.steps, inference);
  Y.assert(index >= 0, 'Inference not found in proof');
  return index + 1;
};


//// PROOF CONTROL

// TODO: Extend these to support proof steps that can take more
// than one selection.

/**
 * Construct a ProofControl given a DOM node and handler function for
 * selection events.  Properties:
 *
 * proof: the proof
 * node: Node containing the entire rendering of the proof.
 * stepsNode: Node containing all of the rendered steps as children.
 * editorButton: step insertion button, or null.
 */
function ProofControl(proof) {
  var controller = this;
  this.proof = proof;
  // a set (array) of selected steps.
  this.selections = [];
  this.selection = null;

  // Only official "proof nodes" are permitted to have this class:
  // Contains the step nodes.
  html =
    '<table class=proofDisplay><tr><td><div class=proofSteps></div></table>';
  this.node = Y.Node.create(html);
  this.stepsNode = this.node.one('.proofSteps');
  this.stepEditor = new Y.StepEditor(this);
  this.editorVisible = false;

  var html = ('<input class=addStep type=button value="+" '
              + 'title="Add a step to the proof">');
  this.editorButton =
    this.stepsNode.get('parentNode').appendChild(html);
  this.setEditable(false);
  // TODO: eventually default this to true.
  this.editable = false;
  this.editorButton.on('click', function () {
      controller.showStepEditor(controller.stepsNode.get('children').length);
      this.set('disabled', true);
    });
  renderSteps(this);
  // Set up handling of mouseover and mouseout events.
  Y.on('mouseover', exprHandleOver, this.node);
  Y.on('mouseout', exprHandleOut, this.node);
}

/**
 * Displays the proof step editor at the given index in the proof,
 * setting it as the stepEditor.  If the index is greater than the
 * index of any proof step, appends it at the end.
 */
ProofControl.prototype.showStepEditor = function(position) {
  // TODO: Handle placement of the editor at the location of
  // an existing step.
  addChild(this.stepsNode, position, this.stepEditor.node);
  this.editorVisible = true;
}

ProofControl.prototype.hideStepEditor = function() {
  this.stepEditor.node.remove();
  this.stepEditor.reset();
  this.deselectStep();
  this.editorButton.set('disabled', false);
  this.editorVisible = false;
}

/**
 * Generic function to add a node to an element at a position.
 */
function addChild(parent, position, node) {
  var children = parent.get('children');
  if (position == children.length) {
    parent.appendChild(node);
  } else {
    parent.insertBefore(node, children[position]);
  }
}

/**
 * Makes the control editable or not by showing/hiding the
 * editor button and flagging its state.
 */
ProofControl.prototype.setEditable = function(state) {
  this.editable = state;
  this.editorButton.setStyle('display', state ? '' : 'none');
}

/**
 * Unconditionally select the step, no other action.
 */
ProofControl.prototype.selectStep = function(step) {
  step.node.addClass('selected');
  this.selection = step;
};

/**
 * Unconditionally deselect any selected step and any
 * selected expression in it.
 */
ProofControl.prototype.deselectStep = function() {
  var step = this.selection;
  if (step) {
    step.node.removeClass('selected');
    this.selection = null;
    this.deselectExpr(step);
  }
};

/**
 * Unconditionally select the expr, no other action.
 */
ProofControl.prototype.selectExpr = function(expr) {
  var step = getProofStep(expr);
  expr.node.addClass('selected');
  step.selection = expr;
};

/**
 * Unconditionally deselect any selected expr in the
 * step, no other action.
 */
ProofControl.prototype.deselectExpr = function(step) {
  var expr = step.selection;
  if (expr) {
    expr.node.removeClass('selected');
    step.selection = null;
  }
};

/**
 * Handler for click on a proof step.  Selects the current
 * step, deselecting any other.  Toggles the current one if
 * already selected.
 */
ProofControl.prototype.handleStepClick = function(step) {
  if (this.editorVisible) {
    var selected = this.selection;
    this.deselectStep();
    if (selected) {
      this.deselectExpr(selected);
    }
    if (step != selected) {
      this.selectStep(step);
    }
  }
};

/**
 * Handler for click on a subexpression in a step.
 * Deselects any other selected expression in the step,
 * toggles the current one if already selected.  Prevents
 * event bubbling up to the step itself.
 */
ProofControl.prototype.handleExprClick = function(expr) {
  if (this.editorVisible) {
    var step = getProofStep(expr);
    var selection = this.selection;
    var oldExpr = null;
    this.deselectStep();
    if (selection) {
      oldExpr = selection.selection;
      this.deselectExpr(selection);
    }
    if (expr != oldExpr) {
      this.selectExpr(expr);
    }
    // Always select the step containing the clicked expression.
    this.selectStep(step);
    // Don't bubble the event up to the proof step.
    event.stopPropagation();
  }
};


//// RENDERING AND EVENT HANDLING

/**
 * Renders the steps of the controller's proof into its stepsNode,
 * first clearing the node.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression has a "node" property that refers
 *   to a YUI node with its rendering.
 * - Each proofStep YUI node has a proofStep data property that refers
 *   to the Inference (proof step) it represents.
 */
function renderSteps(controller) {
  var proof = controller.proof;
  var stepsNode = controller.stepsNode;
  stepsNode.setContent('');
  stepsNode.setData('proof', proof);
  var steps = proof.steps;
  // Map from inference result string to inference.
  var allSteps = {};
  for (var i = 0; i < steps.length; i++) {
    var inf = steps[i];
    var text = '<div class=proofStep><span class=stepNumber>'
      + (i + 1) + '.</span></div>';
    var stepNode = stepsNode.appendChild(text);
    inf.node = stepNode;
    stepNode.setData('proofStep', steps[i]);
    // See appendSpan in expr.js.
    var wffNode = stepNode.appendChild('<span class=expr></span>');

    // Render the WFF and record the rendered copy as the inference
    // result.
    inf.result = inf.result.render(wffNode);

    // Set up click handlers for selections within the step.
    Y.on('click',
         // This implements a policy of one selection per proof step.
         // TODO: Implement such policies in the proof controller.
         function(event) {
           controller.handleExprClick(getExpr(event.target));
         },
         wffNode);
    Y.on('click',
         function(event) {
           controller.handleStepClick(getProofStep(event.target));
         },
         stepNode);
                
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
    var stepInfo = computeStepInfo(proof, inf);
    stepNode.appendChild('<span class=stepInfo>' + stepInfo + '</span>');
    // Set up "hover" event handling on the stepNode.
    stepNode.on('hover',
                // Call "hover", passing these arguments as well as the event.
                Y.rbind(hoverStep, null, proof, i, 'in', stepsNode),
                Y.rbind(hoverStep, null, proof, i, 'out', stepsNode));

    allSteps[inf.result.asString()] = inf;
    // Caution: passing null to Y.on selects everything.
    var target = stepNode.one('span.ruleName');
    if (target) {
      target.on('click', Y.rbind(function(event, inf) {
            renderSubProof(event, inf, stepsNode, controller.editable);
            // Don't give the proof step a chance to select itself.
            event.stopPropagation();
          }, null, inf));
    }
  }
};

/**
 * Renders the given inference and a header after
 * the given proof Node, clearing any other subproofs
 * that currently follow the proof node.
 */
function renderSubProof(event, inference, proofNode, editable) {
  var display = proofNode.ancestor('.proofDisplay');
  var parent = display.get('parentNode');
  var next = display.get('nextSibling');
  while (next) {
    next.remove();
    next = display.get('nextSibling');
  }
  if (inference.name == 'theorem') {
    renderInference(getTheorem(inference.arguments[0]), parent, editable);
  } else {
    renderInference(inference, parent, editable);
  }
}

/**
 * Computes and returns a string of HTML with information about
 * the given proof step.
 */
function computeStepInfo(proof, inf) {
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
    stepInfo = fancyName(inf, proof);
  } else {
    if (inf.proof.steps.length == 0) {
      stepInfo = inf.name;
    } else {
      // It is a (derived) rule of inference.
      stepInfo = fancyName(inf, proof);
    }
    var firstDep = true;
    for (var key in inf.deps) {
      if (firstDep) {
        firstDep = false;
      } else {
        stepInfo += ',';
      }
      stepInfo += ' ' + fancyStepNumber(proof.stepNumber(inf.deps[key]));
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
}

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
 * second is the proof display.  Returns the proof display node.
 */
function renderInference(inference, node, editable) {
  if (node == null) {
    node = new Y.Node(document.body);
  }
  var pruf = inference.arguments.length ? 'Rule ' : 'Proof of ';
  var argInfo = '';
  for (var i = 0; i < inference.arguments.length; i++) {
    if (i > 0) {
      argInfo += ', ';
    }
    var arg = inference.arguments[i];
    if (typeof arg == 'string' || arg instanceof Y.Expr) {
      argInfo += arg;
    } else {
      argInfo += debugString(inference.arguments[i]);
    }
  }
  argInfo =
    ': <span style="font-weight: normal; font-family: monospace">'
    + argInfo + '</span>';
  var comment = rules[inference.name].info.comment || '';
  node.appendChild('<div class=proofHeader><b>' + pruf
                   + inference.name + '</b>' + argInfo + '<br>'
                   + '<i>' + comment + '</i>'
                   + '</div>');
  // Map to inference from its result as string.  Each result will be
  // annotated with links into the DOM.  Starts with the assumptions.
  // Add the assumptions to the proof before rendering it.
  var assumptions = inference.assumptions();
  for (var key in assumptions) {
    var wff = assumptions[key];
    inference.proof.add(makeInference('given', [wff]), 0);
  }
  var controller = new ProofControl(inference.proof);
  node.append(controller.node);
  controller.setEditable(editable);
}



//// PROOF NAVIGATION

// Every Expr (expression) of a rendered proof has a "node" property
// that references the YUI Node that has the display for that
// expression.  From each of these nodes the YUI Node for its proof
// step (Inference) is accessible, and from the YUI Node for a proof
// step, the inference itself accessible.  From any of these YUI Nodes
// the Node of the entire proof is accessible, and from it the Proof
// object, all using the API below.

/**
 * Gets the DOM node associated with the step, given the YUI
 * node for all or part of the expression for the step.
 */
function getStepNode(node) {
  return node.ancestor('.proofStep', true);
}

/**
 * Gets the proof step (Inference) of the step that renders
 * in part into the given YUI Node.  Also accepts an Expr of
 * a rendered proof.
 */
function getProofStep(node) {
  if (node instanceof Y.Expr) {
    node = node.node;
  }
  return getStepNode(node).getData('proofStep');
}

/**
 * Gets the YUI Node of a rendered proof given the YUI node of
 * one of its steps or of an expression in a step.
 */
function getStepsNode(node) {
  return node.ancestor('.proofSteps', true);
}

/**
 * Gets the proof that renders in part into the given YUI Node.
 * Also accepts an Expr or Inference of a rendered proof.
 */
function getProof(node) {
  if (node instanceof Y.Expr) {
    node = node.node;
  }
  if (node instanceof Inference) {
    node = node.getStepNode();
  }
  return getStepsNode(node).getData('proof');
}

/**
 * Returns the expression associated with a YUI node.
 */
function getExpr(node) {
  // Go up to the proof step then look through all subexpressions.
  var step = getProofStep(node);
  return step.result.search(function (expr) { return expr.node == node; },
                            true);
}


//// EVENT HANDLING

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
    // Do nothing if there is no bottom panel.
    displayNode.setContent('');
  }
};

function addClass(node, className) {
  node.addClass(className);
}

function removeClass(node, className) {
  node.removeClass(className);
}

/**
 * Event handler for "hover" events on proof steps.
 * Adds or removes highlighting for the step.
 *
 * <p>Event is the mouse event.  Proof is the containing proof,
 * index is the step index, direction is "in" or "out", and
 * proofNode is the DOM node of the proof.
 */
function hoverStep(event, proof, index, direction, proofNode) {
  var inference = proof.steps[index];
  var iString = '' + (index + 1);
  var action = direction == 'in' ? addClass : removeClass;
  var deps = inference.deps;
  var handler = hoverHandlers[inference.name];
  // Always add or remove the "hover" class to the step node
  // as the mouse goes in or oiut.
  action(inference.getStepNode(), 'hover');
  
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
    handler(inference, action);
  } else {
    // If no handler apply or remove default highlighting.
    for (var key in deps) {
      action(deps[key].result.node, 'dep');
    }
  }
}

// Arguments to the handler functions are an inference
// and the operation is "addClass" or "removeClass".
var hoverHandlers = {
  r: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    var eqn = deps[args[0].asString()].result;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    action(target.node, 'hover');
    action(target.locate(path).node, 'old');
    action(inf.result.locate(path).node, 'new');
    action(eqn.getLeft().node, 'old');
    action(eqn.getRight().node, 'new');
  },
  rRight: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    var eqn = deps[args[0].asString()].result;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    action(target.node, 'hover');
    action(target.locate(path).node, 'old');
    action(inf.result.locate(path).node, 'new');
    action(eqn.getRight().node, 'old');
    action(eqn.getLeft().node, 'new');
  },
  axiom4: function(inf, action) {
    var call = inf.result.getLeft();
    action(call.arg.node, 'new');
    var target = call.fn.body;
    action(target.node, 'scope');
    action(inf.result.getRight().node, 'scope');
    var varName = call.fn.bound;
    target.findAll(varName,
                   function(v) { action(v.node, 'occur'); },
                   inf.result.getRight(),
                   function(expr) { action(expr.node, 'new'); });
  },
  reduce: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    var dep = deps[args[0].asString()].result;
    var path = args[1];
    var call = dep.locate(path);
    var target = call.fn.body;
    var varName = call.fn.bound.name;
    var result = inf.result.locate(path);
    action(dep.node, 'hover');
    action(call.arg.node, 'new');
    action(target.node, 'scope');
    action(result.node, 'scope');
    target.findAll(varName,
                   function(v) { action(v.node, 'occur'); },
                   result,
                   function(expr) { action(expr.node, 'new'); });
  },
  useDefinition: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    action(target.node, 'hover');
    action(target.locate(path).node, 'old');
    action(inf.result.locate(path).node, 'new');
  },
  instEqn: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = args[2].name;
    action(input.node, 'hover');
    input.findAll(varName,
                  function(_var) { action(_var.node, 'occur'); },
                  inf.result,
                  function(expr) { action(expr.node, 'new'); });
  },
  sub: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = args[2].name;
    action(input.node, 'hover');
    input.findAll(varName,
                  function(_var) { action(_var.node, 'new'); },
                  inf.result,
                  function(expr) { action(expr.node, 'new'); });
  },
  // TODO: subAll
  forallInst: function(inf, action) {
    var deps = inf.deps;
    var args = inf.arguments;
    // Input expression.
    var input = deps[args[0].asString()].result;
    // Name of variable being instantiated.
    var varName = input.arg.bound.name;
    action(input.node, 'hover');
    input.arg.body.findAll(varName,
                           function(_var) { action(_var.node, 'occur'); },
                           inf.result,
                           function(expr) { action(expr.node, 'new'); });
  }
};


//// OTHER UTILITY FUNCTIONS

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
 * of an object, and their values.  If "specials" is
 * given, it should be a map from key name to a function
 * for presenting the value of any key with that name.
 */
// TODO: Move this to expr.js.
function debugString(o, specials) {
  if (typeof o == 'object') {
    var result = '{';
    for (var key in o) {
      if (o.hasOwnProperty(key)) {
        if (result.length > 1) {
          result += ', ';
        }
        result += key + ': ';
        var value = o[key];
        var f = specials && specials[key];
        if (f) {
          result += f(value);
        } else if (typeof value == 'string') {
          result += '"' + o[key] + '"';
        } else if (value && value.concat) {
          // Array-like value.
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
// nested inferences using makeInference.  Each function here
// can have an "info" property with all the data from the ruleInfo
// object passed to createRules.
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
Y.isConstant = isConstant;
Y.renderInference = renderInference;
Y.createRules = createRules;
Y.addBottomPanel = addBottomPanel;
Y.debugString = debugString;
Y.getStepsNode = getStepsNode;
Y.getProofStep = getProofStep;
Y.getStepsNode = getStepsNode;
Y.getProof = getProof;
Y.getExpr = getExpr;
// TODO: Consider getting rid of this global variable.
Y.rules = rules;

// For testing:
Y.definitions = definitions;

}, '0.1', {requires: ['array-extras', 'expr', 'step-editor']});
