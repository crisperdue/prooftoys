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
  // a set (array) of selected steps.
  this.selections = [];
  this.selection = null;
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

/**
 * Construct a ProofControl given a DOM node and handler function for
 * selection events.  Instances must also have methods "select"
 * and "deselect".  Each takes a single DOM Node argument.
 */
function ProofControl(controlNode, proof, proofNode) {
  this.node = controlNode;
  this.proof = proof;
  this.proofNode = proofNode;
  // Only official "proof nodes" are permitted to have this class:
  proofNode.addClass('proofDisplay');
  this.editorButton = null;
  // Currently a YUI node, should become a widget.
  this.stepEditor = null;
}

ProofControl.prototype.handleStepClick = function(step) {
  var proof = this.proof;
  var selection = proof.selection;
  if (step == selection) {
    step.node.removeClass('selected');
    proof.selection = null;
  } else {
    if (selection) {
      selection.node.removeClass('selected');
    }
    step.node.addClass('selected');
    proof.selection = step;
  }
};

ProofControl.prototype.handleExprClick = function(expr) {
  var step = getProofStep(expr);
  var selection = step.selection;
  if (expr == selection) {
    selection.node.removeClass('selected');
    step.selection = null;
  } else {
    if (selection) {
      selection.node.removeClass('selected');
    }
    expr.node.addClass('selected');
    step.selection = expr;
  }
};


//// RENDERING AND EVENT HANDLING

/**
 * Renders the steps of the proof into the given DOM node,
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
  var proofNode = controller.proofNode;
  proofNode.setContent('');
  proofNode.setData('proof', proof);
  var steps = proof.steps;
  // Map from inference result string to inference.
  var allSteps = {};
  for (var i = 0; i < steps.length; i++) {
    var inf = steps[i];
    var text = '<div class=proofStep><span class=stepNumber>'
      + (i + 1) + '.</span> </div>';
    var stepNode = proofNode.appendChild(text);
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
           // Don't bubble the event up to the proof step.
           event.stopPropagation();
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
                Y.rbind(hover, null, proof, i, 'in', proofNode),
                Y.rbind(hover, null, proof, i, 'out', proofNode));

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
    renderInference(getTheorem(inference.arguments[0]), parent);
  } else {
    renderInference(inference, parent);
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
function renderInference(inference, node) {
  if (node == null) {
    node = new Y.Node(document.body);
  }
  var pruf = inference.arguments.length ? 'Rule ' : 'Proof of ';
  // var argInfo = inference.arguments.join(', ');
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
  var proofNode = node.appendChild('<div></div>');
  // Map to inference from its result as string.  Each result will be
  // annotated with links into the DOM.  Starts with the assumptions.
  // Add the assumptions to the proof before rendering it.
  var assumptions = inference.assumptions();
  for (var key in assumptions) {
    var wff = assumptions[key];
    inference.proof.add(makeInference('given', [wff]), 0);
  }
  var controller = new ProofControl(null, inference.proof, proofNode);
  renderSteps(controller);
  Y.on('mouseover', exprHandleOver, proofNode);
  Y.on('mouseout', exprHandleOut, proofNode);
  var div = node.appendChild('<div></div>');
  var buttonHtml =
    ('<input class=addStep type=button value="+" '
     + 'title="Add a step to the proof">');
  var button = div.appendChild(buttonHtml);
  button.on('click',
            function () {
              if (!(controller.stepEditor && controller.stepEditor.visible)) {
                showStepEditor(controller, controller.proof.steps.length);
              } else {
                controller.stepEditor.node.remove();
                button.set('value', '+');
                controller.stepEditor.visible = false;
                controller.stepEditor = null;
              }
            });
  controller.editorButton = button;
  return proofNode;
}

/**
 * Displays the proof step editor at the given index in the proof,
 * setting it as the stepEditor.  If the index is greater than the
 * index of any proof step, appends it at the end.
 */
function showStepEditor(controller, position) {
  if (!controller.stepEditor) {
    var div =
      ('<div class=stepEditor>Hello</div>');
    var editorNode;
    var steps = controller.proof.steps;
    if (position < steps.length) {
      var prevNode = steps[position].node;
      editorNode = prevNode.get('parentNode').insertBefore(div, prevNode);
    } else {
      editorNode =
        steps[steps.length - 1].node.get('parentNode').appendChild(div);
    }
    var input = editorNode.appendChild('<input class=ruleSelector>');
    var config = {resultFilters: ['startsWith'],
                  resultHighlighter: 'startsWith',
                  source: ['friends', 'romans', 'countrymen'],
                  inputNode: input,
                  render: true
    };
    var ac = new Y.AutoComplete(config);
    // On Enter key press select the active item. If no item is active but
    // there is just one result make it active first.
    ac._keysVisible[13] = function () {
      var item = this.get('activeItem');
      var results = this.get('results');
      if (!item && results.length == 1) {
        this._keyDown();
        item = this.get('activeItem');
      }
      if (item) {
        this.selectItem(item);
      } else {
        // Don't prevent form submission when there's no active item.
        return false;
      }
    };

    // TODO: Decide what to store in the controller.
    editorNode.node = editorNode;
    editorNode.visible = true;
    controller.stepEditor = editorNode;
    controller.editorButton.set('value', '-');
  }
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
function getProofNode(node) {
  return node.ancestor('.proofDisplay', true);
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
  return getProofNode(node).getData('proof');
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
  // TODO: subAll
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
Y.isConstant = isConstant;
Y.renderInference = renderInference;
Y.createRules = createRules;
Y.addBottomPanel = addBottomPanel;
Y.debugString = debugString;
Y.getProofNode = getProofNode;
Y.getProofStep = getProofStep;
Y.getProofNode = getProofNode;
Y.getProof = getProof;
Y.getExpr = getExpr;
// TODO: Consider getting rid of this global variable.
Y.rules = rules;

// For testing:
Y.definitions = definitions;

}, '0.1', {requires: ['array-extras', 'expr', 'autocomplete',
                      'autocomplete-filters', 'autocomplete-highlighters']});
