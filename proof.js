// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

//// THEOREMHOOD

// Private to addTheorem, getTheorem, and the initializations
// at the bottom of this file.  Maps from name to an inference
// containing a proof of the theorem, or true, indicating
// 
var _theoremsByName = {};

/**
 * Checks that the theorem is not already in the database, then adds a
 * function to prove it to the set of theorems, which are indexed by
 * theorem name.
 */
function addTheorem(name) {
  Y.assert(!_theoremsByName[name], 'Theorem already exists: ' + name);
  Y.assert(rules[name], 'No proof: ' + name);
  _theoremsByName[name] = true;
}

/**
 * Gets an existing theorem from the theorems database, or returns
 * null if there is none.  Runs the proof if it has not already run.
 */
function getTheorem(name) {
  var value = _theoremsByName[name];
  if (value == true) {
    value = _theoremsByName[name] = rules[name]();
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
  // TODO: Check for indirectly-circular definitions.
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
 * database.  Throws an exception if an appropriate definition is not
 * found.  Pass true or false or T or F to get the appropriate part of
 * a definition by cases.
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
  // Steps (Exprs) in order.
  this.steps = [];
}

/**
 * Add a step to this proof, optionally specifying its
 * index.  Default location is at the end.
 */
Proof.prototype.add = function(step, index) {
  if (index == null) {
    this.steps.push(step);
  } else {
    this.steps.splice(index, 0, step);
  }
};

Proof.prototype.setSteps = function(steps) {
  this.steps = steps;
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
  // Confirm that there are no assumptions required.
  var steps = this.steps;
  for (var i = 0; i < steps.length; i++) {
    var step = steps[i];
    if (step.ruleName == 'assumption') {
      return false;
    }
  }
  return true;
}


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
  step.stepNode.addClass('selected');
  this.selection = step;
};

/**
 * Unconditionally deselect any selected step and any
 * selected expression in it.
 */
ProofControl.prototype.deselectStep = function() {
  var step = this.selection;
  if (step) {
    step.stepNode.removeClass('selected');
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
  var stepsNode = controller.stepsNode;
  stepsNode.setContent('');
  var steps = controller.proof.steps;
  for (var i = 0; i < steps.length; i++) {
    var step = steps[i];
    var text = '<div class=proofStep><span class=stepNumber>'
      + step.stepNumber + '.</span></div>';
    var stepNode = stepsNode.appendChild(text);
    stepNode.setData('proofStep', step);
    step.stepNode = stepNode;
    // Render the WFF and record the rendered copy as the inference
    // result.  Rendering guarantees to copy every step that it
    // renders.
    var wffNode = step.render();
    stepNode.appendChild(wffNode);

    // Set the property here until we stop using copyProof:
    step.original.rendering = step;

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
                
    var stepInfo = computeStepInfo(step);
    stepNode.appendChild('<span class=stepInfo>' + stepInfo + '</span>');
    // Set up "hover" event handling on the stepNode.
    stepNode.on('hover',
                // Call "hover", passing these arguments as well as the event.
                Y.bind(hoverStep, null, step, 'in', stepsNode),
                Y.bind(hoverStep, null, step, 'out', stepsNode));

    // Caution: passing null to Y.on selects everything.
    var target = stepNode.one('span.ruleName');
    if (target) {
      target.on('click', Y.rbind(function(event, step) {
            renderSubProof(event, step, stepsNode, controller.editable);
            // Don't give the proof step a chance to select itself.
            event.stopPropagation();
          }, null, step));
    }
  }
};

/**
 * Returns an array of copies of the steps leading from the limits to
 * the given step.  If limits are given, copies of them are not
 * included in the result.  Sorts the copies by ordinal of the
 * originals.  Each copy has an "original" property that refers to its
 * original.
 */
function copySubproof(step, limits) {
  limits = limits || [];
  var copies = [];
  Y.each(limits, function(limit) { limit.__copied = true; });
  // Traverses the dependency graph, recording a copy of every step
  // and building an array of all of the original steps.  In Java
  // one might use HashMaps to associate the copies with the original,
  // avoiding temporary modifications to the originals.
  function graphWalk(step) {
    if (!step.__copied) {
      step.__copied = true;
      var copy = step.copy();
      copy.original = step;
      copies.push(copy);
      Y.each(step.ruleDeps, function(dep) { graphWalk(dep); });
    }
  }
  graphWalk(step);
  Y.each(limits, function(limit) { delete limit.__copied; });
  Y.each(copies, function(copy) { delete copy.original.__copied; });
  copies.sort(function(s1, s2) {
      return s1.original.ordinal - s2.original.ordinal;
    });
  return copies;
}

// TODO: implement.
function renderSubproof(step, limits, node) {
  
}

/**
 * Finds all the proof steps supporting the given one at its level in
 * the proof and returns copies of all of them as an array, including
 * the given one, ordered by their ordinals.  This produces a copy of
 * the proof graph and a deep copy of every step, making the result
 * ready for rendering.  Copies no further back in the proof than any
 * of the given steps.
 */
function copyProof(step, dependencies) {
  baseDeps = Y.Array.map(dependencies, function(dep) {
      return dep.getBase();
    });
  var oldSteps = [];
  // Traverses the dependency graph, recording a copy of every step
  // and building an array of all of the original steps.  In Java
  // one might use HashMaps to associate the copies with the orginal,
  // avoiding temporary modifications to the originals.
  function graphWalk(step) {
    if (!step.__copy) {
      step.__copy = step.copyStep();
      oldSteps.push(step);
      for (var i = 0; i < baseDeps.length; i++) {
        // If this step is a dependency of the original, don't walk
        // back further.
        if (step.getBase() == baseDeps[i]) {
          // In the copy treat the dependency as an assumption.
          step.__copy.assume();
          return;
        }
      }
      Y.each(step.ruleDeps, function(dep) { graphWalk(dep); });
    }
  }
  graphWalk(step);
  // Make a copy of the steps array, with a copy in place of each
  // old step, updating each copy's dependencies and arguments to refer to
  // appropriate new copies as well.
  var result = [];
  Y.each(oldSteps, function(oldStep) {
      var copy = oldStep.__copy;
      copy.original = oldStep;
      var deps = [];
      // The copy might have been converted to an assumption, and in
      // that case it already has the correct empty lists of dependencies
      // and arguments.
      if (copy.ruleName != 'assumption') {
        copy.ruleDeps =
          Y.Array.map(oldStep.ruleDeps, function(dep) {
              Y.assert(dep.__copy, 'No copy available: ' + Y.debugString(dep));
              Y.assert(dep.__copy.ruleName,
                       'No ruleName: ' + Y.debugString(dep.__copy));
              return dep.__copy;
            });
        copy.ruleArgs =
          Y.Array.map(oldStep.ruleArgs, function(arg) {
              // If the arg is a step, it should have a copy,
              // use the copy.
              return arg.__copy || arg;
            });
      }
      result.push(copy);
    });
  // Sort the result by the step ordinals.
  result.sort(function(s1, s2) { return s1.ordinal - s2.ordinal; });
  // Clean up references to the copies.
  Y.each(oldSteps, function(step) { delete step.__copy; });
  return result;
}

/**
 * Renders the given inference and a header after
 * the given proof Node, clearing any other subproofs
 * that currently follow the proof node.
 */
function renderSubProof(event, step, proofNode, editable) {
  var display = proofNode.ancestor('.proofDisplay');
  var parent = display.get('parentNode');
  var next = display.get('nextSibling');
  while (next) {
    next.remove();
    next = display.get('nextSibling');
  }
  if (step.ruleName == 'theorem') {
    renderInference(getTheorem(step.ruleArgs[0]), parent, editable);
  } else {
    renderInference(step, parent, editable);
  }
}

/**
 * Computes and returns a string of HTML with information about
 * the given proof step.
 */
function computeStepInfo(step) {
  var expr = step;
  var stepInfo;
  if (expr.ruleName == 'definition') {
    stepInfo = 'definition of ';
    if (expr.ruleArgs.length == 2) {
      stepInfo += expr.ruleArgs[1] + ' ';
    }
    stepInfo += expr.ruleArgs[0];
  } else {
    if (expr.details) {
      // It is a (derived) rule of inference.
      stepInfo = fancyName(expr);
    } else {
      // It is a primitive rule of inference (Rule R).
      stepInfo = expr.ruleName;
    }

    // Display dependencies on other steps.
    var firstDep = true;
    Y.each(expr.ruleDeps, function(dep) {
        if (firstDep) {
          firstDep = false;
        } else {
          stepInfo += ',';
        }
        stepInfo += ' ' + fancyStepNumber(dep.stepNumber);
      });

    // Display rule arguments.
    var args = expr.ruleArgs;
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
function fancyName(expr) {
  var name = expr.ruleName;
  var info = rules[name].info;
  var comment = info.comment || '';
  return '<span class=ruleName title="' + comment + '">' + name + '</span>';
}

/**
 * Renders a step number in a fancy way, currently in a SPAN
 * with class "stepNumber".
 */
function fancyStepNumber(n) {
  return '<span class=stepNumber>' + n + '</span>';
}

/**
 * Renders a header and the proof steps of an inference by appending
 * them to a container Node, which defaults to the document body.  The
 * first child is the header, rendered with class proofHeader.  The
 * second is the proof display.  Returns the final step of the rendered
 * copy.
 *
 * Inputs are a proof step, the container node, a flag to indicate
 * whether to make the display editable, and an optional proof time in
 * milliseconds.  This renders the details of the step and a
 * description of the step itself.
 */
function renderInference(step, node, editable, millis) {
  if (node == null) {
    node = new Y.Node(document.body);
  }
  var pruf = step.ruleArgs.length ? 'Rule ' : 'Proof of ';
  var argInfo = '';
  for (var i = 0; i < step.ruleArgs.length; i++) {
    if (i > 0) {
      argInfo += ', ';
    }
    var arg = step.ruleArgs[i];
    if (typeof arg == 'string'
        || arg instanceof Y.Expr
        || arg instanceof Y.Path) {
      argInfo += arg;
    } else {
      argInfo += debugString(arg);
    }
  }
  argInfo =
    ': <span style="font-weight: normal; font-family: monospace">'
    + argInfo + '</span>';
  // TODO: Clean up relationships between Proof, ProofControl,
  // and steps.  Consider merging Proof into ProofControl.
  var startRender = new Date().getTime();
  var steps = copyProof(step.details, step.ruleDeps);
  var nSteps = steps[steps.length - 1].ordinal - computeFirstOrdinal(steps);
  // Give the steps numbers from 1 to N.
  Y.each(steps, function(step, i) {
      step.stepNumber = Y.showOrdinals ? step.ordinal : i + 1;
    });
  var proof = new Proof();
  proof.setSteps(steps);
  var controller = new ProofControl(proof);
  var renderTime = Math.ceil(new Date().getTime() - startRender);

  var comment = rules[step.ruleName].info.comment || '';
  var stats = '';
  if (millis != null) {
    stats = '<br><i style="font-size:smaller; color:gray">Proof '
      + Math.ceil(millis) + ' msec, rendering '
      + renderTime + ' msec, ' + nSteps + ' steps</i>';
  }
  node.appendChild('<div class=proofHeader><b>' + pruf
                   + step.ruleName + '</b>' + argInfo + '<br>'
                   + '<i>' + comment + '</i>' + stats
                   + '</div>');
  node.append(controller.node);
  controller.setEditable(editable);
  return steps[steps.length - 1];
}

/**
 * Computes the lowest real ordinal of a set of steps.
 * TODO: Eliminate this when there are no more artificial ordinals
 * due to creating assumptions after the fact.
 */
function computeFirstOrdinal(steps) {
  var lowest = 0;
  for (var i = 0; i < steps.length; i++) {
    var lowest = steps[i].getBase().ordinal;
    if (lowest >= 1) {
      return lowest;
    }
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
 * Gets the proof step (Expr) of the step that renders
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
 * Returns the expression associated with a YUI node.
 */
function getExpr(node) {
  // Go up to the proof step then look through all subexpressions.
  var step = getProofStep(node);
  return step.search(function (expr) { return expr.node == node; },
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
    var path = proofStep.pathTo(isTarget);
    hoverShowPath(proofStep, path);
  }
};

/**
 * Defines how to display the hovered path.  Highlighting of the
 * DOM node is handled elsewhere.
 */
function hoverShowPath(wff, path) {
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
function hoverStep(step, direction, proofNode, event) {
  var action = direction == 'in' ? addClass : removeClass;
  // Always add or remove the "hover" class to the step node
  // as the mouse goes in or oiut.
  action(getStepNode(step.node), 'hover');
  
  // When entering a step, highlight all references to it.
  // When leaving remove highlights from all references.
  proofNode.all('span.stepNumber').each(function(node) {
      if (direction == 'in') {
        if (node.get('innerHTML') == step.stepNumber) {
          node.addClass('referenced');
        }
      } else {
        node.removeClass('referenced');
      }
    });
  var handler = hoverHandlers[step.ruleName];
  if (handler) {
    // If there is a hover handler for this type of inference, apply it.
    handler(step, action);
  } else {
    // If no handler apply or remove default highlighting.
    Y.each(step.ruleDeps, function(dep) {
        action(dep.node, 'dep');
      });
  }
}

// Arguments to the handler functions are an inference
// and the operation is "addClass" or "removeClass".
var hoverHandlers = {
  r: function(step, action) {
    var args = step.original.ruleArgs;
    var eqn = args[0].rendering;
    var target = args[1].rendering;
    var path = args[2];
    action(target.node, 'hover');
    action(target.locate(path).node, 'old');
    action(step.locate(path).node, 'new');
    action(eqn.getLeft().node, 'old');
    action(eqn.getRight().node, 'new');
  },
  rRight: function(step, action) {
    var args = step.original.ruleArgs;
    var eqn = args[0].rendering;
    var target = args[1].rendering;
    var path = args[2];
    action(target.node, 'hover');
    action(target.locate(path).node, 'old');
    action(step.locate(path).node, 'new');
    action(eqn.getRight().node, 'old');
    action(eqn.getLeft().node, 'new');
  },
  axiom4: function(step, action) {
    var call = step.getLeft();
    action(call.arg.node, 'new');
    var target = call.fn.body;
    action(target.node, 'scope');
    action(step.getRight().node, 'scope');
    var varName = call.fn.bound;
    target.findAll(varName,
                   function(v) { action(v.node, 'occur'); },
                   step.getRight(),
                   function(expr) { action(expr.node, 'new'); });
  },
  reduce: function(step, action) {
    var args = step.original.ruleArgs;
    var dep = args[0].rendering;
    var path = args[1];
    var call = dep.locate(path);
    var target = call.fn.body;
    var varName = call.fn.bound.name;
    var result = step.locate(path);
    action(dep.node, 'hover');
    action(call.arg.node, 'new');
    action(target.node, 'scope');
    action(result.node, 'scope');
    target.findAll(varName,
                   function(v) { action(v.node, 'occur'); },
                   result,
                   function(expr) { action(expr.node, 'new'); });
  },
  useDefinition: function(step, action) {
    var args = step.original.ruleArgs;
    var target = args[1].rendering;
    var path = args[2];
    action(target.node, 'hover');
    action(target.locate(path).node, 'old');
    action(step.locate(path).node, 'new');
  },
  instEqn: function(step, action) {
    var args = step.original.ruleArgs;
    // Input expression.
    var input = args[0].rendering;
    // Name of variable being instantiated.
    var varName = args[2].ruleName;
    action(input.node, 'hover');
    input.findAll(varName,
                  function(_var) { action(_var.node, 'occur'); },
                  step,
                  function(expr) { action(expr.node, 'new'); });
  },
  sub: function(step, action) {
    var args = step.original.ruleArgs;
    // Input step.
    var input = args[0].rendering;
    // Name of variable being instantiated.
    var varName = args[2].name || args[2];
    action(input.node, 'hover');
    input.findAll(varName,
                  function(_var) { action(_var.node, 'occur'); },
                  step,
                  function(expr) { action(expr.node, 'new'); });
  },
  // TODO: subAll
  forallInst: function(step, action) {
    var args = step.original.ruleArgs;
    // Input expression.
    var input = args[0].rendering;
    // Name of variable being instantiated.
    var varName = input.arg.bound.name;
    action(input.node, 'hover');
    input.arg.body.findAll(varName,
                           function(_var) { action(_var.node, 'occur'); },
                           step,
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
    // Remember ALL of the info as well, redundantly.  See the "to do"
    // above.
    var info = ruleInfo[key];
    var fn = (typeof info == 'function') ? info : info.action;
    // Each function in rules has its action function as
    // the value of its innerFn property.
    rules[key] = fn;
    rules[key].info = info;
  }
}


//// Export public names.

Y.showOrdinals = false;
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
Y.getExpr = getExpr;
// TODO: Consider getting rid of this global variable.
Y.rules = rules;

// For testing:
Y.definitions = definitions;

}, '0.1', {requires: ['array-extras', 'expr', 'step-editor']});
