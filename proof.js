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

//// PROOF CONTROL

// TODO: Extend these to support proof steps that can take more
// than one selection.

/**
 * Construct a ProofControl.  No arguments.
 *
 * Properties:
 *
 * steps: an array of the _rendered_ steps (Expr objects) displayed.
 * node: Node containing the entire rendering of the proof.
 * stepsNode: Node containing all of the rendered steps as children.
 * editorButton: step insertion button, or null.
 */
function ProofControl() {
  var controller = this;
  this.steps = [];
  // Set (array) of selected steps.
  // TODO: Implement this.
  this.selections = [];
  // Single selected step when exactly one is selected, or null.
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
  // Set up handling of mouseover and mouseout events.
  Y.on('mouseover', exprHandleOver, this.node);
  Y.on('mouseout', exprHandleOut, this.node);
}

/**
 * Sets the steps of the current proof to be the ones in the given array,
 * which should contain only unrendered steps.  Sets their stepNumber properties
 * to run from 1 to N and renders them.  The rendered copies become the accessible
 * steps of the ProofControl.
 */
ProofControl.prototype.setSteps = function(steps) {
  var rendered = Y.Array.map(steps, function(step) {
      var copy = step.copyStep();
      step.rendering = copy;
      copy.original = step;
      return copy;
    });
  // Clear presentation of any old steps.
  var stepsNode = this.stepsNode;
  Y.Array.each(this.steps, function(step) {
      step.original.rendering = null;
    });
  stepsNode.setContent('');
  // Now render the desired steps.
  this.steps = rendered;
  for (var i = 0; i < steps.length; i++) {
    var stepNode = renderStep(rendered[i], this);
    stepsNode.append(stepNode);
  }
  this._renumber();
};

/**
 * Gives the steps numbers from 1 to N, or each its ordinals if
 * showOrdinals flag is true and updates displays of them.
 */
ProofControl.prototype._renumber = function() {
  // Give the steps numbers from 1 to N.
  Y.each(this.steps, function(step, i) {
    // Fix up the step number and its display.
    step.stepNumber = Y.showOrdinals ? step.ordinal : i + 1;
    renderStepNumber(step);
  });
  // TODO: This will also need to support renumbering of any step
  // detail displays.
};  

function renderStepNumber(step) {
  step.stepNode.one('.stepNumber')
    .setContent(document.createTextNode(step.stepNumber + '. '));
  // Fix up references made by the step.  (These should all be prior
  // steps.)
  Y.each(step.stepNode.all('.stepReference'), function(ref, j) {
    ref.setContent(step.original.ruleDeps[j].rendering.stepNumber);
  });
}

/**
 * Adds the given unrendered (top-level) proof step into the control's
 * proof, rendering it and assigning it the stepNumber for its
 * position.
 */
ProofControl.prototype.addStep = function(step) {
  var copy = step.copyStep();
  step.rendering = copy;
  copy.original = step;
  copy.stepNumber = Y.showOrdinals ? step.ordinal : this.steps.length + 1;
  var stepNode = renderStep(copy, this);
  renderStepNumber(copy);
  this.stepsNode.append(stepNode);
};

/**
 * Remove from the proof display the given top-level rendered proof
 * step and all steps that depend on it.
 */
ProofControl.prototype.removeStep = function(toRemove) {
  var original = toRemove.original;
  var steps = this.steps;
  var dependent;
  while (true) {
    dependent = Y.Array.find(steps, function(step) {
      return contains(step.original.ruleDeps, original);
    });
    if (!dependent) {
      break;
    }
    this.removeStep(dependent);
  }
  toRemove.stepNode.remove();
  delete toRemove.original.rendering;
  this.steps.splice(Y.Array.indexOf(steps, toRemove), 1);
  // this._renumber();
};

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
};

ProofControl.prototype.hideStepEditor = function() {
  this.stepEditor.node.remove();
  this.stepEditor.reset();
  this.deselectStep();
  this.editorButton.set('disabled', false);
  this.editorVisible = false;
};

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


// INTERNAL TO PROOFCONTROL

/**
 * Create and return a YUI node to display the step within the
 * given controller.  The step should be renderable, including
 * a stepNumber property.  This also sets up event handlers for
 * click and hover events within the step.  The caller must
 * insert the new node into the document.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression has a "node" property that refers
 *   to a YUI node with its rendering.
 * - Each proofStep YUI node has a proofStep data property that refers
 *   to the Inference (proof step) it represents.
 */
function renderStep(step, controller) {
  var stepsNode = controller.stepsNode;
  // stepNumber may be filled in later with an actual number.
  var html = '<div class=proofStep><span class=stepNumber>. </span></div>';
  var stepNode = Y.Node.create(html);
  var n = step.stepNumber;
  if (n != null) {
    stepNode.one('.stepNumber').setContent(n);
  }
  stepNode.setData('proofStep', step);
  step.stepNode = stepNode;
  // Render the WFF and record the rendered copy as the inference
  // result.  Rendering guarantees to copy every step that it
  // renders.
  var wffNode = step.render();
  stepNode.appendChild(wffNode);

  // TODO: Consider up these handlers in an ancestor node by delegation.
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
          renderSubProof(event, step, stepsNode);
          // Don't give the proof step a chance to select itself.
          event.stopPropagation();
        }, null, step));
  }
  return stepNode;
}

/**
 * Returns an array of the unrendered steps leading up to and
 * including the given step, sorted by ordinal.  Helper function
 * internal to renderInference.  The "unrendered" aspect is helpful
 * for rendering subproofs.
 */
function unrenderedDeps(step) {
  var result = [];
  // Traverses the dependency graph, recording a copy of every step
  // and building an array of all of the original steps.  In Java
  // one might use HashSets to identify already-visited steps,
  // avoiding temporary modifications to the originals.
  function visitWithDeps(step) {
    if (!step.rendering && !step.__visited) {
      result.push(step);
      step.__visited = true;
      Y.each(step.ruleDeps, function(dep) { visitWithDeps(dep); });
    }
  }
  visitWithDeps(step);
  Y.Array.each(result, function(step) { delete step.__visited; });
  result.sort(function(s1, s2) {
      return s1.ordinal - s2.ordinal;
    });
  return result;
}

/**
 * Renders the given inference and a header after
 * the given proof Node, clearing any other subproofs
 * that currently follow the proof node.
 */
function renderSubProof(event, step, proofNode) {
  var display = proofNode.ancestor('.proofDisplay');
  var parent = display.get('parentNode');
  var next = display.get('nextSibling');
  while (next) {
    // TODO: Get rid of this hack soon.
    // BEGIN HACK:
    // Clear out all of the renderings of the original steps
    // rendered in here.
    next.all('div.proofStep').each(function(stepNode) {
        stepNode.getData('proofStep').original.rendering = null;
      });
    // END HACK.
    next.remove();
    next = display.get('nextSibling');
  }
  if (step.ruleName == 'theorem') {
    renderInference(getTheorem(step.ruleArgs[0]), parent, false);
  } else {
    renderInference(step, parent, false);
  }
}

/**
 * Computes and returns a string of HTML with information about
 * the given proof step.
 */
function computeStepInfo(step) {
  var stepInfo;
  if (step.ruleName == 'definition') {
    stepInfo = 'definition of ';
    if (step.ruleArgs.length == 2) {
      stepInfo += step.ruleArgs[1] + ' ';
    }
    stepInfo += step.ruleArgs[0];
  } else {
    if (step.details) {
      // It is a (derived) rule of inference.
      stepInfo = fancyName(step);
    } else {
      // It is a primitive rule of inference (Rule R).
      stepInfo = step.ruleName;
    }

    // Display dependencies on other steps.
    var firstDep = true;
    Y.each(step.ruleDeps, function(dep, i) {
      if (i > 0) {
        stepInfo += ',';
      }
      // This gets filled in later with the referenced step number.
      stepInfo += ' <span class=stepReference></span>';
    });

    // Display rule arguments.
    var args = step.ruleArgs;
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
 * Renders a header and the proof steps of an inference by appending
 * them to a container Node, which defaults to the document body.  The
 * first child is the header, rendered with class proofHeader.  The
 * second is the proof display.
 *
 * Inputs are a proof step, the container node, a flag to indicate
 * whether to make the display editable, and an optional proof time in
 * milliseconds (elapsed time of proof execution).  This renders the
 * details of the step and a description of the step itself.
 *
 * Returns the ProofController.
 */
function renderInference(step, node, editable, millis) {
  var startRender = new Date().getTime();
  var steps = unrenderedDeps(step.details);
  var nSteps = steps[steps.length - 1].ordinal - computeFirstOrdinal(steps);
  var controller = new ProofControl();
  controller.setSteps(steps);
  var renderTime = Math.ceil(new Date().getTime() - startRender);
  var comment = rules[step.ruleName].info.comment || '';
  var stats = '';
  if (millis != null) {
    stats = '<br><i style="font-size:smaller; color:gray">Proof '
      + Math.ceil(millis) + ' msec, rendering '
      + renderTime + ' msec, ' + nSteps + ' steps</i>';
  }
  var pruf = step.ruleArgs.length ? 'Rule ' : 'Proof of ';
  node.appendChild('<div class=proofHeader><b>' + pruf
                   + step.ruleName + '</b>' + computeArgInfo(step) + '<br>'
                   + '<i>' + comment + '</i>' + stats
                   + '</div>');
  node.append(controller.node);
  controller.setEditable(editable);
  return controller;
}

/**
 * Helper for renderInference, computes arguments display string of a step.
 */
function computeArgInfo(step) {
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
  return argInfo;
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
  proofNode.all('span.stepReference').each(function(node) {
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
        action(dep.rendering.node, 'dep');
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

function contains(collection, item) {
  return Y.Array.indexOf(collection, item) >= 0;
}

/**
 * Generic function to add a node to a YUI node at a position, with
 * numbering that starts at 0.
 */
function addChild(parent, position, node) {
  var children = parent.get('children');
  if (position == children.length) {
    parent.appendChild(node);
  } else {
    parent.insertBefore(node, children[position]);
  }
}

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
 * properly.  If not supplied in the rule definition, the info.input
 * is defaulted to an empty object here.
 */
function createRules(ruleInfo) {
  for (var key in ruleInfo) {
    // Remember ALL of the info as well, redundantly.  See the "to do"
    // above.
    var info = ruleInfo[key];
    if (!info.inputs) {
      info.inputs = {};
    }
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
