// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Use the application's assert function.
var assert = Y.assertTrue;

//// PROOF CONTROL

// TODO: Extend these to support proof steps that can take more
// than one selection.

/**
 * Construct a ProofControl.  No arguments.
 *
 * Properties:
 *
 * steps: an array of the _rendered_ steps displayed.
 * node: Node containing the entire rendering of the proof.
 * stepsNode: Node containing all of the rendered steps as children.
 *
 * A step is an Expr, either rendered or unrendered.  Unrendered steps
 * are the top-level expressions of a proof, with properties added by
 * Expr.justify.  Rendered steps have properties "node" (a YUI node
 * with the step's display) and "original" referring to the unrendered
 * proof step from which the rendered step was created.  Creation of a
 * rendered step adds a "rendering" property to the original, so
 * original proof steps can currently have only one rendering at a time.
 *
 * Note that the stepNumber property of a step depends on its position
 * in its ProofControl's steps array, so it must be a property of a
 * _rendered_ step.
 *
 * TODO: Consider supporting a set of renderings per unrendered proof
 * step.
 */
function ProofControl() {
  var controller = this;
  this.steps = [];
  // Set (array) of selected steps.
  // TODO: Implement this.
  this.selections = [];
  // Single selected step when exactly one is selected, or null.
  this.selection = null;

  // ID of element to use for saving/restoring proof state,
  // settable, normally as part of initial setup of the control.
  this.textAreaId = 'proofState';

  // Only official "proof nodes" are permitted to have class proofDisplay.
  html =
    '<table class=proofDisplay><tr><td><div class=proofSteps></div></table>';
  this.node = Y.Node.create(html);
  // Potentially useful for debugging.
  this.node.setData('proofControl', this);
  this.stepsNode = this.node.one('.proofSteps');
  this.stepEditor = new Y.StepEditor(this);
  this.node.one('td').append(this.stepEditor.node);

  var html = ('<input class=addStep type=button value="+" '
              + 'title="Add a step to the proof">');
  this.setEditable(false);
  // Set up handling of mouseover and mouseout events.
  Y.on('mouseover', exprHandleOver, this.node);
  Y.on('mouseout', exprHandleOut, this.node);
}

/**
 * Sets the steps of the current proof to be the ones in the given
 * array, which should contain only renderable steps.  Sets their
 * stepNumber properties to run from 1 to N and renders them.  The
 * rendered copies become the value of the steps property of the
 * ProofControl.
 */
ProofControl.prototype.setSteps = function(steps, record) {
  // Clear rendering properties of current steps, as they will be
  // deleted.
  var stepsNode = this.stepsNode;
  Y.Array.each(this.steps, function(step) {
    step.original.rendering = null;
  });
  stepsNode.setContent('');
  // Now render the desired steps.
  this.steps = [];
  for (var i = 0; i < steps.length; i++) {
    this.addStep(steps[i]);
  }
  this._renumber();
  if (arguments < 2 || record) {
    this.recordSteps();
  }
};

/**
 * Gives the steps numbers from 1 to N, or each its ordinal if
 * showOrdinals flag is true.  Updates step number display of each.
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

/**
 * Render's the step number into its element of class "stepNumber",
 * and fixes up its elements of class "stepReference" to contain the
 * stepNumber of the correspondindg dependency.
 */
function renderStepNumber(step) {
  step.stepNode.one('.stepNumber')
    .setContent(document.createTextNode(step.stepNumber + '. '));
  // Fix up references made by the step.  (These should all be prior
  // steps.)
  Y.each(step.stepNode.all('.stepReference'), function(ref, j) {
    ref.setContent(step.original.ruleDeps[j].rendering.stepNumber);
  });
  // TODO: Consider fixing up references to hypotheses here.
}

/**
 * Adds the given unrendered (top-level) proof step to the end of the
 * control's proof, rendering it and assigning it the stepNumber for
 * its position in this ProofControl's steps (rendered steps).
 */
ProofControl.prototype.addStep = function(step) {
  // TODO: Move most of this logic into renderStep.
  var copy = step.copyStep();
  step.rendering = copy;
  copy.original = step;
  this.steps.push(copy);
  copy.stepNumber = Y.showOrdinals ? step.ordinal : this.steps.length;
  var stepNode = renderStep(copy, this);
  renderStepNumber(copy);
  this.stepsNode.append(stepNode);
};

/**
 * Finds a step belonging to this ProofControl that has the original
 * of the given step as one of its dependents; or null if none found.
 */
ProofControl.prototype.findDependent = function(target) {
  var original = target.original;
  for (var i = 0; i < this.steps.length; i++) {
    var step = this.steps[i];
    if (step.ruleDeps.indexOf(original) >= 0) {
      return step;
    }
  }
  return null;
};

/**
 * Unconditionally remove the rendered step from this controller,
 * deselecting it if selected.  Does not update other steps in
 * any way.
 */
ProofControl.prototype._removeStep = function(toRemove) {
  if (this.selection == toRemove) {
    this.deselectStep();
  }
  toRemove.stepNode.remove();
  delete toRemove.original.rendering;
  this.steps.splice(this.steps.indexOf(toRemove), 1);
};

/**
 * Remove from the proof display the given top-level rendered proof
 * step and all other steps of the display that depend on it directly
 * or indirectly.
 *
 * TODO: Complete this by updating remaining steps appropriately
 *   and clearing subproofs.
 */
ProofControl.prototype.removeStepAndDeps = function(toRemove) {
  var dependent;
  while (dependent = this.findDependent(toRemove)) {
    this.removeStepAndDeps(dependent);
  }
  this._removeStep(toRemove);
};

/**
 * Remove from the proof display the given top-level rendered proof
 * step and all other steps of the display that come after it.
 *
 * TODO: Clear subproofs, see renderSubProof. 
 */
ProofControl.prototype.removeStepAndFollowing = function(toRemove) {
  var index = this.steps.indexOf(toRemove);
  var steps = this.steps;
  // Remember the current length.
  var length = steps.length;
  for (var i = index; i < length; i++) {
    // Don't change the index - each iteration deletes a step.
    this._removeStep(steps[index]);
  }
};

/**
 * Makes the control editable or not by showing/hiding the
 * editor button and flagging its state.
 */
ProofControl.prototype.setEditable = function(state) {
  this.editable = state;
  var node = this.stepEditor.node;
  if (state) {
    node.show();
  } else {
    node.hide();
  }
}


// SAVING AND RESTORING STATE

/**
 * In case there is a textarea with the proof control's configured ID
 * on the page, save the proof state to it.
 */
ProofControl.prototype.saveState = function() {
  var node = Y.one('textarea#' + this.textAreaId);
  if (!node) {
    return;
  }
  node.set('value', Y.encodeSteps(this.steps));
};

/**
 * In case there is a textarea with the proof control's configured ID
 * on the page, restore the proof state from it.
 */
ProofControl.prototype.restoreState = function() {
  var node = Y.one('textarea#' + this.textAreaId);
  if (!node) {
    return;
  }
  var steps;
  try {
    var value = node.get('value');
    assert(value, 'No proof state recorded');
    steps = Y.decodeSteps(value);
  } catch(err) {
    window.alert('Failed to parse proof state: ' + err.message);
    throw err;
  }
  this.setSteps(steps);
};


// STEP SELECTION

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
  if (this.editable) {
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
  if (this.editable) {
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
 * Create and return a YUI node to display the step (justified Expr)
 * within the given controller.  The step should be renderable.  This
 * also sets up event handlers for click and hover events within the
 * step.  Does not insert the new node into the document.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression and subexpression has a "node" property
 *   that refers to a YUI node with its rendering.
 * - Each proofStep YUI node has a proofStep data property that refers
 *   to the Inference (proof step) it represents.
 */
function renderStep(step, controller) {
  var stepsNode = controller.stepsNode;
  var deleter = (controller.editable
                 ? ('<input type=button class=deleteStep value="x"' +
                    ' title="Delete step">')
                 : '');
  var html = ('<div class=proofStep>' +
              deleter +
              '<span class=stepNumber>. </span>' +
              '<span class=wff></span>' +
              '<span class=stepInfo></span>' +
              '</div>');
  var stepNode = Y.Node.create(html);
  var n = step.stepNumber;
  stepNode.one('.stepNumber').setContent(n);
  stepNode.setData('proofStep', step);
  step.stepNode = stepNode;
  var wffNode = step.render(true);
  stepNode.one('.wff').setContent(wffNode);

  // TODO: Consider up these handlers in an ancestor node by delegation.
  // Set up click handlers for selections within the step.
  wffNode.on('mousedown',
       // This implements a policy of one selection per proof step.
       // TODO: Implement such policies in the proof controller.
       function(event) {
         controller.handleExprClick(getExpr(event.target));
       });
  stepNode.on('mousedown',
       function(event) {
         controller.handleStepClick(getProofStep(event.target));
       });

  stepNode.one('.stepInfo').setContent(computeStepInfo(step));
  // Set up "hover" event handling on the stepNode.
  stepNode.on('hover',
              // Call "hover", passing these arguments as well as the event.
              Y.bind(hoverStep, null, step, 'in', stepsNode),
              Y.bind(hoverStep, null, step, 'out', stepsNode));

  var deleter = stepNode.one('.deleteStep');
  if (deleter) {
    deleter.on('mousedown', function(event) {
        // Don't give the proof step a chance to select itself.
        event.stopPropagation();
      });
    deleter.on('click', function(event) {
        // Don't give the proof step a chance to select itself.
        event.stopPropagation();
        var msg = 'Delete step ' + step.stepNumber + ' and all following?';
        // Note that step numbers start at 1.
        var ok = (step.stepNumber >= controller.steps.length
                  || window.confirm(msg));
        if (ok) {
          controller.removeStepAndFollowing(step);
          controller.saveState();
        }
      });
  }
               
  // Caution: passing null to Y.on selects everything.
  var target = stepNode.one('span.ruleName');
  if (target) {
    target.on('mousedown', function(event) {
          // Don't give the proof step a chance to select itself.
          event.stopPropagation();
      });
    target.on('click', function(event) {
          // Don't give the proof step a chance to select itself.
          event.stopPropagation();
          renderSubProof(event, step, stepsNode);
      });
  }
  return stepNode;
}

/**
 * Returns an array of the unrendered steps leading up to and
 * including the given step, sorted by ordinal.  Helper function
 * internal to renderInference.  The "unrendered" aspect is helpful
 * for rendering subproofs, furthermore currently a step only
 * remembers one rendering.
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
    renderInference(Y.getTheorem(step.ruleArgs[0]), parent, false);
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

    // TODO: Consider showing some of the arguments.
  }
  return stepInfo;
}

/**
 * Renders an inference step name in a fancy way, currently with class
 * ruleName and a tooltip that briefly describes it.  (Displays much
 * like a hyperlink.)
 */
function fancyName(expr) {
  var name = expr.ruleName;
  var info = Y.rules[name].info;
  var comment = Y.Escape.html(info.comment || '');
  return '<span class=ruleName title="' + comment + '">' + name + '</span>';
}

/**
 * Renders a header and the proof steps of an inference by appending
 * them to a container Node.  First appends a node containing the
 * header, rendered with class proofHeader, then a node with the proof
 * display.
 *
 * Inputs are a proof step, the container node, a flag to indicate
 * whether to make the display editable, and an optional proof time in
 * milliseconds (elapsed time of proof execution).  This renders the
 * details of the step and a description of the step itself.
 *
 * Returns the ProofController.
 */
function renderInference(step, node, editable, millis) {
  var steps = unrenderedDeps(step.details);
  var controller = new ProofControl();
  controller.setSteps(steps);
  var comment = Y.rules[step.ruleName].info.comment || '';
  var pruf = step.ruleArgs.length ? 'Rule ' : 'Proof of ';
  node.appendChild('<div class=proofHeader><b>' + pruf
                   + step.ruleName + '</b>' + computeArgInfo(step) + '<br>'
                   + '<i>' + comment + '</i></div>');
  node.append(controller.node);
  controller.setEditable(editable);
  return controller;
}

/**
 * Render the unrendered steps up to and including the given step,
 * appending the display to the given Node.  If millis are given they
 * should be the elapsed time for executing the proof, and this
 * appends statistics on proof execution and rendering before
 * appending the proof itself.  Returns a new ProofControl containing
 * the rendering; and nSteps then should be the number of steps
 * counted.
 */
function renderProof(step, node, millis, nSteps) {
  var startRender = new Date().getTime();
  var steps = unrenderedDeps(step);
  var controller = new ProofControl();
  controller.setSteps(steps);
  var renderTime = Math.ceil(new Date().getTime() - startRender);
  var stats = '';
  if (millis != null) {
    stats = '<i style="font-size:smaller; color:gray">Proof '
      + Math.ceil(millis) + ' msec, rendering '
      + renderTime + ' msec, ' + nSteps + ' steps</i>';
    node.append('<div class=proofHeader>' + stats + '</div>');
  }
  node.append(controller.node);
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
    var argText;
    if (typeof arg == 'string'
        || arg instanceof Y.Expr
        || arg instanceof Y.Path) {
      argText = arg;
    } else {
      argText = Y.debugString(arg);
    }
    argInfo += '<code>' + argText + '</code>';
  }
  if (i > 0) {
    argInfo =
      ' <span style="font-weight: normal">with '
      + argInfo + '</span>';
  }
  return argInfo;
}

/**
 * Computes the lowest real ordinal of a set of steps.
 * TODO: Eliminate this when there are no more artificial ordinals
 * due to creating assertions after the fact.
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

/**
 * Adds the named CSS class to the node.  For use in hover handlers.
 * Currently does nothing if node is null, which occurs in hypotheses.
 */
function addClass(node, className) {
  node && node.addClass(className);
}

/**
 * Removes the named CSS class from the node.
 * For use in hover handlers.
 */
function removeClass(node, className) {
  node && node.removeClass(className);
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
  // as the mouse goes in or out.
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

/**
 * Hover handler for "r" and "replace".
 */
function hoverReplace(step, action) {
   var args = step.original.ruleArgs;
   var eqn = args[0].rendering;
   var target = args[1].rendering;
   var path = args[2];
   action(target.node, 'hover');
   action(target.locate(path).node, 'old');
   action(step.locate(path).node, 'new');
   action(eqn.getLeft().node, 'old');
   action(eqn.getRight().node, 'new');
}

// Arguments to the handler functions are an inference
// and the operation is "addClass" or "removeClass".
var hoverHandlers = {
  r: hoverReplace,
  replace: hoverReplace,
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
  apply: function(step, action) {
    var args = step.original.ruleArgs;
    var dep = args[0].rendering;
    var path = args[1];
    var call = dep.locate(path);
    var result = step.locate(path);
    if (call.fn instanceof Y.Lambda) {
      var target = call.fn.body;
      var varName = call.fn.bound.name;
      action(dep.node, 'hover');
      action(call.arg.node, 'new');
      action(target.node, 'scope');
      action(result.node, 'scope');
      target.findAll(varName,
                     function(v) { action(v.node, 'occur'); },
                     result,
                     function(expr) { action(expr.node, 'new'); });
    } else {
      action(call.node, 'dep');
      action(result.node, 'scope');
    }
  },
  useDefinition: function(step, action) {
    var args = step.original.ruleArgs;
    var target = args[0].rendering;
    var path = args[1];
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
  instVar: function(step, action) {
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
  // TODO: instMultiVars
  instForall: function(step, action) {
    var args = step.original.ruleArgs;
    // Input expression, a top-level call to "forall".
    var input = args[0].rendering.unHyp();
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

function contains(array, item) {
  return Y.Array.indexOf(array, item) >= 0;
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

//// Export public names.

Y.ProofControl = ProofControl;
Y.showOrdinals = false;
Y.renderInference = renderInference;
Y.renderProof = renderProof;
Y.addBottomPanel = addBottomPanel;
Y.getStepsNode = getStepsNode;
Y.getProofStep = getProofStep;
Y.getStepsNode = getStepsNode;
Y.getExpr = getExpr;
// TODO: Consider getting rid of this global variable.

}, '0.1', {requires: ['array-extras', 'expr', 'step-editor']});
