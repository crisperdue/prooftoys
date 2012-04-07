// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Use the application's assert function.
var assert = Y.assertTrue;


//// PROOF EDITOR

// TODO: Consider how to refactor ProofEditor, ProofControl, and
//   StepEditor for cleaner code.  Should ProofEditor subclass from
//   ProofControl?

/**
 * Construct a proof displayer/editor, which is a composite made from
 * a ProofControl.  User interaction may also create additional
 * subproof ProofControl objects within this.
 */
function ProofEditor() {
  var self = this;
  this.mainControl = new ProofControl();
  var stateDisplayHtml =
    '<div class="proofStateDisplay hidden"\n' +
    ' style="padding: 1em; border: 2px solid #aaf">\n' +
    '<p style="margin: 0em">\n' +
    '<b>Proof state</b>\n' +
    '<p>\n' +
    'The text area below contains the current state of the proof in textual\n' +
    'form.  You can save the state of your work by copying this text into a\n' +
    'document of your choice.  To restore the state at some time in the\n' +
    'future, paste it back then press "Restore proof".\n' +
    '<p>\n' +
    '<input class=loadProofState type=button value="Restore proof">\n' +
    '<input class=hideProofState type=button value="Close"><br>\n' +
    '<textarea class=proofStateArea rows=20></textarea>\n' +
    '</div>\n';
  this.stateDisplay = Y.Node.create(stateDisplayHtml);
  this.stateArea = this.stateDisplay.one('.proofStateArea');
  this.containerNode = Y.Node.create('<div class=proofContainer></div>');
  this.containerNode
    .append(this.mainControl.node)
    .append(this.stateDisplay);

  // Toggling the proof state display visibility with a button.
  // 
  // TODO: Consider creating the step editor from the proof editor
  //   rather than ProofControls for cleaner structure, less redundant
  //   step editors.
  this.mainControl.stepEditor.saveRestore.on('click', function() {
      self.stateDisplay.toggleClass('hidden');
    });

  // Make the ProofControl save state when the proof changes.
  this.mainControl.proofChanged = function() { self.saveState(); };

  // Handler for loading proof state from the text area:
  function loadProofState() {
    Y.withErrorReporting(function() {
        var text = self.stateArea.get('value');
        if (text.length > 3) {
          // If the text is empty, don't bother.  This is important on
          // page (re)load, below.
          var steps = Y.decodeSteps(text);
          self.mainControl.setSteps(steps);
        }
      });
  }
  this.stateDisplay.one('.loadProofState').on('click', loadProofState);

  // Closing the state display:
  this.stateDisplay.one('.hideProofState').on('click', function() {
      self.stateDisplay.addClass('hidden');
    });

  Y.on('domready', function() { loadProofState(); });
}

/**
 * In case there is a textarea with the proof control's configured ID
 * on the page, save the proof state to it.
 */
ProofEditor.prototype.saveState = function() {
  this.stateArea.set('value', Y.encodeSteps(this.mainControl.steps));
};

/**
 * In case there is a textarea with the proof control's configured ID
 * on the page, restore the proof state from it.
 */
ProofEditor.prototype.restoreState = function() {
  var steps;
  try {
    var value = this.stateArea.get('value');
    assert(value, 'No proof state recorded');
    steps = Y.decodeSteps(value);
  } catch(err) {
    window.alert('Failed to parse proof state: ' + err.message);
    throw err;
  }
  this.mainControl.setSteps(steps);
};


//// PROOF CONTROL

// TODO: Extend these to support proof steps that can take more
// than one selection.

/**
 * Construct a ProofControl.  No arguments.
 *
 * Properties:
 *
 * steps: an array of the _rendered_ steps displayed.
 *
 * node: Node containing the entire rendering of the proof.  This has
 * CSS class proofDisplay and the ProofControl as the value of its
 * getData('proofControl').  Only ProofControl nodes should have the
 * proofDisplay class.
 *
 * Other properties should be considered private.
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

  // ID of element to use for saving/restoring proof state.
  // TODO: Make the textarea part of the ProofControl.
  this.textAreaId = 'proofState';

  // Only official "proof nodes" are permitted to have class proofDisplay.
  var html = ('<table class=proofDisplay><tr><td>' +
              '<div class=stepsParent><div class=proofSteps></div></div>' +
              '</table>');
  this.node = Y.Node.create(html);
  this.node.setData('proofControl', this);
  var stepsParent = this.node.one('.stepsParent');
  this.stepsNode = this.node.one('.proofSteps');
  this.stepEditor = new Y.StepEditor(this);
  this.node.one('td').append(this.stepEditor.node);

  this.setEditable(false);

  // Create an overlay to display step details when hovered.
  this.hoverOverlay = new Y.Overlay({
      width: '80%',
      bodyContent: 'Sample overlay content',
      zIndex:2
  });
  this.hoverOverlay.render(stepsParent);
  this.hoverOverlay.hide();

  // Set up handling of mouseover and mouseout events.
  Y.on('mouseover', exprHandleOver, this.node);
  Y.on('mouseout', exprHandleOut, this.node);
}

/**
 * By default do nothing when the proof changes, but instances may
 * provide their own actions.
 */
ProofControl.prototype.proofChanged = function() {};

/**
 * Sets the steps of the current proof to be the ones in the given
 * array, which should contain only renderable steps.  Sets their
 * stepNumber properties to run from 1 to N and renders them.  The
 * rendered copies become the value of the steps property of the
 * ProofControl.
 */
ProofControl.prototype.setSteps = function(steps) {
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
  this.proofChanged();
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
  // TODO: Consider updating "dep" highlighting here if this is "hovered".
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
  this.proofChanged();
};

/**
 * Remove from the proof display the given top-level rendered proof
 * step and all other steps of the display that come after it.
 *
 * TODO: Clear subproofs, see renderSubproof. 
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
 * Create and return a YUI node to display the renderable step within
 * the given controller.  This also sets up event handlers for click
 * and hover events within the step.  Does not insert the new node
 * into the document.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression and subexpression has a "node" property
 *   that refers to a YUI node with its rendering.
 * - The given step's YUI node has CSS class 'proofStep' and a
 *   'proofStep' data property that refers to the step.  Code
 *   elsewhere may assume that only node's that render a proof step
 *   have the proofStep CSS class.
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
        // Is it the last step or the user says OK?
        if (controller.steps.indexOf(step) >= controller.steps.length - 1 ||
            window.confirm(msg)) {
          controller.removeStepAndFollowing(step);
          // Unmark all steps as dependencies.  They might be dependencies
          // of a deleted step.  Moving the mouse will get highlighting
          // started again.
          // TODO: Consider whether this action should be part of
          //   ProofControl._removeStep.
          Y.each(controller.steps, function(step) {
              getStepNode(step).removeClass('dep');
            });
          controller.proofChanged();
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
          renderSubproof(step);
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
 * Renders details of the given rendered proof step.
 */
function renderSubproof(step) {
  if (step.subproofControl) {
    clearSubproof(step);
  } else {
    var controller = getProofControl(step);
    Y.each(controller.steps, clearSubproof);
    var proof = step.node.ancestor('.proofDisplay');
    var display = proof.ancestor('.inferenceDisplay') || proof;
    // TODO: Flag the parent as "proofContainer" and simply search for that.
    var parent = display.get('parentNode');
    var node;
    if (step.ruleName == 'theorem') {
      node = renderInference(Y.getTheorem(step.ruleArgs[0]));
    } else {
      node = renderInference(step);
    }
    step.subproofControl = node.getData('proofControl');
    // Actually, append it to the top node of the proof + subproofs.
    parent.append(node);
  }
}

/**
 * Clear any subproof of this step and any subproofs of its steps
 * recursively.
 */
function clearSubproof(step) {
  var controller = step.subproofControl;
  delete step.subproofControl;
  if (controller) {
    Y.each(controller.steps, function(step) {
        // Record that the rendering is gone.
        step.original.rendering = null;
        // Clear any rendered subproof for the step.
        clearSubproof(step);
      });
    var container = controller.node.ancestor('.inferenceDisplay');
    container.remove();
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
    stepInfo += step.ruleArgs[0];
    if (step.ruleArgs.length == 2) {
      stepInfo += ' ' + step.ruleArgs[1];
    }
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

    var exclusions = ['assume', 'assert', 'axiom4', 'eqSelf', 'applier',
                      'mergeConjunctions'];
    if (exclusions.indexOf(step.ruleName) < 0) {
      var argDetails = computeExtraArgInfo(step);
      // TODO: Consider showing some of the arguments.
      if (argDetails) {
        stepInfo += ('<span class=argDetails> with ' + argDetails + '</span');
      }
    }
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
 * Given a rendered proof step, renders a header and the proof steps
 * of its as-yet-unrendered details. within a container DIV with CSS
 * class inferenceDisplay.  Sets the 'proofControl' data property of
 * the node to refer to the new ProofControl.
 *
 * Returns the new container DIV.
 */
function renderInference(step) {
  var steps = unrenderedDeps(step.details);
  var controller = new ProofControl();
  controller.setSteps(steps);
  var comment = Y.rules[step.ruleName].info.comment || '';
  var pruf = step.ruleArgs.length ? 'Rule ' : 'Proof of ';
  node = Y.Node.create('<div class=inferenceDisplay></div>');
  node.append('<div class=proofHeader><b>' + pruf
              + step.ruleName + '</b>' + computeArgInfo(step) + '<br>'
              + '<i>' + comment + '</i></div>');
  node.append(controller.node);
  node.setData('proofControl', controller);
  return node;
}

/**
 * Renders a proof of steps that derive a given step.  Renders the
 * unrendered steps up to and including the given step, appending the
 * display to the given Node.  Returns a new ProofControl containing
 * the rendering.
 *
 * If millis are given they should be the elapsed time for executing
 * the proof, and this appends statistics on proof execution and
 * rendering before appending the proof itself.  In this case nSteps
 * then should also be given, with the number of steps counted during
 * execution of the proof.
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
 * Computes HTML for arguments that are not steps or paths.  Returns a
 * comma-separated string, with each argument enclosed in <code></code>.
 * To enable more specific styling enclose the result in an element
 * with a suitable class.
 */
function computeExtraArgInfo(step) {
  var args = step.ruleArgs;
  var info = [];
  counter = 0;
  Y.eachArgType(step.ruleName, function(index, type) {
      var text;
      switch(type) {
      case 'term':
      case 'varName':
        text = args[index].toString();
        break;
      case 'string':
        text = Y.unparseString(args[index - 1]);
        break;
      default:
        // End the iteration.
        return;
      }
      info.push('<code>' + text + '</code>');
    });
  Y.each(step.ruleArgs, function(arg) {
      if (arg.constructor.prototype == Object.prototype) {
        // It is a plain object, show as a map.
        info.push('<code>' + Y.debugString(arg) + '</code>');
      }
    });
  return info.join(', ');
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
 * Gets the DOM node associated with the step, given a rendered Expr
 * within the step or the YUI node within it.
 */
function getStepNode(expr) {
  var node = expr instanceof Y.Expr ? expr.node : expr;
  return node.ancestor('.proofStep', true);
}

/**
 * Gets the proof step (Expr) of the step that renders
 * in part into the given YUI Node.  Also accepts an Expr of
 * a rendered proof.
 */
function getProofStep(node) {
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
 * Gets the ProofControl of a rendered term or step, or the node of
 * one.
 */
function getProofControl(expr) {
  var node = expr instanceof Y.Expr ? expr.node : expr;
  var ancestor = node.ancestor('.proofDisplay');
  return ancestor.getData('proofControl');
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
  var align = Y.WidgetPositionAlign;
  var action = direction == 'in' ? addClass : removeClass;
  // Always add or remove the "hover" class to the step node
  // as the mouse goes in or out.
  var stepNode = getStepNode(step.node);
  action(stepNode, 'hover');
  
  var overlay = getProofControl(step).hoverOverlay;
  if (Y.useHoverOverlays) {
    if (direction == 'in') {
      overlay.set('align', {
          node: stepNode, points: [align.TR, align.BR]});
      overlay.set('bodyContent', computeExtraArgInfo(step));
      overlay.show();
    } else {
      overlay.hide();
    }
  }

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
  // If no handler apply or remove default highlighting.
  Y.each(step.ruleDeps, function(dep) {
      action(getStepNode(dep.rendering), 'dep');
    });
  if (handler) {
    // If there is a hover handler for this type of inference, apply it.
    handler(step, action);
    // TODO: Let the default "dep" management below apply in all cases.
  }
}

/**
 * Hover handler for "r" and "replace".
 */
function hoverReplace(step, action) {
   var args = step.original.ruleArgs;
   var eqn = args[0].rendering.unHyp();
   var target = args[1].rendering;
   var path = args[2];
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
      action(call.arg.node, 'new');
      action(target.node, 'scope');
      action(result.node, 'scope');
      target.findAll(varName,
                     function(v) { action(v.node, 'occur'); },
                     result,
                     function(expr) { action(expr.node, 'new'); });
    } else {
      action(call.node, 'occur');
      action(result.node, 'scope');
    }
  },
  useDefinition: function(step, action) {
    var args = step.original.ruleArgs;
    var target = args[0].rendering;
    var path = args[1];
    action(target.node, 'dep');
    action(target.locate(path).node, 'old');
    action(step.locate(path).node, 'new');
  },
  instEqn: function(step, action) {
    var args = step.original.ruleArgs;
    // Input equation.
    var eqn = args[0].rendering;
    // Name of variable being instantiated.
    var varName = args[2].ruleName;
    action(eqn.node, 'dep');
    eqn.findAll(varName,
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
    action(input.node, 'dep');
    input.findAll(varName,
                  function(_var) { action(_var.node, 'occur'); },
                  step,
                  function(expr) { action(expr.node, 'new'); });
  },
  // TODO: instMultiVars
  instForall: function(step, action) {
    var args = step.original.ruleArgs;
    // Input step, a top-level call to "forall".
    var input = args[0].rendering;
    // Name of variable being instantiated.
    var varName = input.arg.bound.name;
    action(input.node, 'dep');
    var body = input.unHyp().arg.body;
    body.findAll(varName,
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

// Global configuration variable for displaying extra information per
// step when hovered.
Y.useHoverOverlays = false;

Y.ProofEditor = ProofEditor;
Y.ProofControl = ProofControl;
Y.showOrdinals = false;
Y.renderInference = renderInference;
Y.renderProof = renderProof;
Y.addBottomPanel = addBottomPanel;
Y.getStepNode = getStepNode;
Y.getProofStep = getProofStep;
Y.getStepsNode = getStepsNode;
Y.getExpr = getExpr;
// TODO: Consider getting rid of this global variable.

}, '0.1', {requires: ['array-extras', 'expr', 'step-editor']});
