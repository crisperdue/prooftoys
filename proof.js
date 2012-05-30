// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Use the application's assert function.
var assert = Y.assertTrue;

// Make the main classes available without "Y.":
var Expr = Y.Expr;
var Var = Y.Var;
var Call = Y.Call;
var Lambda = Y.Lambda;

//// APPLICATION DATA STORAGE

var proofToyState = {

  // Global data to store in the hidden field named ToyStore.
  // Created with an object/slot to hold all ProofEditor data.
  data: {proofEditors: {}},

  // Global form element to store proofToyData.
  _toyStore: null,

  // Callbacks to run when the global data becomes ready.
  _dataReadyHandlers: [],

  /**
   * Registers a "data ready" callback.
   */
  onDataReady: function(fn) {
    this._dataReadyHandlers.push(fn);
  },

  /**
   * Save proofToyData into the document's data store so it will persist
   * across page load/unload.  Silently do nothing if there is no store
   * element.  Called automatically immediately after all dataReady
   * handlers have fired during page loading.
   *
   * TODO: Consider deferring this action using a Refresher, to reduce
   * redundant work.
   */
  store: function() {
    if (this._toyStore) {
      this._toyStore.set('value', Y.JSON.stringify(this.data, null, 1));
    }
  },

  /**
   * Load all application data from the per-page store; runs just once
   * on page load.  If there is data, run all dataReady handlers, then
   * store the global data back into the toyStore.
   */
  _load: function() {
    node = Y.one('#ToyStore');
    this._toyStore = node;
    if (node) {
      var text = node.get('value');
      if (text) {
        // Non-empty text.
        this.data = Y.JSON.parse(text);
      }
      Y.each(this._dataReadyHandlers, function(fn) { fn(); });
      this.store();
    } else {
      console.log('No #ToyStore element.');
    }
  }
}
// This should be insensitive to when this script loads.
Y.on('domready', proofToyState._load, proofToyState);


//// PROOF EDITOR

// TODO: Consider how to refactor ProofEditor, ProofControl, and
//   StepEditor for cleaner code.  Should ProofEditor subclass from
//   ProofControl?

// Each instance has a numeric ID.
var nextProofEditorId = 1;

/**
 * Construct a proof displayer/editor, which is a composite made from
 * a ProofControl.  User interaction may also create additional
 * subproof ProofControl objects within this.
 */
function ProofEditor() {
  var self = this;
  // Set the ID.
  this.proofEditorId = nextProofEditorId++;
  // Data of this ProofEditor to remember across page load/unload,
  // representable in JSON.
  this.data = {};
  this._mainControl = new ProofControl();
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
    '<input class=restoreProof type=button value="Restore proof">\n' +
    '<input class=hideProofState type=button value="Close"><br>\n' +
    '<textarea class=proofStateArea rows=20></textarea>\n' +
    '</div>\n';
  this.stateDisplay = Y.Node.create(stateDisplayHtml);
  this.stateArea = this.stateDisplay.one('.proofStateArea');
  this.containerNode = Y.Node.create('<div class=proofContainer></div>');
  this.containerNode
    .append(this._mainControl.node)
    .append(this.stateDisplay);

  // If the proof has changed, save its state.
  this._refresher = new Y.Refresher(function() {
      self.saveState();
    });
  // Make the ProofControl save state when the proof changes.
  this._mainControl.proofChanged = function() {
    // Changing the proof may change selections (without registering a
    // click on a step).  It also moves the location of the step
    // editor on the page, and both are handled appropriately by a
    // reset.
    self._refresher.activate();
    // "this" is the ProofControl.
    this.stepEditor.reset();
  };
  // Update the step editor query results when the selection may
  // have changed.
  this._mainControl.selectionChanged = function() {
    // Forces full display of the appropriate inference rules for
    // the new selection.
    this.stepEditor.reset();
    this.stepEditor.focus();
  };

  // Toggling the proof state display visibility with a button.
  // 
  // TODO: Consider creating the step editor from the proof editor
  //   rather than ProofControls for cleaner structure, less redundant
  //   step editors.
  this._mainControl.stepEditor.saveRestore.on('click', function() {
      self.stateDisplay.toggleClass('hidden');
    });

  // Handler for the "restore proof" button.  Restores proof state from
  // the text area and saves global state.
  function restoreProof() {
    Y.withErrorReporting(function() {
        self.restoreState();
        proofToyState.store();
      });
  }
  this.stateDisplay.one('.restoreProof').on('click', restoreProof);

  // Closing the state display:
  this.stateDisplay.one('.hideProofState').on('click', function() {
      self.stateDisplay.addClass('hidden');
    });

  // Sets this ProofEditor's "data" property to the global data
  // associated with its proofEditorId.  Updates the state of the
  // proof itself, and saves the state into the text area.
  //
  // If the global data has no information about this, just links the
  // existing value into the global data.
  function loadData() {
    var data = proofToyState.data.proofEditors[self.proofEditorId];
    if (data) {
      self.data = data;
      if (data.proofState) {
        self._mainControl.setSteps(Y.decodeSteps(data.proofState));
      }
    } else {
      proofToyState.data.proofEditors[self.proofEditorId] = self.data;
    }
  }
  proofToyState.onDataReady(Y.bind(Y.withErrorReporting, null, loadData));
}

/**
 * Add a step to the proof.
 */
ProofEditor.prototype.addStep = function(step) {
  this._mainControl.addStep(step);
};

/**
 * Gets the state of the proof, in string form.
 */
ProofEditor.prototype.getStateString = function() {
  return Y.encodeSteps(this._mainControl.steps)
};

/**
 * Sets the state of the proof from a string as returned by
 * getStateString.
 */
ProofEditor.prototype.setStateFromString = function(encoded) {
  var steps = Y.decodeSteps(encoded);
  this._mainControl.setSteps(steps);
};

/**
 * Sets the steps to the given array of non-renderable steps.
 */
ProofEditor.prototype.setSteps = function(steps) {
  var rendered = Y.Array.map(steps, function(step) { return step.copyStep(); });
  this._mainControl.setSteps(rendered);
};

/**
 * Save the proof state to the the proof's text area and the
 * document's data store.  Normally use the proofChanged method rather
 * than calling this directly, avoiding redundant work.
 */
ProofEditor.prototype.saveState = function() {
  var text = this.getStateString();
  this.stateArea.set('value', text);
  this.data.proofState = text;
  proofToyState.store();
};

/**
 * Attempts to restore the proof state from the proof's text area.
 */
ProofEditor.prototype.restoreState = function() {
  var string = this.stateArea.get('value');
  assert(string, 'No proof state recorded');
  this.setStateFromString(string);
};

ProofEditor.prototype.setEditable = function(value) {
  this._mainControl.setEditable(value);
}


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
 * Expr.justify.
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
 * Like proofChanged, default is a no-op but instances may override
 * this.
 */
ProofControl.prototype.selectionChanged = function() {};

/**
 * Sets the steps of the current proof to be the ones in the given
 * array, which should contain only renderable steps.  Sets their
 * stepNumber properties to run from 1 to N and renders them.  The
 * rendered copies become the value of the steps property of the
 * ProofControl.
 *
 * TODO: Make a sensible policy for accepting renderable versus
 * nonrenderable steps.
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
 */
ProofControl.prototype.removeStepAndFollowing = function(toRemove) {
  var index = this.steps.indexOf(toRemove);
  var steps = this.steps;
  // Remember the current length.
  var length = steps.length;
  for (var i = index; i < length; i++) {
    // Don't change the index - each iteration deletes a step.
    clearSubproof(steps[index]);
    this._removeStep(steps[index]);
  }
  this.proofChanged();
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
    // Communicate that the selection _may_ have changed.
    this.selectionChanged();
  }
};

/**
 * Handles selection of an expression in a step.
 * Deselects any other selected expression in the step,
 * toggles the current one if already selected.  Prevents
 * event bubbling up to the step itself.
 */
ProofControl.prototype.handleExprSelection = function(expr) {
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
    // Communicate that the selection _may_ have changed.
    this.selectionChanged();
  }
};


////
//// PROOF and STEP RENDERING
////

// String containing just the turnstile math character.  See
// http://tlt.its.psu.edu/suggestions/international/bylanguage/mathchart.html
var _turnstile = Y.Node.create('&#8870;').get('text');

/**
 * Create and return a YUI node to display the renderable step within
 * the given controller.  Assumes that the renderable step already
 * inserted into the controller's steps array.
 *
 * This also sets up event handlers for click
 * and hover events within the step.  Does not insert the new node
 * into the document.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression and subexpression has a "node" property
 *   that refers to a YUI node with its rendering.
 *
 * - A rendered step has an "original" property referring to the
 *   unrendered proof step from which it was created.
 *
 * - When a rendered step has a subproof display open, it has a
 *   "subproofControl" property referring to the subproof's
 *   ProofControl.
 *
 * - Creation of a rendered step adds a "rendering" property to the
 *   original, so original proof steps can currently have only one
 *   rendering at a time.
 *
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
  var elide = wantLeftElision(step, controller);
  step.hasLeftElision = elide;
  var wffNode = renderAsStep(step);
  stepNode.one('.wff').setContent(wffNode);

  // TODO: Consider up these handlers in an ancestor node by delegation.
  // Set up click handlers for selections within the step.
  wffNode.on(TOUCHDOWN,
       // This implements a policy of one selection per proof step.
       // TODO: Implement such policies in the proof controller.
       function(event) {
         controller.handleExprSelection(getEffectiveSelection(event.target));
         event.preventDefault();
       });
  stepNode.on(TOUCHDOWN,
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
  if (target && Y.modes.subproofs) {
    target.on('mousedown', function(event) {
          // Don't give the proof step a chance to select itself.
          event.stopPropagation();
      });
    target.on('click', function(event) {
          // Don't give the proof step a chance to select itself.
          event.stopPropagation();
          if (step.subproofControl) {
            clearSubproof(step);
          } else {
            renderSubproof(step);
          }
      });
  }
  return stepNode;
}

/**
 * If not in simplified selections mode, just get the Expr for the
 * target node.
 *
 * If selections are simplified, do not select the name of a function
 * in a function call (including the operator of a call to a binary
 * operator), nor the "Curried part" of an infix call.
 *
 * Argument is the target node of a selection event.
 */
function getEffectiveSelection(node) {
  // TODO: Consider applying this concept to hovers also.
  if (Y.simplifiedSelections) {
    // This could be optimized for speed:
    var expr = getExpr(node);
    var nodeParent1 = node.ancestor('.expr');
    var parent1 = getExpr(nodeParent1);
    var parent2 = getExpr(nodeParent1.ancestor('.expr'));
    if (expr instanceof Y.Var && Y.isInfixDesired(expr) && parent2.isCall2()) {
      // Node is for a binary operator called as binop.
      return parent2;
    } else if (parent1.isCall1() && expr == parent1.fn) {
      // Node is for function name in call with 1 arg.
      return parent1;
    } else if (parent1.isCall2() && expr == parent1.fn) {
      // Node is for "half" of a binop call.
      return parent1;
    } else {
      return expr;
    }
  } else {
    return getExpr(node);
  }
}


// NOTE that some methods on Expr and its subclasses appear here.

/**
 * Returns true iff policy is to elide the LHS of the given step
 * within the given ProofControl, assumed to contain it.
 */
function wantLeftElision(step, controller) {
  if (step.ruleName == 'display' || step.ruleName == 'asImplication') {
    return false;
  }
  var index = controller.steps.indexOf(step);
  var prev = index > 0 ? controller.steps[index - 1] : null;
  return (prev &&
          (prev.hasLeftElision || prev.ruleName == 'consider') &&
          // "Matches" is OK, maybe better to define and use "identical".
          // They are copies so not ==.
          step.unHyp().getLeft().matches(prev.unHyp().getLeft()));
}


/**
 * Renders this (renderable copy of an original) expression into a new
 * YUI node, returning the node.  Omits surrounding parens if the step
 * is a Call.
 *
 * TODO: Consider fleshing out the concept of display with fewer
 * parentheses.
 *
 * TODO: When displaying hypotheses, somehow properly distinguish
 * hypotheses that come from within the current subproof versus those
 * that come from outside.
 */
function renderAsStep(step) {
  if (step.hasHyps) {
    var wffNode = step.node = renderHyps(step.getLeft());
    wffNode.append(textNode(' ' + _turnstile + ' '));
    wffNode.append(renderMain(step));
    return wffNode;
  } else {
    return renderMain(step);
  }
};

/**
 * Renders the "main" part of a renderable step, meaning everything
 * but the hypotheses.  Currently gives special treatment to equations
 * starting with rules.consider and immediately following steps.
 * Returns a new YUI node that renders it.
 */
function renderMain(step) {
  var main = step.unHyp();
  if (main.isCall2('=')) {
    if (step.ruleName == 'consider') {
      var node = main.node = exprNode();
      node.append(main.getRight()._render(true));
      node.append(textNode(' = '));
      node.append('<span class=ellipsis>&hellip;</span>');
    } else {
      if (step.hasLeftElision) {
        var node = main.node = exprNode();
        node.append('<span class=ellipsis>&hellip;</span>');
        node.append(textNode(' = '));
        node.append(main.getRight()._render(true));
      } else {
        var node = main._render(true);
      }
    }
    return node;
  } else {
    return main._render(true);
  }
}

/**
 * Walk through the expression as a set of hypotheses.  This code
 * might recurs both left and right, which may help displaying
 * hypotheses that are in the process of being rearranged.
 */
function renderHyps(expr) {
  var mainNode = exprNode();
  if (Y.suppressRealTypeDisplays) {
    expr = omittingReals(expr);
  }
  if (!expr) {
    return mainNode;
  }
  function render(expr) {
    if (expr.sourceStep) {
      var node = expr.node = exprNode();
      // Note that this requires the unrendered proof step to be already
      // linked to a rendering with proper stepNumber:
      node.append(expr.sourceStep.rendering.stepNumber);
      mainNode.append(node);
    } else if (expr.isCall2('&&')) {
      render(expr.getLeft());
      mainNode.append(textNode(', '));
      var rhs = expr.getRight();
      if (rhs.isCall2('&&')) {
        mainNode.append(textNode('('));
        render(rhs);
        mainNode.append(textNode(')'));
      } else {
        render(rhs);
      }
    } else {
      mainNode.append(expr._render(true));
    }
  }
  render(expr);
  return mainNode;
}

/**
 * Returns a conjunction of a subset of the given hyps (a chain of
 * conjuncts or null).  If the set is empty returns null.  Note that
 * this does not copy any conjuncts in the chain.  The subset omits
 * any that declare a variable to be a real number using the "R"
 * predicate.
 */
function omittingReals(hyps) {
  if (!hyps) {
    return null;
  }
  var result = null;
  hyps.eachHyp(function(hyp) {
      if (!hyp.isCall1('R') || !hyp.arg.isVariable()) {
        if (result) {
          result = Y.infixCall(result, '&&', hyp);
        } else {
          result = hyp;
        }
      }
    });
  return result;
}

/**
 * Build and return a Node of class "expr".
 */
function exprNode() {
  return Y.Node.create('<span class=expr></span>');
}

/**
 * Converts text symbols to HTML for display.
 */
var entities = {
  // Do not use nonbreaking hyphens in case the end user wants to copy and
  // paste displayed text.  Instead consider CSS hyphenation options.
  // '-->': '&#8209;&#8209&gt;',   // &rArr; looks lousy in fixed-width font.
  '>=': '&ge;',
  '<=': '&le;',
  '!=': '&ne;',
  '==': '&equiv;'
};

/**
 * Create and return a text node containing a space.  YUI (and IE)
 * trim whitespace if you put in text in other ways.
 */
function space() {
  return document.createTextNode(' ');
}

function textNode(text) {
  return document.createTextNode(text);
}

// _render(omit)
//
// Render this expression into a new YUI node, returning the node.
// Sets the expression's "node" property to refer to the node created
// to enclose this expression.  Should be done only once to any given
// expression.  Helper for the render method.  (Not public)
//
// If the optional "omit" argument is true and this is a Call, omit
// the enclosing parentheses.
// 
//

Var.prototype._render = function(omit) {
  var node = this.node = exprNode();
  var name = this.pname || this.name;
  node.append(entities[name] || name);
  return node;
};

Call.prototype._render = function(omit) {
  var node = this.node = exprNode();
  var stepNum = (Y.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  omit = omit && !stepNum;
  if (!omit) {
    if (Y.trackSourceSteps) {
      if (this.sourceStep) {
        node.append('$');
      }
      if (stepNum) {
        node.append(stepNum);
      }
    }
    node.append('(');
  }
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    // This is a call on a named function of two arguments.
    if (Y.isInfixDesired(this.fn.fn)) {
      // Non-alphabetic characters: use infix: "x + y"
      var fnNode = this.fn.node = exprNode();
      fnNode.append(this.fn.arg._render());
      fnNode.append(space());
      fnNode.append(this.fn.fn._render());
      node.append(fnNode);
      node.append(space());
      node.append(this.arg._render());
    } else {
      // Alphabetic characters: function comes first.
      var fnNode = this.fn.node = exprNode();
      fnNode.append(this.fn.fn._render());
      fnNode.append(space());
      fnNode.append(this.fn.arg._render());
      node.append(fnNode);
      node.append(space());
      node.append(this.arg._render());
    }
  } else if (this.fn instanceof Var && Y.isInfixDesired(this.fn)) {
    // Infix operator, but only one argument: "x +"
    node.append(this.arg._render());
    node.append(space());
    node.append(this.fn._render());
  } else {
    // Normal function call: "f x"
    node.append(this.fn._render());
    node.append(space());
    node.append(this.arg._render());
  }
  if (!omit) {
    node.append(')');
  }
  return node;
};

Lambda.prototype._render = function(omit) {
  var node = this.node = exprNode();
  var stepNum = (Y.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  if (stepNum) {
    node.append('$' + stepNum);
  }
  node.append('{');
  node.append(this.bound._render());
  node.append(textNode('. '));
  node.append(this.body._render(true));
  node.append('}');
  return node;
};

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
 * Renders details of the given rendered proof step and set the
 * subproofControl property of the step to the ProofControl for the
 * subproof.
 */
function renderSubproof(step) {
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

/**
 * Clear any subproof of this step and any subproofs of its steps
 * recursively.  Remove the subproofControl property from the step.
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

    var exclusions = ['assume', 'assert', 'axiom4', 'consider', 'eqSelf',
                      'applier', 'tautology', 'mergeConjunctions'];
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
  var description = info.description || name;
  var comment = Y.Escape.html(info.comment || '');
  if (Y.modes.subproofs) {
    return ('<span class=ruleName title="' + comment + '">'
            + description + '</span>');
  } else {
    return description;
  }
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
  var comment = Y.Escape.html(Y.rules[step.ruleName].info.comment || '');
  var pruf = step.ruleArgs.length ? 'Rule ' : 'Proof of ';
  node = Y.Node.create('<div class=inferenceDisplay></div>');
  node.append('<div class=proofHeader><b>' + pruf
              + step.ruleName + '</b>'
              + computeHeaderArgInfo(step) + '<br>'
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
 * Helper for renderInference, computes arguments display string for
 * the header display of a subproof.
 *
 * TODO: Re-think and rewrite this, probably using Y.eachArgType.
 *   Indicate sites in steps in some user-friendly way.
 */
function computeHeaderArgInfo(step) {
  var argInfo = '';
  for (var i = 0; i < step.ruleArgs.length; i++) {
    var arg = step.ruleArgs[i];
    var argText;
    if (arg instanceof Y.Expr) {
      argText = arg.toString();
    } else if (typeof arg == 'string' && arg[0] != '/') {
      argText = arg;
    } else if (typeof arg == 'string' || arg instanceof Y.Path) {
      // Ignore paths and strings that look like paths.
      continue;
    } else {
      argText = Y.debugString(arg);
    }
    if (argInfo) {
      argInfo += ', ';
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
    // The top-level call to "forall".
    var input = args[0].rendering.unHyp();
    // Name of variable being instantiated.
    var varName = input.arg.bound.name;
    action(input.node, 'dep');
    var body = input.arg.body;
    body.findAll(varName,
                 function(_var) { action(_var.node, 'occur'); },
                 step.unHyp(),
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

Y.proofToyState = proofToyState;
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

// Global configuration variable for displaying extra information per
// step when hovered.
Y.useHoverOverlays = false;

// Global parameter to suppress displaying hypotheses such as "(R x)".
Y.suppressRealTypeDisplays = true;

// Detect if the device has a touch screen, e.g. a tablet.
// Mobile jQuery 1.1 does this same test.
Y.hasTouchEvents = 'ontouchend' in document;

// Control whether to use an Autocompleter vs. plain SELECT element.
Y.useAutocompleter = !Y.hasTouchEvents;

// Global parameter to suppress GUI selection of function names
// and the "Curried part" of an infix call.
Y.simplifiedSelections = Y.hasTouchEvents;

// Name of event when the user touches the screen or clicks the mouse.
// Note: when using 'mousedown' as the TOUCHDOWN event Chrome has been
// observed to unfocus the keyboard on the subsequent mouseup event,
// an unwanted effect.
var TOUCHDOWN = Y.hasTouchEvents ? 'touchstart' : 'click';

// Override these properties on the page to get custom modes of
// display and/or operation.
Y.modes = {
  subproofs: true
};

}, '0.1', {requires: ['array-extras', 'expr', 'step-editor', 'event-touch']});
