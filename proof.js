// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

/**
 * Compatibility hack, global function that converts a YUI Node or
 * NodeList to a jQuery object, and jQuery objects pass through
 * unchanged.  When there are no more YUI things, calls to this
 * can be removed.
 */
function $$(x) {
  if (x instanceof jQuery) {
    return x;
  } else {
    var data = x._nodes || x._node;
    if (data) {
      return jQuery(data);
    } else {
      throw new Error('Cannot unYUI ' + x);
    }
  }
}

/**
 * Version of the jQuery $ function that type checks its input.
 */
function $(x) {
  if (arguments.length > 1) {
    return jQuery.apply(null, arguments);
  } else if (typeof x === 'string' ||
             x.nodeType ||
             x === window ||
             x instanceof jQuery) {
    return jQuery(x);
  } else {
    throw new Error('Not a DOM node: ' + x);
  }
}
jQuery.extend($, jQuery);

YUI.add('proof', function(Y) {

// Use the application's assert function.
var assert = Toy.assertTrue;

// Make the main classes available without "Toy."
var Expr = Toy.Expr;
var Var = Toy.Var;
var Call = Toy.Call;
var Lambda = Toy.Lambda;

/**
 * Converts a singleton jQuery object to its DOM node,
 * checking carefully that it is a jQuery singleton.
 */
function dom(jq) {
  if (jq instanceof jQuery) {
    if (jq.length === 1) {
      return jq[0];
    } else {
      throw new Error('Not a jQuery object: ' + jq);
    }
  } else {
    throw new Error('Length not 1: ' + jq);
  }
}

/**
 * Applies the action to each integer index and "input type" of each of
 * the arguments described by a rules "inputs" descriptor.  Indexes
 * passed to the action are zero-based, not 1-based as in the
 * descriptors.  Currently does not include indexes of paths not
 * explicitly described.
 */
function eachArgType(ruleName, action) {
  var inputs = Toy.rules[ruleName].info.inputs;
  for (var type in inputs) {
    if (type === 'condition') {
      // Value is not a position or position list.
      continue;
    }
    var where = inputs[type];
    if (typeof where == 'number') {
      action(where - 1, type);
    } else {
      where.forEach(function(position) {
        action(position - 1, type);
      });
    }
  }
}

/**
 * Given a step, rendered or not, uses its rule information to return
 * a list of paths used in its rule.
 */
function stepPaths(step) {
  assert(step.isStep(), 'Not a step: ' + step);
  var results = [];
  var args = step.ruleArgs;
  eachArgType(step.ruleName, function(position, type) {
      if (Toy.siteTypes.hasOwnProperty(type)) {
        results.push(step.ruleArgs[position + 1]);
      }
    });
  return results;
}

/**
 * Given a step, rendered or not, uses its rule information to return a list
 * of subexpressions of renderings of source steps that provided the input
 * sites for this step.  Their nodes will contain the rendering of the sites.
 */
function stepSites(step) {
  assert(step.isStep(), 'Not a step: ' + step);
  var results = [];
  var args = step.ruleArgs;
  eachArgType(step.ruleName, function(position, type) {
    if (Toy.siteTypes.hasOwnProperty(type)) {
      var source = step.ruleArgs[position];
      if (source.rendering) {
        results.push(source.rendering.locate(step.ruleArgs[position + 1]));
      }
    }
  });
  return results;
}


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
      this._toyStore.value = JSON.stringify(this.data, null, 1);
    }
  },

  /**
   * Load all application data from the per-page store; runs just once
   * on page load.  If there is data, run all dataReady handlers, then
   * store the global data back into the toyStore.
   */
  _load: function() {
    storage = dom($('#ToyStore'));
    this._toyStore = storage;
    if (storage) {
      var text = storage.value;
      if (text) {
        // Non-empty text.
        this.data = JSON.parse(text);
      }
      this._dataReadyHandlers.forEach(function(fn) { fn(); });
      this.store();
    } else {
      console.log('No #ToyStore element.');
    }
  }
}

// When the page is completely loaded, load the app state.
$(window).load($.proxy(proofToyState, '_load'));

// Try using this version when YUI is removed.
// When the DOM is ready load the proof state.
// $($.proxy(proofToyState, '_load'));


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
  @mainControl = new ProofControl();
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
  this._stateDisplay = $(stateDisplayHtml);
  this._stateArea = dom(this._stateDisplay.find('.proofStateArea'));
  this.containerNode = $('<div class=proofContainer></div>');
  this.containerNode
    .append(@mainControl.node)
    .append(this._stateDisplay);

  // If the proof has changed, save its state.
  this._refresher = new Toy.Refresher(function() {
      self.saveState();
    });

  // Make the ProofControl save state when the proof changes.
  @mainControl.proofChanged = function() {
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
  @mainControl.selectionChanged = function() {
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
  @mainControl.stepEditor.saveRestore.on('click', function() {
      self._stateDisplay.toggleClass('hidden');
    });

  // Handler for the "restore proof" button.  Restores proof state from
  // the text area and saves global state.
  function restoreProof() {
    Toy.withErrorReporting(function() {
        self.restoreState();
        proofToyState.store();
      });
  }
  this._stateDisplay.find('.restoreProof').on('click', restoreProof);

  // Closing the state display:
  this._stateDisplay.find('.hideProofState').on('click', function() {
      self._stateDisplay.addClass('hidden');
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
        @mainControl.setSteps(Toy.decodeSteps(data.proofState));
      }
    } else {
      proofToyState.data.proofEditors[self.proofEditorId] = self.data;
    }
  }
  proofToyState.onDataReady(Toy.withErrorReporting.bind(null, loadData));
}

/**
 * Add a step to the proof.
 */
ProofEditor.prototype.addStep = @(step) {
  @mainControl.addStep(step);
};

/**
 * Gets the state of the proof, in string form.
 */
ProofEditor.prototype.getStateString = @() {
  return Toy.encodeSteps(@mainControl.steps)
};

/**
 * Sets the state of the proof from a string as returned by
 * getStateString.
 */
ProofEditor.prototype.setStateFromString = @(encoded) {
  var steps = Toy.decodeSteps(encoded);
  @mainControl.setSteps(steps);
};

/**
 * Sets the steps to the given array of non-renderable steps.
 */
ProofEditor.prototype.setSteps = @(steps) {
  var rendered = steps.map(@{step. step.copyStep()});
  @mainControl.setSteps(rendered);
};

/**
 * Save the proof state to the the proof's text area and the
 * document's data store.  Normally use the proofChanged method rather
 * than calling this directly, avoiding redundant work.
 */
ProofEditor.prototype.saveState = function() {
  var text = this.getStateString();
  this._stateArea.value = text;
  this.data.proofState = text;
  proofToyState.store();
};

/**
 * Attempts to restore the proof state from the proof's text area.
 */
ProofEditor.prototype.restoreState = function() {
  var string = this._stateArea.value;
  assert(string, 'No proof state recorded');
  this.setStateFromString(string);
};

ProofEditor.prototype.setEditable = @(value) {
  @mainControl.setEditable(value);
};

ProofEditor.prototype.showSaveRestore = @(value) {
  @mainControl.stepEditor.showSaveRestore(value);
};

ProofEditor.prototype.displayShowAll = @(value) {
  @mainControl.stepEditor.displayShowAll(value);
};

//// PROOF CONTROL

// TODO: Extend these to support proof steps that can take more
// than one selection.

/**
 * Construct a ProofControl.
 *
 * Optional single argument, a map, currently only interprets
 * 'stepPrefix' to initialize the stepPrefix property.
 *
 * Properties:
 *
 * steps: an array of the _rendered_ steps displayed.
 *
 * node: Node containing the entire rendering of the proof.  This has
 * CSS class proofDisplay and the ProofControl as the value of its
 * data('proofControl').  Only ProofControl nodes should have the
 * proofDisplay class.
 *
 * stepPrefix: string prefixed to each step number, defaults to
 * an empty string.  Set only during initialization.
 *
 * Other properties should be considered private.
 *
 * A step is an Expr, either rendered or unrendered.  Unrendered steps
 * are the top-level sentences of a proof, with properties added by
 * Expr.justify.
 *
 * Note that the stepNumber property of a step depends on its position
 * in its ProofControl's steps array, so it must be a property of a
 * _rendered_ step.
 *
 * TODO: Consider supporting a set of renderings per unrendered proof
 * step.
 */
function ProofControl(properties) {
  properties = properties || {};
  var controller = this;
  this.steps = [];
  // Set (array) of selected steps.
  // TODO: Implement this.
  this.selections = [];
  // Single selected step when exactly one is selected, or null.
  this.selection = null;
  // Prefix string for each step.
  this.stepPrefix = properties.stepPrefix || '';

  // ID of element to use for saving/restoring proof state.
  // TODO: Make the textarea part of the ProofControl.
  this.textAreaId = 'proofState';

  // Only official "proof nodes" are permitted to have class proofDisplay.
  var jq = $('<table class=proofDisplay><tr><td>' +
             '<div class=stepsParent><div class=proofSteps></div></div>' +
             '</table>');
  this.node = dom(jq);
  jq.data('proofControl', this);
  var stepsParent = jq.find('.stepsParent');
  this._stepsJQ = jq.find('.proofSteps');
  this.stepEditor = new Toy.StepEditor(this);
  jq.find('td').append(this.stepEditor.jq);

  this.setEditable(false);

  /* Omit this unused code until a jQuery counterpart to
     Y.Overlay is found.
  // Create an overlay to display step details when hovered.
  this.hoverOverlay = new Y.Overlay({
      width: '80%',
      bodyContent: 'Sample overlay content',
      zIndex:2
  });
  this.hoverOverlay.render(stepsParent);
  this.hoverOverlay.hide();
  */

  // Set up handling of mouseover and mouseout events.
  jq.on('mouseover', exprHandleOver);
  jq.on('mouseout', exprHandleOut);
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
  var stepsJQ = this._stepsJQ;
  this.steps.forEach(function(step) {
    step.original.rendering = null;
  });
  stepsJQ.html('');
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
  var self = this;
  // Give the steps numbers from 1 to N.
  this.steps.forEach(function(step, i) {
    // Fix up the step number and its display.
    step.stepNumber = (Toy.showOrdinals
                       ? step.ordinal
                       : self.stepPrefix + (i + 1));
    renderStepNumber(step);
  });
  // TODO: This will also need to support renumbering of any step
  // detail displays.
};  

/**
 * Render's the step number into its element of class "stepNumber",
 * and fixes up its elements of class "stepReference" to contain the
 * stepNumber of the corresponding dependency.
 */
function renderStepNumber(step) {
  $(step.stepNode).find('.stepNumber').text(step.stepNumber);
  // Fix up references made by the step.  (These should all be prior
  // steps.)
  var deps = getRenderedDeps(step);
  $(step.stepNode).find('.stepReference').each(function(index) {
      $(this).text(deps[index].rendering.stepNumber);
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
  copy.rendering = copy;
  step.original = step;
  copy.original = step;
  this.steps.push(copy);
  copy.stepNumber = (Toy.showOrdinals
                     ? step.ordinal
                     : this.stepPrefix + this.steps.length);
  var stepNode = renderStep(copy, this);
  renderStepNumber(copy);
  this._stepsJQ.append(stepNode);
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
  $(toRemove.stepNode).remove();
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
  this.stepEditor.jq.toggle(state);
}


// STEP SELECTION

/**
 * Unconditionally select the step, no other action.
 */
ProofControl.prototype.selectStep = function(step) {
  $(step.stepNode).addClass('selected');
  this.selection = step;
};

/**
 * Unconditionally deselect any selected step and any
 * selected expression in it.
 */
ProofControl.prototype.deselectStep = function() {
  var step = this.selection;
  if (step) {
    $(step.stepNode).removeClass('selected');
    this.selection = null;
    this.deselectExpr(step);
  }
};

/**
 * Unconditionally select the expr, no other action.
 */
ProofControl.prototype.selectExpr = function(expr) {
  var step = getProofStep(expr);
  $(expr.node).addClass('selected');
  step.selection = expr;
};

/**
 * Unconditionally deselect any selected expr in the
 * step, no other action.
 */
ProofControl.prototype.deselectExpr = function(step) {
  var expr = step.selection;
  if (expr) {
    $(expr.node).removeClass('selected');
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
var _turnstile = '\u22a6';

/**
 * Create and return a DOM node to display the renderable step within
 * the given controller.  Assumes that the renderable step is already
 * inserted into the controller's steps array.
 *
 * This also sets up event handlers for click
 * and hover events within the step.  Does not insert the new node
 * into the document.
 *
 * The rendering is structured as follows:
 *
 * - Each rendered expression and subexpression has a "node" property
 *   that refers to a DOM node with its rendering.
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
  var delHtml = (controller.editable
                 ? ('<input type=button class=deleteStep value="x"' +
                    ' title="Delete step">')
                 : '');
  var stepJQ =
    $('<div class=proofStep>' +
      delHtml +
      '<span class=stepNumArea>(<span class=stepNumber></span>)</span> ' +
      '<span class=wff></span>' +
      '<span class=stepInfo></span>' +
      '</div>');
  stepJQ.data('proofStep', step);
  step.stepNode = dom(stepJQ);
  var elide = wantLeftElision(step, controller);
  step.hasLeftElision = elide;
  var wffJQ = $(renderAsStep(step));
  stepJQ.find('.wff').empty().append(wffJQ);

  // TODO: Consider up these handlers in an ancestor node by delegation.
  // Set up click handlers for selections within the step.
  wffJQ.on(TOUCHDOWN,
       // This implements a policy of one selection per proof step.
       // TODO: Implement such policies in the proof controller.
       function(event) {
         controller.handleExprSelection(getEffectiveSelection(event.target));
         event.preventDefault();
       });
  stepJQ.on(TOUCHDOWN,
       function(event) {
         controller.handleStepClick(getProofStep(event.target));
       });

  stepJQ.find('.stepInfo').html(formattedStepInfo(step));

  // "Hover" events can come in slightly out of order as we track both
  // an inner and outer element.  Straighten this out by maintaining
  // a count of net in/out events and considering the mouse "in" when
  // the net is exactly 1.
  var netHovers = 0;
  function hover(diff, event) {
    var previous = netHovers == 1;
    netHovers += diff;
    var current = netHovers == 1;
    if (current != previous) {
      hoverStep(step, current == 1 ? 'in' : 'out', event);
    }
  }    
  // Set up "hover" event handling on the stepNode.
  stepJQ
    .hover(
           // Call hoverStep, passing these arguments as well as the event.
           hover.bind(null, 1),
           hover.bind(null, -1));
  // We count the wffJQ as outside for this purpose.
  wffJQ
    .hover(
           // Call hoverStep, passing these arguments as well as the event.
           hover.bind(null, -1),
           hover.bind(null, 1));

  var deleter = stepJQ.find('.deleteStep');
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
          // Fix up all highlighting by pretending the mouse moved out.
          // Deleting the node will not trigger the mouse out event.
          hoverStep(step, 'out');
          controller.removeStepAndFollowing(step);
          controller.proofChanged();
        }
      });
  }
               
  // Clicking on a ruleName "link" shows the subproof when subproofs
  // are enabled.
  var target = stepJQ.find('span.ruleName[class~="link"]');
  if (target.length && Toy.modes.subproofs) {
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
  return dom(stepJQ);
}

/**
 * Searches up the DOM tree for a hovered expr or fullExpr node,
 * depending on the selection mdoe, that is hovered.  Returns the expr
 * for that node.
 * 
 * Argument is the target node of a selection event.
 */
function getEffectiveSelection(node) {
  var selector = (Toy.simplifiedSelections
                  ? '.fullExpr.hovered' :
                  '.expr.hovered');
  // Include the node itself in the search.
  var selected = dom($(node).closest(selector));
  if (selected) {
    return getExpr(selected);
  } else {
    Toy.logError('No selectable node found');
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
 * DOM node, returning the node.  Omits surrounding parens if the step
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
    var hyps = step.getLeft();
    if (Toy.suppressRealTypeDisplays) {
      hyps = omittingReals(hyps);
    }
    if (hyps) {
      step.node = renderHyps(step.getLeft());
      var wffJq = $(step.node);
    } else {
      // Must we make the wffJq if there are hyps, but none visible?
      var wffJq = exprJq();
      step.node = dom(wffJq);
    }
    wffJq.append(renderMain(step));
    markAsFullExpr(wffJq);
    return dom(wffJq);
  } else {
    return renderMain(step);
  }
};

/**
 * Renders the "main" part of a renderable step, meaning everything
 * but the hypotheses.  Currently gives special treatment to equations
 * starting with rules.consider and immediately following steps.
 * Returns a new DOM node that renders it.
 */
function renderMain(step) {
  var main = step.unHyp();
  if (main.isCall2('=')) {
    if (step.ruleName == 'consider') {
      var jq = exprJq();
      main.node = dom(jq);
      jq.append(main.getRight()._render(true));
      jq.append(textNode(' = '));
      jq.append('<span class=ellipsis>&hellip;</span>');
    } else {
      if (step.hasLeftElision) {
        var jq = exprJq();
        main.node = dom(jq);
        jq.append('<span class=ellipsis>&hellip;</span>');
        jq.append(textNode(' = '));
        jq.append(main.getRight()._render(true));
      } else {
        var jq = main._render(true);
      }
    }
    return dom(jq);
  } else {
    return dom(main._render(true));
  }
}

/**
 * Walk through the expression as a set of hypotheses, rendering into
 * a new Expr DOM node, returning the node.
 */
function renderHyps(expr) {
  var topJq = exprJq();
  var hypsNode;
  if (Toy.suppressRealTypeDisplays) {
    expr = omittingReals(expr);
  }
  function render(expr) {
    if (expr.sourceStep) {
      var jq = exprJq();
      expr.node = dom(jq);
      // Note that this requires the unrendered proof step to be already
      // linked to a rendering with proper stepNumber:
      jq.append(expr.sourceStep.rendering.stepNumber);
      hypsNode.append(jq);
    } else if (expr.isCall2('&')) {
      render(expr.getLeft());
      hypsNode.append(textNode(', '));
      var rhs = expr.getRight();
      if (rhs.isCall2('&')) {
        hypsNode.append(textNode('('));
        render(rhs);
        hypsNode.append(textNode(')'));
      } else {
        render(rhs);
      }
    } else {
      hypsNode.append(expr._render(true));
    }
  }
  if (expr) {
    hypsNode = $('<span class=assumptions></span>');
    render(expr);
    hypsNode.append(':');
    topJq.append(hypsNode);
  }
  return dom(topJq);
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
          result = Toy.infixCall(result, '&', hyp);
        } else {
          result = hyp;
        }
      }
    });
  return result;
}

/**
 * Build and return a jQuery of class "expr".
 */
function exprJq() {
  return $('<span class=expr></span>');
}

/**
 * Returns an array CSS class names to add to an Expr node for a
 * variable having the specified name.
 */
function specialClasses(name) {
  if (Toy.isVariable(name)) {
    return ['italic'];
  }
  if (name === 'T' || name === 'F') {
    return ['trueFalse'];
  }
  return [];
}

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

/**
 * Marks the given JQ as a "full expr", selectable in the
 * simplified selections mode, and highlighted on hover in
 * that mode.
 */
function markAsFullExpr(jq) {
  jq.addClass('fullExpr');
}

// _render(omit)
//
// Render this expression into a new DOM node, returning a jQuery
// object for the node.  Sets the expression's "node" property to
// refer to the DOM node created to enclose this expression.  Should
// be done only once to any given expression.  Helper for the render
// method.  (Not public)
//
// If the optional "omit" argument is true and this is a Call, omit
// the enclosing parentheses.
// 
//

Var.prototype._render = function(omit) {
  var jq = exprJq();
  this.node = dom(jq);
  if (Toy.isVariable(this.name)) {
    markAsFullExpr(jq);
  }
  var name = this.toUnicode();
  specialClasses(name).forEach(function(cl) { jq.addClass(cl); });
  jq.text(name);
  return jq;
};

Call.prototype._render = function(omit) {
  var jq = exprJq();
  this.node = dom(jq);
  // Only parenthesize uses of quantifiers in case of step tracking.
  // TODO: Remove this special case and omit parens around all ordinary
  // function calls that appear as args to infix operators.  Presumably
  // this code is correct for (not (forall ... )) because "forall"
  // displays as a unary operator.
  if (this.fn instanceof Var &&
      (this.fn.name == 'forall' || this.fn.name == 'exists')) {
    omit = true;
  }
  var stepNum = (Toy.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  omit = omit && !stepNum;
  if (!omit) {
    if (Toy.trackSourceSteps) {
      if (this.sourceStep) {
        jq.append('$');
      }
      if (stepNum) {
        jq.append(stepNum);
      }
    }
    jq.append('(');
  }
  if (this.fn instanceof Call && this.fn.fn instanceof Var) {
    // This is a call on a named function of two arguments.
    if (Toy.isInfixDesired(this.fn.fn)) {
      // Non-alphabetic characters: use infix: "x + y"
      var fnJq = exprJq();
      this.fn.node = dom(fnJq);
      fnJq.append(this.fn.arg._render());
      fnJq.append(space());
      fnJq.append(this.fn.fn._render());
      jq.append(fnJq);
      jq.append(space());
      jq.append(this.arg._render());
    } else {
      // Alphabetic characters: function comes first.
      var fnJq = exprJq();
      this.fn.node = dom(fnJq);
      fnJq.append(this.fn.fn._render());
      fnJq.append(space());
      fnJq.append(this.fn.arg._render());
      jq.append(fnJq);
      jq.append(space());
      jq.append(this.arg._render());
    }
    markAsFullExpr(jq);
  } else if (this.fn instanceof Var && Toy.isInfixDesired(this.fn)) {
    // Infix operator, but only one argument: "x +"
    jq.append(this.arg._render());
    jq.append(space());
    jq.append(this.fn._render());
  } else if (this.fn instanceof Var && !this.fn.displaysIdentifier()) {
    // Function call with non-identifier operator.
    // Display the function adjacent to its argument, but precede both
    // with a non-breaking space to the left to help the user select
    // this expression, and to set them off from preceding infix operator
    // or other text.
    jq.append(document.createTextNode('\u00a0'));
    jq.append(this.fn._render());
    jq.append(this.arg._render());
    markAsFullExpr(jq);
  } else {
    // Normal function call: "f x"
    jq.append(this.fn._render());
    jq.append(space());
    jq.append(this.arg._render());
    markAsFullExpr(jq);
  }
  if (!omit) {
    jq.append(')');
  }
  return jq;
};

Lambda.prototype._render = function(omit) {
  var jq = exprJq();
  this.node = dom(jq);
  markAsFullExpr(jq);
  var stepNum = (Toy.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  if (stepNum) {
    jq.append('$' + stepNum);
  }
  jq.append('{');
  jq.append(this.bound._render());
  jq.append(textNode('. '));
  var bodyJq = this.body._render(true);
  markAsFullExpr(bodyJq);
  jq.append(bodyJq);
  jq.append('}');
  return jq;
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
      step.ruleDeps.forEach(function(dep) { visitWithDeps(dep); });
    }
  }
  visitWithDeps(step);
  result.forEach(function(step) { delete step.__visited; });
  result.sort(function(s1, s2) {
      return s1.ordinal - s2.ordinal;
    });
  return result;
}

/**
 * Renders details of the given rendered proof step and sets the
 * subproofControl property of the step to the ProofControl for the
 * subproof.
 */
function renderSubproof(step) {
  var controller = getProofControl(step);
  controller.steps.forEach(clearSubproof);
  var jq;
  if (step.ruleName == 'theorem') {
    jq = renderInference(Toy.getTheorem(step.ruleArgs[0]));
  } else {
    jq = renderInference(step);
  }
  step.subproofControl = jq.data('proofControl');
  // Append it to the top node of the proof + subproofs.
  var container = getTopProofContainer(step);
  container.append(jq);
}

/**
 * Clear any subproof of this step and any subproofs of its steps
 * recursively.  Remove the subproofControl property from the step.
 */
function clearSubproof(step) {
  var controller = step.subproofControl;
  delete step.subproofControl;
  if (controller) {
    controller.steps.forEach(function(step) {
        // Record that the rendering is gone.
        step.original.rendering = null;
        // Clear any rendered subproof for the step.
        clearSubproof(step);
      });
    var container = $(controller.node).closest('.inferenceDisplay');
    container.remove();
  }
}

/**
 * Returns an array of the dependencies to show for the given step.
 */
function getRenderedDeps(step) {
  if (step.ruleDeps.length > 1) {
    return step.ruleDeps;
  }
  var result = [];
  var node = getStepNode(step);
  step.ruleDeps.forEach(function(dep) {
      var depNext = getStepNode(dep.rendering).nextElementSibling;
      // In the future we may insert the step's node early,
      // so we do the != test here.
      if (depNext && depNext != node) {
        result.push(dep);
      }
    });
  return result;
}

/**
 * True iff step1 and step2 are rendered adjacent to each other,
 * with step1 first.  As a sop to current practice, allow step1
 * to have no next step, and step2 not linked into the DOM.
 */
function adjacentSteps(step1, step2) {
  var j1 = $(getStepNode(step1.rendering));
  var j2 = $(getStepNode(step2.rendering));
  // TODO: Link in new steps before rendering, and eliminate this
  // special test.
  // Is j2 linked into the DOM?
  var p2 = j2.closest('body');
  return (p2.length == 0 && j1.next().length == 0) || j1.next().is(j2);
}

/**
 * Returns HTML text describing the step, displayed after the formula
 * on each proof line.  This is an HTML description of a proof step
 * followed by references to other steps this one depends on.  This
 * finds the description in the rule's 'description' property as a
 * template.  Expands paired braces using expandMarkup.  Any text
 * after a ";;" pair is formatted as arguments to the rule.  
 *
 * Automatically formats site-type dependencies as "in step ... ".
 * If there is no markup that refers to steps, formats other step
 * dependencies as "using step(s) ... ".
 */
function formattedStepInfo(step) {
  var info = Toy.rules[step.ruleName].info;
  var description = info.description;
  var useDefault = true;
  if (description[0] === '=') {
    useDefault = false;
    // Expand the description with the named function.
    var fn = stepFormatters[description.slice(1)];
    assert(fn, @{. 'No step formatter "' + description.slice(1) + '"'});
    description = fn(step);
  }
  // Use default step refs only if there are no formatting directives;
  // no original "=", no ";;", and no braces.
  if (description.match(/\{|;;/)) {
    useDefault = false;
  }
  var d1 = description;
  var d2 = '';
  var parts = d1.match(/(.*?);;(.*)$/);
  if (parts) {
    d1 = parts[1];
    d2 = parts[2];
  }
  // Expand any markup within the description.
  d1 = d1.replace(/[{].*?[}]/g,
                  @{markup. expandMarkup(step, markup)});
  d2 = d2.replace(/[{].*?[}]/g,
                  @{markup. expandMarkup(step, markup)});
  var comment = (Toy.escapeHtml(info.comment || '') +
                 ' (&quot;' + step.ruleName + '&quot;)');
  var classes = (step.details && Toy.modes.subproofs
                 ? 'ruleName link'
                 : 'ruleName');
  var result =  ('<span class="' + classes + '" title="' + comment + '">'
                 + d1 + '</span>' + d2);
  return result + (useDefault ? defaultStepRefs(step, description) : '');
}

/**
 * Computes replacement text for rule description markup.  Appearances
 * of {step}, {step1}, {step2} expand to the step number of the step
 * argument.  Also supports {equation}, {implication}.
 *
 * Appearances of {term*} display as the term; {var} as the variable
 * name, {site} as the term at the site.  Unknown markup passes
 * through, e.g. lambdas -- {x. f x}.
 */
function expandMarkup(step, markup) {
  // Given an array of places, as stored in the value of an "inputs"
  // property of a rule, and an index into them, returns a step number
  // or phrase ending in a step number, for the nth element.  Also
  // accepts a number for places in place of a 1-element array.
  function stepNumber(places, index) {
    if (places === undefined) {
      return '?';
    }
    var place = (typeof places === 'number' && index === 0
                 ? places
                 : places[index]);
    if (place) {
      var stepArg = step.ruleArgs[place - 1];
      if (markupRest && adjacentSteps(stepArg, step)) {
        return '';
      } else {
        return markupRest + stepArg.rendering.stepNumber;
      }
    } else {
      // If the index is out of range return '?'.
      return '?';
    }
  }
  var info = Toy.rules[step.ruleName].info;
  if (markup.match(/^\{[a-z][_0-9]*[.]/)) {
    // It looks like a lambda, not markup!
    return markup;
  }
  var matches = markup.match(/^\{(.*? ?)([a-zA-Z0-9]+)\}$/);
  var markupRest = matches[1];
  var markupName = matches[2];
  switch (markupName) {
  case 'step':
  case 'step1':
    return stepNumber(info.inputs.step, 0);
  case 'step2':
    return stepNumber(info.inputs.step, 1);
  case 'equation':
    return stepNumber(info.inputs.equation, 0);
  case 'implication':
    return stepNumber(info.inputs.implication, 0);
  case 'siteStep':
    return stepNumber(info.inputs.site, 0);
  case 'term':
  case 'terms':
    var places = info.inputs.term;
    // Convert number to array.
    if (typeof places === 'number') {
      places = [places];
    }
    var terms = places.map(function(place) {
        return Toy.mathMarkup(Toy.toUnicode(step.ruleArgs[place - 1]));
      });
    return terms.join(', ');
  case 'var':
    var place = info.inputs.varName[0] || info.inputs.varName;
    return Toy.mathMarkup(Toy.toUnicode(step.ruleArgs[place - 1]));
  case 'site':
    var place = info.inputs.site[0] || info.inputs.site;
    var siteStep = step.ruleArgs[place - 1];
    var term = siteStep.locate(step.ruleArgs[place]);
    return Toy.mathMarkup(term.toUnicode());
  default:
    // Allow lambdas to pass through, e.g. {x. T}.
    return markup;
  }
}

/**
 * Generate HTML to render a list of steps used by the given step
 * according to display policy.  Currently this is to show "site"
 * dependencies as "in" and others as "using", but only when not
 * immediately preceding the given step.
 */
function defaultStepRefs(step, description) {
  var siteRefs = [];
  var stepRefs = [];
  var args = step.ruleArgs;
  Toy.eachArgType(step.ruleName, function(where, type) {
      var arg = args[where];
      if (type in Toy.siteTypes && !adjacentSteps(arg, step)) {
        siteRefs.push(arg);
      } else if (type in Toy.stepTypes && !adjacentSteps(arg, step)) {
        stepRefs.push(arg);
      }
    });
  var html = '';
  if (siteRefs.length) {
    html += siteRefs.length > 1 ? ' in steps ' : ' in step ';
    html += siteRefs.map(@{s. s.rendering.stepNumber}).join(', ');
  }
  if (stepRefs.length) {
    html += stepRefs.length > 1 ? ' using steps ' : ' using step ';
    html += stepRefs.map(@{s. s.rendering.stepNumber}).join(', ');
  }
  return html;
}


/**
 * Formatting functions for steps.  The function should return
 * an HTML description string.
 */
var stepFormatters = {
  definition: function(step) {
    var result = 'definition of ' + Toy.toUnicode(step.ruleArgs[0]);
    if (step.ruleArgs.length == 2) {
      result += ' ' + step.ruleArgs[1];
    }
    return result;
  },
  changeVar: function(step) {
    var step0 = step.ruleArgs[0];
    var path = step.ruleArgs[1];
    var target = step0.locate(path);
    return 'rename ' + target.bound;
  },
  instForall: function(step) {
    var step0 = step.ruleArgs[0];
    // Get the bound variable of the arg to forall.
    var bound = step0.locate('/main/arg/bound');
    return 'substitute for ' + bound;
  },
  simpleApply: function(step) {
    var step0 = step.ruleArgs[0];
    var path = step.ruleArgs[1];
    var target = step0.locate(path);
    assert(target instanceof Toy.Call);
    assert(target.fn instanceof Toy.Lambda);
    return 'substitute for ' + target.fn.bound.name;
  },
  // TODO: Treat "apply" as a rewrite using arbitrary definitions.
  apply: function(step) {
    var step0 = step.ruleArgs[0];
    var path = step.ruleArgs[1];
    var target = step0.locate(path);
    if (target instanceof Toy.Call) {
      var fn = target.fn;
      if (fn instanceof Toy.Lambda) {
        return 'substitute for ' + target.fn.bound.name;
      } else if (target.isCall2()) {
        return 'apply definition of ' + target.getBinOp().toString();
      } else {
        return 'apply definition of ' + fn.toString();
      }
    } else {
      return 'apply: not a Call';
    }
  },
  instMultiVars: function(step) {
    var map = step.ruleArgs[1];
    var keys = [];
    for (key in map) {
      keys.push(key);
    }
    return 'substitute for ' + keys.join(', ') + ';; in step {step}';
  },
  tautInst: function(step) {
    var taut = step.ruleArgs[0];
    if (typeof taut === 'string') {
      taut = Toy.parse(taut);
    }
    return 'tautology ' + Toy.mathMarkup(taut.toUnicode());
  }
};

/**
 * Given a proof step, renders a header and the proof steps
 * of its as-yet-unrendered details within a container DIV with CSS
 * class inferenceDisplay.  Sets the 'proofControl' data property of
 * the node to refer to the new ProofControl.  If the step is
 * rendered, the details are rendered with step numbers relative to
 * its step number.
 *
 * Returns the new container jQuery DIV.
 */
function renderInference(step) {
  var steps = unrenderedDeps(step.details);
  var prefix = step.stepNumber ? step.stepNumber + '.' : '';
  var controller = new ProofControl({stepPrefix: prefix});
  controller.setSteps(steps);
  var comment = Toy.escapeHtml(Toy.rules[step.ruleName].info.comment || '');
  var pruf = step.ruleArgs.length ? 'Rule ' : 'Proof of ';
  jq = $('<div class=inferenceDisplay></div>');
  jq.append('<div class=proofHeader><b>' + pruf
              + step.ruleName + '</b>'
              + computeHeaderArgInfo(step) + '<br>'
              + '<i>' + comment + '</i></div>');
  jq.append(controller.node);
  jq.data('proofControl', controller);
  return jq;
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
function renderProof(step, where, millis, nSteps) {
  where = $(where);
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
    where.append('<div class=proofHeader>' + stats + '</div>');
  }
  where.append($(controller.node));
  return controller;
}

/**
 * Helper for renderInference, computes arguments display string for
 * the header display of a subproof.
 *
 * TODO: Re-think and rewrite this, probably using Toy.eachArgType.
 *   Indicate sites in steps in some user-friendly way.
 */
function computeHeaderArgInfo(step) {
  var argInfo = '';
  for (var i = 0; i < step.ruleArgs.length; i++) {
    var arg = step.ruleArgs[i];
    var argText;
    if (arg instanceof Toy.Expr) {
      argText = arg.toString();
    } else if (typeof arg == 'string' && arg[0] != '/') {
      argText = arg;
    } else if (typeof arg == 'string' || arg instanceof Toy.Path) {
      // Ignore paths and strings that look like paths.
      continue;
    } else {
      argText = Toy.debugString(arg);
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
 * within the step or its DOM node.
 */
function getStepNode(expr) {
  var node = $(expr instanceof Toy.Expr ? expr.node : expr);
  return dom(node.closest('.proofStep'));
}

/**
 * Gets the proof step (Expr) of the step that renders
 * in part into the given DOM Node.  Also accepts an Expr of
 * a rendered proof.
 */
function getProofStep(node) {
  return $(getStepNode(node)).data('proofStep');
}

/**
 * Gets the DOM object of a rendered proof given the YUI node of
 * one of its steps or of an expression in a step.
 */
function getStepsNode(node) {
  return dom($(node).closest('.proofSteps'));
}

/**
 * Get a jQuery for the parent node containing the top-level proof and
 * subproofs where this rendered expr can be found.  That parent node
 * is currently not part of a ProofControl, but by convention should
 * contain only the top-level proof and its subproofs.
 */
function getTopProofContainer(expr) {
  var proofJq = $(expr.node).closest('.proofDisplay');
  var display = proofJq.closest('.inferenceDisplay');
  if (display.length === 0) {
    display = proofJq;
  }
  // TODO: Flag the parent as "proofContainer" and simply search for that.
  var parent = display.parent();
  return parent;
}

/**
 * Gets the ProofControl of a rendered term or step, or the node of
 * one.
 */
function getProofControl(expr) {
  var node = expr instanceof Toy.Expr ? expr.node : expr;
  var ancestor = $(node).closest('.proofDisplay');
  return ancestor.data('proofControl');
}


/**
 * Returns the expression associated with a DOM node.
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
  var selector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  var target = $(event.target);
  var exprJq = target.closest(selector);
  // Could be no elements in exprJq.
  exprJq.addClass('hovered');
  function isTarget(expr) {
    return expr.node == event.target;
  }
  var stepJq = exprJq.closest('.proofStep');
  if (stepJq.length) {
    var proofStep = stepJq.data('proofStep');
    var path = proofStep.pathTo(isTarget);
    hoverShowPath(proofStep, path);
  }
};

/**
 * Defines how to display the hovered path.  Highlighting of the
 * DOM node is handled elsewhere.
 */
function hoverShowPath(wff, path) {
  var displayJq = $('#hoverPath');
  if (displayJq.length) {
    // If there is no bottom panel, do nothing.
    var expr = wff.locate(path);
    var pathStr = path ? path.toString() : '';
    displayJq.html(pathStr);
  }
}

/**
 * Handle mouseouts on subexpressions.
 */
function exprHandleOut(event) {
  var selector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  var target = $(event.target).closest(selector) || $(event.target);
  target.removeClass('hovered');
  var displayJq = $('#hoverPath');
  if (displayJq) {
    // Do nothing if there is no bottom panel.
    displayJq.html('');
  }
};

/**
 * Adds the named CSS class to the DOM node.  For use in hover
 * handlers.  Currently does nothing if node is null, which occurs in
 * hypotheses.
 */
function addClass(node, className) {
  node && $(node).addClass(className);
}

/**
 * Removes the named CSS class from the DOM node.
 * For use in hover handlers.
 */
function removeClass(node, className) {
  node && $(node).removeClass(className);
}

/**
 * Event handler for "hover" events on proof steps.
 * Adds or removes highlighting for the step based on the direction.
 */
function hoverStep(step, direction, event) {
  var action = direction == 'in' ? addClass : removeClass;

  // Always add or remove the "hover" class to the step node
  // as the mouse goes in or out.
  var stepNode = getStepNode(step.node);
  action(stepNode, 'hover');

  doHoverOverlay(step, direction);

  // When entering a step, highlight all references to it.
  // When leaving remove highlights from all references.
  var container = getTopProofContainer(step);
  container.find('span.stepReference').each(function() {
    if (direction == 'in') {
      if (this.innerHTML == step.stepNumber) {
        $(this).addClass('referenced');
      }
    } else {
      $(this).removeClass('referenced');
    }
  });

  // Rule-specific hover actions, or default.
  var handler = getHoverHandler(step);
  if (handler) {
    // If there is a hover handler for this type of inference, apply it.
    handler(step, action);
  } else {
    // If no handler apply or remove default highlighting.
    step.ruleDeps.forEach(function(dep) {
      action(getStepNode(dep.rendering), 'dep');
    });
  }
}

/**
 * Returns a hover handler function for the step if any, or null.
 */
function getHoverHandler(step) {
  var handler = hoverHandlers[step.ruleName];
  if (handler) {
    return handler;
  } else if (Toy.rules[step.ruleName].info.isRewriter) {
    return hoverAsRewriter;
  } else {
    return null;
  }
}

/**
 * Highlights input sites as usual for rewrite rules.
 */
function hoverAsRewriter(step, action) {
  var selections = Toy.stepSites(step);
  // Highlight the input sites expressions for the step while hovered.
  selections.forEach(function(expr) {
    action(expr.node, 'site');
  });

  // Show the corresponding subexpressions of this step if possible.
  // Note: this is likely to require overrides in some rules.
  Toy.stepPaths(step).forEach(function(path) {
    try {
      action(step.locate(path).node, 'site');
    } catch(err) {
      Toy.logError(err);
    }
  });
}

/**
 * If enabled, build and show a "hover overlay" on hover, hide on exit.
 */
function doHoverOverlay(step, direction) {
  // NB: Hover overlays currently have no information in them,
  // but might be helpful in the future.
  if (Toy.useHoverOverlays) {
    /* Comment out unused functionality until jQuery counterpart
     * to YUI Overlay is found.
    var align = Y.WidgetPositionAlign;
    var overlay = getProofControl(step).hoverOverlay;
    if (direction == 'in') {
      overlay.set('align', {
          node: getStepNode(step.node), points: [align.TR, align.BR]});
      overlay.show();
    } else {
      overlay.hide();
    }
    */
  }
}

/**
 * Hover handler for "r" and "replace".
 */
function hoverReplace(step, action) {
  hoverAsRewriter(step, action);
  var args = step.original.ruleArgs;
  var eqnStep = args[0].rendering;
  action(getStepNode(eqnStep), 'dep');
}

// Arguments to the handler functions are an inference
// and the operation is "addClass" or "removeClass".
var hoverHandlers = {
  r: hoverReplace,
  replace: hoverReplace,
  rRight: hoverReplace,
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
  useDefinition: hoverReplace,
  instEqn: function(step, action) {
    var args = step.original.ruleArgs;
    // Input equation.
    var eqn = args[0].rendering;
    // Name of variable being instantiated.
    var varName = args[2].ruleName;
    action(getStepNode(eqn), 'dep');
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
    action(getStepNode(input), 'dep');
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
    action(getStepNode(input), 'dep');
    var body = input.arg.body;
    body.findAll(varName,
                 function(_var) { action(_var.node, 'occur'); },
                 step.unHyp(),
                 function(expr) { action(expr.node, 'new'); });
  }
};


//// OTHER UTILITY FUNCTIONS

function contains(array, item) {
  return array.indexOf(item) >= 0;
}

function addBottomPanel(jq) {
  jq = jq || $(document.body);
  var style = ('position: fixed; width: 100%; background-color: white; '
               + 'bottom:0px; left: 0em; border-top: 1px solid black');
  var div = $('<div id="bottomPanel" style="' + style + '"></div>');
  div.append('Path: <span id=hoverPath></span>');
  jq.append(div);
}


//// Export public names.

Toy.dom = dom;
Toy.eachArgType = eachArgType;
Toy.stepPaths = stepPaths;
Toy.stepSites = stepSites;

Toy.proofToyState = proofToyState;
Toy.ProofEditor = ProofEditor;
Toy.ProofControl = ProofControl;
Toy.showOrdinals = false;
Toy.renderInference = renderInference;
Toy.renderProof = renderProof;
Toy.addBottomPanel = addBottomPanel;
Toy.getStepNode = getStepNode;
Toy.getProofStep = getProofStep;
Toy.getStepsNode = getStepsNode;
Toy.getExpr = getExpr;

// For testing:
Toy._formattedStepInfo = formattedStepInfo;

// Global configuration variable for displaying extra information per
// step when hovered.
Toy.useHoverOverlays = false;

// Global parameter to suppress displaying hypotheses such as "(R x)".
Toy.suppressRealTypeDisplays = true;

// Detect if the device has a touch screen, e.g. a tablet.
// Mobile jQuery 1.1 does this same test.
Toy.hasTouchEvents = 'ontouchend' in document;

// Control whether to use an Autocompleter vs. plain SELECT element.
// To turn on use of the AutoCompleter, remove "false &".  This
// leaves it off in any case for touch screen systems.
Toy.useAutocompleter = false && !Toy.hasTouchEvents;

// Global parameter to suppress GUI selection of function names
// and the "Curried part" of an infix call.
Toy.simplifiedSelections = Toy.hasTouchEvents;

// Name of event when the user touches the screen or clicks the mouse.
// Note: when using 'mousedown' as the TOUCHDOWN event Chrome has been
// observed to unfocus the keyboard on the subsequent mouseup event,
// an unwanted effect.
var TOUCHDOWN = Toy.hasTouchEvents ? 'touchstart' : 'click';

// Override these properties on the page to get custom modes of
// display and/or operation.
Toy.modes = {
  subproofs: true
};

}, '0.1', {requires: ['array-extras', 'expr', 'step-editor', 'event-touch']});
