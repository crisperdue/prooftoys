// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

// This file implements rendering of proofs and proof steps.
// For the deductive system itself see theorems.js.

/**
 * Version of the jQuery $ function that type checks its input.
 */
function $(x) {
  if (arguments.length > 1) {
    return jQuery.apply(null, arguments);
  } else if (typeof x === 'string' ||
             typeof x === 'function' ||
             x.nodeType ||
             x === window ||
             x instanceof jQuery) {
    return jQuery(x);
  } else {
    throw new Error('Not a DOM node: ' + x);
  }
}
jQuery.extend($, jQuery);

// Set all of this up immediately on load, but avoiding changes
// to the global environment except in namespace "Toy".
(function() {

// Use the application's assert function.
var assert = Toy.assertTrue;

// Make the main classes available without "Toy."
var Expr = Toy.Expr;
var Atom = Toy.Atom;
var Call = Toy.Call;
var Lambda = Toy.Lambda;
var Step = Toy.Step;
var Bindings = Toy.Bindings;
var TermSet = Toy.TermSet;

// Test in context of rendering.js.
window.Rtest = function(x) {
  setTimeout(function() { console.log(window.Tval = eval(x)); });
};

/**
 * Converts a singleton jQuery object to its DOM node,
 * checking carefully that it is a jQuery singleton.
 */
function dom($node) {
  if ($node instanceof jQuery) {
    if ($node.length === 1) {
      return $node[0];
    } else {
      throw new Error('Not a jQuery object: ' + $node);
    }
  } else {
    throw new Error('Length not 1: ' + $node);
  }
}

/**
 * Setting up a "destroyed" handler on a node will cause the handler
 * to run when the node is removed from the DOM using jQuery's .remove
 * method, as in:
 *
 * $(node).on('destroyed', function() { "do stuff" })
 *
 * This could make it easier to manage information such as
 * associations between proof steps and their renderings.  The handler
 * fires as it is being unbound, so so avoid explicitly unbinding.
 */
jQuery.event.special.destroyed = {
  remove: function(o) {
    if (o.handler) {
      o.handler.apply(this, arguments);
    }
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
  assert(step.isProved(), 'Not a step: ' + step);
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
  assert(step.isProved(), 'Not a step: ' + step);
  var results = [];
  var args = step.ruleArgs;
  eachArgType(step.ruleName, function(position, type) {
    if (Toy.siteTypes.hasOwnProperty(type)) {
      var source = step.ruleArgs[position];
      if (source.rendering) {
        results.push(source.rendering.get(step.ruleArgs[position + 1]));
      }
    }
  });
  return results;
}


//// APPLICATION DATA STORAGE

var proofToyState = {

  // Global data to store in the hidden field named ToyStore.  Created
  // with an object/slot to hold all data for all ProofEditor objects
  // on the page.  Completely overwritten by the _load method.
  // The point of proofToyState is to manage this data.
  data: {proofEditors: {}},

  // Indicates whether the data slot has been filled in yet.
  loaded: false,

  // Global form element to store proofToyData.
  _toyStore: null,

  // Storing the state of all proof editors into the hidden textarea.

  /**
   * Save proofToyData into the document's data store so it will persist
   * across page load/unload.  Silently do nothing if there is no store
   * element.
   */
  store: function() {
    if (this._toyStore) {
      this._toyStore.value = JSON.stringify(this.data, null, 1);
    }
  },

  /**
   * Load all application data from the per-page store; runs just once.
   */
  init: function() {
    if (this.loaded) {
      return;
    }
    this.loaded = true;
    var storage = this._toyStore = $('#ToyStore')[0];
    if (storage) {
      var text = storage.value;
      if (text) {
        // Non-empty text.
        this.data = JSON.parse(text);
      }
    } else {
      console.log('No #ToyStore element.');
    }
  }
};


//// PROOF EDITOR

// TODO: Use events and event handlers to make cleaner separation
//   between ProofEditor, ProofDisplay, and StepEditor.  StepEditor
//   needs some kind of access to the array of proof steps to
//   translate step numbers to steps.  Perhaps ProofDisplay can notify
//   when its list of steps changes.

// Each instance has a numeric ID.
var nextProofEditorId = 1;

/**
 * Construct a proof displayer/editor, which is a composite made from
 * a ProofDisplay.  User interaction may also create additional
 * subproof ProofDisplay objects within this.
 *
 * Public properties:
 *
 * proofDisplay: ProofDisplay for the proof being edited.
 * containerNode: jQuery object for outermost DOM node for the display.
 * stepEditor: StepEditor for the proof being edited.
 * givens: array of boolean terms defining the problem, often
 *   equations (not steps).  Should only be set when the proof is
 *   empty.  Read it as a TermSet.
 * givenVars: object/set keyed by names of variables free in the givens;
 *   read-only.
 * solutions: If any of these expressions (or strings) is an alphaMatch
 *   with a step, announce the step as a solution.
 * standardSolution: If no explicit solutions given, but the result of
 *   a step solves for a variable (equal to a numeral or fraction),
 *   announce that the problem is solved.
 */
function ProofEditor() {
  var self = this;
  self._givens = new TermSet();
  self.givenVars = {};
  self.solutions = [];
  self.standardSolution = true;
  // Set the ID.
  this.proofEditorId = nextProofEditorId++;
  // Data of this ProofEditor to remember across page load/unload,
  // representable in JSON.
  this.data = {};
  self.__mainDisplay = new ProofDisplay();
  self.__mainDisplay.proofEditor = self;
  this.proofDisplay = self.__mainDisplay;
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
  // The proofButtons class is used in some examples.
  self.__proofButtons = $('<div class=proofButtons/>');
  var saveRestore =
    // Toggling the proof state display visibility with a button.
    $('<input type=button '
      + 'value="Save/restore proof ..." '
      + 'title="Save or restore proof state">');
  self.__proofButtons.append(saveRestore);
  saveRestore.on('click', function() {
      self._stateDisplay.toggleClass('hidden');
      dom($(self._stateDisplay).find('textarea')).select();
    });
  var clearProof = $('<input type=button value="Clear proof">');
  self.__proofButtons.append(clearProof);
  var selHtml = (' <span>show options for</span> ' +
                 '<select class=rulesToShow>' +
                 '<option value=algebra>algebra' +
                 '<option value=general>general reasoning' +
                 '<option value=all>all available' +
                 '</select>');
  self.__proofButtons.append(selHtml);

  self.$rulesMode = self.__proofButtons.find('.rulesToShow');

  var stepEditor = new Toy.StepEditor(this);
  self.stepEditor = stepEditor;

  clearProof.on('click', function() { self.clear(); });
  // Step editor has state controlling whether to show all rules.
  self.$rulesMode.on('change', function(event) {
      stepEditor.showRuleType = this.value;
      stepEditor.stepSuggester.refresh();
      stepEditor.ruleMenu.refresh();
      stepEditor.reset();
    });
  self.$rulesMode.trigger('change');
  // The ruleStats are visible except when a proof is brand new and
  // there is nothing to show.
  var ruleStats = $('<div class="ruleStats invisible">Last rule ' +
                    '<span class=ruleTime></span> msec, ' +
                    '<span class=ruleSteps></span> steps</div>');
  // This element is for messages about status of solving the problem.
  var $status = $('<div class="solutionStatus hidden"/>');
  self.$status = $status;
  // Top-level element of the proof editor display:
  this.containerNode = $('<div class=proofEditor></div>');
  this.containerNode
    .append(self.__proofButtons)
    .append(ruleStats)
    .append(this._stateDisplay)
    .append(self.__mainDisplay.node)
    .append(self.$status)
    .append(stepEditor.$node);
  this.setEditable(true);

  // If the proof has changed, save its state soon.
  this._refresher = new Toy.Refresher(function() {
      self._updateGivens();
      self.saveState();
      // Set (or clear) the message in the $status box.
      var steps = self.proofDisplay.steps;
      var $status = self.$status;
      var len = steps.length;
      if (len) {
        var step = steps[len - 1];
        var message = self.progressMessage(step);
        $status.empty();
        $status.append(message);
        $status.toggleClass('hidden', !message);
      } else {
        $status.toggleClass('hidden', true);
      }
    });

  // Handler for the "restore proof" button.  Restores proof state from
  // the text area and saves global state.
  function restoreProof() {
    Toy.withErrorReporting(function() {
        self.restoreState();
        proofToyState.store();
        self._stateDisplay.toggleClass('hidden', true);
      });
  }
  this._stateDisplay.find('.restoreProof').on('click', restoreProof);

  // Closing the state display:
  this._stateDisplay.find('.hideProofState').on('click', function() {
      self._stateDisplay.addClass('hidden');
    });

  // Aliases this ProofEditor's "data" property to the global data
  // associated with its proofEditorId in proofToyState.  Updates the
  // state of the proof itself if there is any global data.
  //
  // If the global data has no information about this, just links the
  // existing value into the global data.
  function loadData() {
    proofToyState.init();
    var data = proofToyState.data.proofEditors[self.proofEditorId];
    if (data) {
      self.data = data;
      if (data.proofState) {
        self.__mainDisplay.setSteps(Toy.decodeSteps(data.proofState));
      }
    } else {
      proofToyState.data.proofEditors[self.proofEditorId] = self.data;
    }
  }
  // Soon load remembered proof state, but complete the constructor
  // and any following initializations.
  Toy.soonDo(function() { return Toy.withErrorReporting(loadData)});

  // Clicks in arbitrary areas of the document remove any selection.
  // And clear any proof errors field.
  $(document).on('click', function(event) {
    if ($(event.target).closest('.proofEditor').length == 0) {
      // Not in a ProofDisplay's area.
      self.__mainDisplay.deselectStep();
      stepEditor.$proofErrors.hide();
    }
  });
}

/**
 * Empties the proof and problem statement for a fresh start.
 */
ProofEditor.prototype.clear = function() {
  this.stepEditor.showRules = [];
  this.stepEditor.reset();
  this.proofDisplay.setSteps([]);
};

/**
 * Define the "givens" property as a virtual property.  Setting it has
 * the side effect of modify the "givenVars" property as well, which
 * should be treated as readonly.  If not set explicitly through the
 * setter, givens will come from uses of the "given" rule.
 */
Object.defineProperty(ProofEditor.prototype, "givens", {
    get: function() { return this._givens; },
    set: function(g) {
      assert(this.proofDisplay.steps.length == 0, 'Proof is not empty');
      var wff;
      for (var i = 0; i < g.length; i++) {
        var g1 = Toy.termify(g[i]);
        this._givens.add(g1);
        wff = (wff ? Toy.infixCall(wff, '&', g1) : g1);
      }
      if (wff) {
        this.addStep(Toy.rules.given(wff));
      }
      this._updateGivenVars();
    }
  });

/**
 * Recompute the problem givens from the first proof step
 * if its rule name is "given".
 */
ProofEditor.prototype._updateGivens = function() {
  var self = this;
  var steps = self.proofDisplay.steps;
  self._givens.clear();
  function add(given) { self._givens.add(given); }
  if (steps.length > 0) {
    var step = steps[0];
    if (step.ruleName === 'given') {
      step.wff.getMain().getRight().scanConjuncts(add);
    }
  }
  self._updateGivenVars();
};

/**
 * Update the givenVars to match the (possibly changed) set of givens
 * of this problem.
 */
ProofEditor.prototype._updateGivenVars = function() {
  // An object/set with names of all variables in any of the
  // givens:
  var vars = {};
  this._givens.each(function(g) { $.extend(vars, g.freeVars()); });
  this.givenVars = vars;
};

/**
 * Public interface to set the rule and fact offerability mode
 * of this ProofEditor.
 */
ProofEditor.prototype.setRulesMode = function(mode) { var self = this; 
  this.$rulesMode.val(mode);
  if (this.$rulesMode.val() != mode) {
    Toy.err('Bad rules mode setting: ' + mode);
  }
  this.$rulesMode.trigger('change');
};

/**
 * Add a step to the proof.
 */
ProofEditor.prototype.addStep = function(step) { var self = this; 
  self.__mainDisplay.addStep(step);
};

/**
 * Gets the state of the proof, in string form.
 */
ProofEditor.prototype.getStateString = function() { var self = this; 
  return Toy.encodeSteps(self.__mainDisplay.steps)
};

/**
 * Sets the state of the proof from a string as returned by
 * getStateString.
 */
ProofEditor.prototype.setStateFromString = function(encoded) { var self = this; 
  var steps = Toy.decodeSteps(encoded);
  self.__mainDisplay.setSteps(steps);
};

/**
 * Sets the steps to the given array of non-renderable steps.
 */
ProofEditor.prototype.setSteps = function(steps) { var self = this; 
  self.__mainDisplay.setSteps(steps);
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

ProofEditor.prototype.setEditable = function(value) { var self = this; 
  self.__mainDisplay.setEditable(value);
  this.stepEditor.$node.toggle(value);
};

ProofEditor.prototype.showProofButtons = function(value) { var self = this; 
  self.__proofButtons.toggle(value);
};


//// ProofDisplay

// TODO: Extend these to support proof steps that can take more
// than one selection.

// DOM representation notes:
//
// <div class=proofDisplay>
// <div class=stepsParent>  (TODO: remove this obsolete level of DIV)
//   <div class=proofSteps>  (getStepsNode)
//     // Proof steps and possible subproofs between them
//     <div class=proofStep> (getStepNode)
//     // or
//     <div class=inferenceDisplay>

/**
 * Construct a ProofDisplay.
 *
 * Optional single properties argumenent, recognizing:
 * 
 * stepPrefix: to initialize the stepPrefix property.
 * parentStep: parent step, rendered or not.  If given,
 *   this ProofDisplay's steps will be assumed to be the
 *   details for this step.
 * prevStep: If given, this rendered step will be considered
 *   the previous rendered step for all steps within this
 *   ProofDisplay.  Used for display of alternative next steps
 *   in the "rule selector" of the step editor (builder).
 *
 * ProofDisplay object properties:
 *
 * steps: an array of the _rendered_ steps displayed.
 *
 * node: Node containing the entire rendering of the proof.  This has
 * CSS class proofDisplay and the ProofDisplay as the value of its
 * data('proofDisplay').  Only ProofDisplay nodes should have the
 * proofDisplay class.
 *
 * stepsNode: DOM node of the proofSteps DIV.
 *
 * proofEditor: ProofEditor for this (top-level) ProofDisplay,
 *   or null if there is none.
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
 * in its ProofDisplay's steps array, so it must be a property of a
 * _rendered_ step.
 *
 * TODO: Consider supporting a set of renderings per unrendered proof
 * step.
 */
function ProofDisplay(properties) {
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
  this.parentStep = properties.parentStep || null;
  this.prevStep = properties.prevStep || null;

  // ID of element to use for saving/restoring proof state.
  // TODO: Make the textarea part of the ProofDisplay.
  this.textAreaId = 'proofState';

  this.proofEditor = null;

  // Only official "proof nodes" are permitted to have class proofDisplay.
  var $node = $('<div class=proofDisplay>' +
             '<div class=stepsParent><div class=proofSteps></div></div>' +
             '</div>');
  $node.data('proofDisplay', this);
  this.node = dom($node);

  this.stepsNode = dom($node.find('.proofSteps'));

  this._editable = false;
  // Initially selection is not locked out, so selections can be made
  // when this is editable.
  this._selectLock = false;
  this.setEditable(false);
  this.setHoverHighlighting(Toy.highlightAllHovers);
}

/**
 * Notify that the proof has changed.
 */
ProofDisplay.prototype.proofChanged = function() {
  this.proofEditor && this.proofEditor._refresher.activate();
  // This next only needed on account of rules.given as of 02/2017.
  this.proofEditor && this.proofEditor.stepEditor.ruleMenu.refresh();
};

/**
 * Notify that the selection has changed.
 */
ProofDisplay.prototype.selectionChanged = function() {
  this.proofEditor && this.proofEditor.stepEditor.refresh();
};

/**
 * Sets the steps of this proof control to be renderings of the ones
 * in the given array of nonrenderable steps, with
 * stepNumber properties running from 1 to N.
 *
 * TODO: Make a sensible policy for accepting renderable versus
 * nonrenderable steps.
 */
ProofDisplay.prototype.setSteps = function(steps) {
  if (this.steps.length > 0) {
    this.removeStepAndFollowing(this.steps[0]);
  }
  for (var i = 0; i < steps.length; i++) {
    this.addStep(steps[i]);
  }
};

/**
 * Render's the step number into its element of class "stepNumber".
 */
function renderStepNumber(step) {
  $(step.stepNode).find('.stepNumber').html(step.stepNumber);
}

/**
 * Adds a rendering of the given "real" proof step to the end
 * of the control's proof, assigning it the stepNumber for its
 * position.
 */
ProofDisplay.prototype.addStep = function(step) {
  var self = this;
  // TODO: Move most of this logic into renderStep.
  var copy = step.copyToRender();
  copy.users = 0;
  copy.hasLeftElision = false;
  copy.ordinal = step.ordinal;
  step.rendering = copy;
  copy.rendering = copy;
  step.original = step;
  copy.original = step;
  step.ruleDeps.forEach(function(s) {
      if (self == getProofDisplay(s.rendering)) {
        s.rendering.addUser();
      }
    });
  copy.proofDisplay = this;
  this.steps.push(copy);
  // Give it a stepNumber early so rendering code can find it.
  copy.stepNumber = (this.prevStep
                     ? '<span class=stepNumPlaceholder/>'
                     : (Toy.showOrdinals
                        ? step.ordinal
                        : this.stepPrefix + this.steps.length));
  this.renderStep(copy);
  renderStepNumber(copy);
  this.proofChanged();
};

/**
 * Finds a step belonging to this ProofDisplay that depends on the original
 * of the given target step; or null if none found.
 */
ProofDisplay.prototype.findDependent = function(target) {
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
 * deselecting it if selected.
 */
ProofDisplay.prototype.removeLastStep = function() {
  var self = this;
  var steps = self.steps;
  var index = steps.length - 1;
  var step = steps[index];
  if (self.selection === step) {
    self.deselectStep();
  }
  clearSubproof(step);
  // Remove highlighting by pretending the mouse moved out.
  // Deleting the node will not trigger the mouse out event.
  hoverStepSelector(step, 'out');
  $(step.stepNode).remove();
  delete step.original.rendering;
  var display = getProofDisplay(step);
  step.ruleDeps.forEach(function(s) {
      if (getProofDisplay(s.rendering) == display) {
        s.rendering.removeUser();
      }
    });
  steps.length = index;
};

/**
 * Remove from the proof display the given top-level rendered proof
 * step and all other steps of the display that come after it.
 */
ProofDisplay.prototype.removeStepAndFollowing = function(toRemove) {
  var index = this.steps.indexOf(toRemove);
  var steps = this.steps;
  // Remove the last remaining step in each iteration so there is
  // never a step that references a deleted or non-rendered step.
  for (var i = steps.length - 1; i >= index; --i) {
    this.removeLastStep();
  }
  this.proofChanged();
};

/**
 * Remove just the given rendered step from this proof.
 * The step must not have any rendered steps that depend on it.
 */
ProofDisplay.prototype.removeStep = function(step) {
  assert(step.users === 0, 'Cannot remove used step {1}', step);
  // Works by removing from here down, then re-inserting.
  var self = this;
  var index = self.steps.indexOf(step);
  var followers = self.steps.slice(index + 1);
  var top = $(window).scrollTop();
  self.removeStepAndFollowing(step);
  followers.forEach(function(s) { return self.addStep(s.original)});
  $(window).scrollTop(top);
};

/**
 * Turn highlighting of expressions on or off by adding or removing
 * handlers for their events.
 */
ProofDisplay.prototype.setHoverHighlighting = function(state) {
  var action = state ? 'on' : 'off';
  var $node = $(this.node);
  $node[action]('mouseover', exprHandleOver);
  $node[action]('mouseout', exprHandleOut);
  // If not actually handling "hover" events, prevent occurrences here
  // from being handled by an ancestor.
  var ignore = state ? 'off' : 'on';
  $node[ignore]('mouseover', false);
  $node[ignore]('mouseout', false);
};

/**
 * Returns true iff this ProofDisplay is editable.
 */
ProofDisplay.prototype.isEditable = function() {
  return this._editable;
};

/**
 * Makes the control editable or not by showing/hiding the
 * editor button and flagging its state.  Also updates event
 * handling accordingly.  Can turn on hoverHighling, but never
 * turns it off.
 */
ProofDisplay.prototype.setEditable = function(state) {
  this._editable = state;
  if (state) {
    this.setHoverHighlighting(state);
  }
  var nodeQ = $(this.node);
  nodeQ.toggleClass('editable', !!state);
};

/**
 * Turns this control's select lock on or off.  When on, the lock
 * prevents steps and expressions within this control from being
 * selected.  This does not affect highlighting on hover.  This lock
 * may be temporarily set for example when a rule has been chosen
 * based on an existing selection and its form is displayed.
 */
ProofDisplay.prototype.setSelectLock = function(state) {
  this._selectLock = state;
};

/**
 * Result is truthy if selection is currently accepted in this
 * ProofDisplay, specifically when the control is editable and
 * selection is not locked out.  Display of "popup" replacement
 * expressions also keys off of this.
 */
ProofDisplay.prototype.isSelectAllowed = function() {
  return !this._selectLock && this.isEditable();
};


// STEP SELECTION

/**
 * Unconditionally flag the renderable step as selected within this
 * ProofDisplay and in the UI, no other action.
 */
ProofDisplay.prototype.selectStep = function(step) {
  var $node = $(step.stepNode);
  $node.addClass('selected');
  $node.find('.checkbox').prop('checked', true);
  this.selection = step;
  this.selectionChanged();
};

/**
 * Unconditionally deselect any selected step and any selected
 * expression in it, in both the ProofDisplay and the UI.
 */
ProofDisplay.prototype.deselectStep = function() {
  var step = this.selection;
  if (step) {
    var $node = $(step.stepNode);
    $node.removeClass('selected');
    $node.find('.checkbox').prop('checked', false);
    this.selection = null;
    this.deselectExpr(step);
    this.selectionChanged();
  }
};

/**
 * Unconditionally select the expr in this ProofDisplay and in the UI,
 * no other action.
 */
ProofDisplay.prototype.selectExpr = function(expr) {
  var step = getProofStep(expr);
  this.selection = step;
  $(expr.node).addClass('selected');
  step.selection = expr;
  this.selectionChanged();
};

/**
 * Unconditionally deselect any selected expr in the
 * step, no other action.
 */
ProofDisplay.prototype.deselectExpr = function(step) {
  var expr = step.selection;
  if (expr) {
    $(expr.node).removeClass('selected');
    step.selection = null;
    this.selectionChanged();
  }
};

/**
 * Handler for click on a proof step.  Selects the current
 * step, deselecting any other.  Toggles the current one if
 * already selected.
 */
ProofDisplay.prototype.handleStepClick = function(step) {
  if (this.isSelectAllowed()) {
    var selected = this.selection;
    var expr = selected ? selected.selection : null;
    this.deselectStep();
    if (!(step == selected && !expr)) {
      this.selectStep(step);
    }
  }
};

/**
 * Handles selection of an expression in a step.
 * Deselects any other selected expression in the step,
 * toggles the current one if already selected.  Prevents
 * event bubbling up to the step itself.
 */
ProofDisplay.prototype.handleExprClick = function(expr) {
  if (this.isSelectAllowed()) {
    var step = getProofStep(expr);
    var selection = this.selection;
    var oldExpr = selection ? selection.selection : null;
    this.deselectStep();
    if (expr != oldExpr) {
      this.selectExpr(expr);
    }
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
 * - A rendered step has a "proofDisplay" property referring to
 *   the ProofDisplay it belongs to.
 *
 * - When a rendered step has a subproof display open, it has a
 *   "subproofDisplay" property referring to the subproof's
 *   ProofDisplay.
 *
 * - Creation of a rendered step adds a "rendering" property to the
 *   original, so original proof steps can currently have only one
 *   rendering at a time.
 *
 * - The given step's node has CSS class 'proofStep' and a 'proofStep'
 *   data property that refers to the step.  Code elsewhere may assume
 *   that a node renders a proof step iff it has the proofStep CSS
 *   class.
 *
 * - Rendered steps have properties "stepNumber", a string identifying
 *   the step number to display; and "hasLeftElision", a boolean true
 *   to request omitting display of the LHS of an equation.
 */
ProofDisplay.prototype.renderStep = function(step) {
  var self = this;
  // Annotate all rendered steps with type information.
  step.annotateWithTypes();

  // Make an object for rendering of the whole step.
  var $proofStep = $('<div class=proofStep>');
  // This object will have the display of the step, step number, and
  // all of its controls, everything except the step info display with
  // rule name and such.  In some ways it would be nice for this to be
  // a regular DIV with two inline-block children, but the first is
  // itself a flex box with (vertically) centered items, and it does
  // not align vertically with its sibling unless this is also a flex
  // box also with centered children.
  var $step = $('<div class=stepAndControls>');
  $proofStep.append($step);
  // If editable, add deleter.
  if (self.isEditable()) {
    $step.append('<button class=deleteStep title="Delete step">X</button>');
  }
  // If the UI is configured for it, include the node for "?" or circled a.
  if (Toy.showStepHoverMark) {
    // The stepHoverMark is on the left, with an "info" symbol
    // or an "assumed" symbol.
    $step.append($('<span class=stepHoverMark>')
                 // Here we have CSS classes fa and fa-fw with no
                 // character specified.  The character is controlled by
                 // logic.css, not necessarily an fa "icon".
                 .append('<span class="fa fa-fw"></span>',
                         // This is a place to display information (the full step)
                         // when the stepHoverMark is hovered.
                         '<div class=hoverInfoBox></div>'));
  }
  // If editable, add checkbox.
  if (self.isEditable()) {
    $step.append('<input type=checkbox class="stepSelector checkbox">');
  }
  $numArea = ($('<span class="stepNumArea stepSelector">')
              .append('[<span class=stepNumber></span>]'));
  // If the "hover mark" is not configured, put the hoverInfoBox
  // inside the stepNumArea and show it on hover when the shift key is
  // down, see below.
  if (!Toy.showStepHoverMark) {
    $numArea.append('<div class=hoverInfoBox></div>');
  }
  $stepAndNum = ($('<span class=stepAndNum>')
                 .append($numArea));
  $step.append($stepAndNum);
  $proofStep.append('<span class=stepInfo></span>');
  $(self.stepsNode).append($proofStep);
  if (self.isEditable()) {
    $proofStep.addClass('withDeleter');
  }
  $proofStep.data('proofStep', step);
  step.stepNode = dom($proofStep);
  var elide = wantLeftElision(step, self);
  step.hasLeftElision = elide;
  // Remember this value for future use.  Could be computed from
  // previous step if preferred.
  step.asmSteps = Toy.assumptionsBefore(step);
  var $wff = $(renderWff(step));
  hackOnRendering($wff);
  $stepAndNum.append($wff);
  $proofStep.find('.stepInfo').html(formattedStepInfo(step));

  // Annotate subexpressions with popups as appropriate.
  if (this.isEditable()) {
    this.renderPopups(step);
  }

  // Event handling:

  // Expr hovering is already handled by delegation in
  // ProofDisplay.setEditable.
  //
  // TODO: Consider using delegation more extensively.
  var exprSelector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  $proofStep.on(TOUCHDOWN, exprSelector,
           // This implements a policy of one selection per proof step.
           // TODO: Implement such policies in the proof controller.
           function(event) {
             var expr = getExpr(this);
             // Ignore clicks on tooltips, popups and such that may be
             // descendants of the step's node.
             if (expr) {
               self.handleExprClick(expr);
               // Select only the innermost Expr.
               // stopImmediatePropagation does not seem to be required here.
               event.stopPropagation();
             }
           });
  $proofStep.on('mouseenter mouseleave', '.stepSelector', function(event) {
      hoverStepSelector(step, event.type === 'mouseenter' ? 'in' : 'out');
    });
  $proofStep.on('mouseenter', '.stepNumArea', function(event) {
      if (!Toy.showStepHoverMark && event.shiftKey) {
        fillHoverInfoBox(self.proofEditor, step);
      }
    });
  $proofStep.on('mouseleave', '.stepNumArea', function(event) {
      $step.find('.hoverInfoBox').toggle(false);
    });
  $proofStep.on('mouseenter', '.stepHoverMark', function(event) {
      // If the stepHoverMark is not configured "in", this will not
      // happen.
      fillHoverInfoBox(self.proofEditor, step);
    });
  $proofStep.on('mouseleave', '.stepHoverMark', function(event) {
      $step.find('.hoverInfoBox').toggle(false);
    });
  $proofStep.on(TOUCHDOWN, '.stepSelector', function(event) {
    self.handleStepClick(step);
  });

  // Set up "hover" event handling on the stepNode.
  $proofStep.hover(function(event) {
      hoverStep(step, event.type === 'mouseenter' ? 'in' : 'out');
    });

  // Deleter events
  // If there is no deleter, this sets nothing up.
  $proofStep.on('click', '.deleteStep', function(event) {
    if (step.users == 0) {
      // If the step has users the button is effectively disabled.
      self.removeStep(step);
    }
  });

  // Select or deselect the checkbox solely through the step.
  $proofStep.on('click', '.checkbox', function(event) { event.preventDefault(); });

  // Clicking on a ruleName "link" (if any) shows the subproof when subproofs
  // are enabled.
  if (Toy.modes.subproofs) {
    $proofStep.on('click', 'span.ruleName.link', function(event) {
      if (step.subproofDisplay) {
        clearSubproof(step);
      } else {
        renderSubproof(step);
      }
    });
  }
  return dom($step);
};

/**
 * This is a postprocessing hack to simplify the DOM tree for a term
 * after it has been constructed by the normal rendering process.
 * This removes .expr nodes that have no other classes, primarily to
 * make flex layout work better, but it also reduces the (undesired)
 * extra horizontal whitespace embedded in every display.
 *
 * TODO: Make a more permanent fix, one that for example does not
 *   work by postprocessing or result in attachment of abandoned DOM
 *   nodes to parts of rendered steps.
 */
function hackOnRendering($wff) {
  // Find exprs that have no other classes, such as fullExpr.
  var $exprs = $wff.find('[class=expr]');
  // Remove them from the DOM, so flex layout can work better, mainly
  // so binary operators are nested the same as both their left and
  // right operands.
  $exprs.replaceWith(function() { return $(this).contents(); });
  return $wff;
}

/**
 * Renders the expression popups for a steps in a ProofDisplay.  The
 * proof should be editable.
 */
ProofDisplay.prototype.renderPopups = function(step) {
  if (Toy.profileName.match(/^popups/)) {
    console.profile(Toy.profileName);
  }
  var self = this;
  // Include only "forward" distributive facts (ones that distribute
  // "*" across "+").
  var distribKeys = Toy.listFacts(Toy.distribFacts);
  // Also include the very simplest of associative facts.
  var assocKeys = ['a + b + c = a + (b + c)',
                   'a + b - c = a + (b - c)',
                   'a * b * c = a * (b * c)',
                   'a * b / c = a * (b / c)'
                   ];
  var distribStmts = (distribKeys.concat(assocKeys)
                      .map(Toy.getStatement));
  step.traverse(function(term, rpath) {
      if (term.isCall2() && term.node) {
        var rules = Toy.rules;
        // These resulting equations are the result of applying the
        // distributive law and similar ones for subtraction to the
        // term.
        var eqn = rules.consider(term);
        var getPath = Toy.memo(function() { return rpath.reverse()});
        var stmts = distribStmts
          .filter(function(eqn) { return term.matchSchema(eqn.getMain().getLeft())});

        // Build results of relevant distributive law rewriters and
        // actions to run them later.
        function substituter(eqn) {
          // This does the substitution, but leaves the proof (and
          // creation of side conditions) until later.
          var subst = term.matchSchema(eqn.getMain().getLeft());
          return eqn.getMain().getRight().subFree(subst);
        }
        // This is a list of replacement terms, one for each action
        // in actions.
        var results = stmts.map(substituter);
        // Given a statement of a fact, returns a function that will
        // use it in a rewrite when called with no args.
        var actionBuilder =
          function(stmt) { return function() { return Toy.tryRuleAsync(self.proofEditor.stepEditor,
                                     rules.rewrite,
                                     [step.original, getPath(), stmt])}};
        var actions = stmts.map(actionBuilder);

        // Add a result and an action for a local simplifier if one is
        // found.
        var simpler = Toy.applyFactsOnce(eqn, '/main/right',
                                         Toy.basicSimpFacts);
        if (simpler != eqn) {
          var result = rules.simplifySite(simpler, '/main/right');
          results.push(result.getMain().getRight());
          var action =
            function() { return Toy.tryRuleAsync(self.proofEditor.stepEditor,
                               rules.rewrite,
                               [step.original, getPath(), result])};
          actions.push(action);
        }
        if (results.length) {
          var $term = $(term.node);
          results.forEach(function(result, i) {
              var $div = $('<div class=above></div>');
              $div.text(' = ' +
                        result.toHtml()
                        // Strip any outermost parens.
                        .replace(/^\((.*)\)$/, '$1'));
              // The node's data.result will be an equation that can
              // be used to replace the term.
              $div.data('action', actions[i]);
              $term.append($div);
            });
        }
      }
    });

  // Event handling:

  // Notice hovering in events with class "above".
  $(step.stepNode).on('mouseenter mouseleave', '.above',
                      function() { return void $(this).toggleClass('hover')});
  // Handle click events on "above" nodes.  Note that the control
  // must be editable.
  $(step.stepNode).on(TOUCHDOWN, '.above', function(event) {
      // Prevent the containing .expr node from handling this touch,
      // which would select the term.
      event.stopImmediatePropagation();
    });
  $(step.stepNode).on('click', '.above', function(event) {
      // Run the action.
      var action = $(this).data('action');
      action();
    });

  if (Toy.profileName.match(/^popups/)) {
    console.profileEnd();
  }
};

/**
 * Returns the previous rendered step, if any, which is the previous
 * step in the same ProofDisplay, otherwise the previous rendered step
 * of the ProofDisplay's parent step (recursively if needed),
 * otherwise null.
 */
function prevRenderedStep(step) {
  var proofDisplay = getProofDisplay(step);
  if (!proofDisplay) {
    return null;
  }
  if (proofDisplay.prevStep) {
    return proofDisplay.prevStep;
  }
  var index = proofDisplay.steps.indexOf(step);
  if (index > 0) {
    return proofDisplay.steps[index - 1];
  } else {
    var parent = proofDisplay.parentStep;
    if (parent) {
      return prevRenderedStep(parent);
    }
  }
  return null;
}

/**
 * Returns true iff policy is to elide the LHS of the formula of the
 * given rendered step.  Current policy calls for elision if the main
 * parts of the given rendered step and the preceding rendered step
 * are both equations, possibly conditional equations, with the same
 * LHS.
 *
 * TODO: Consider the possibility of showing the whole step in case
 * the _next_ step modifies the LHS of this one, e.g. a rewrite using
 * the LHS.  That would allow the target site to be highlighted.
 */
function wantLeftElision(step) {
  if (step.ruleName == 'display' || step.ruleName == 'asImplication') {
    return false;
  }
  var prev = prevRenderedStep(step);
  return (prev && prev.isEquation() && step.isEquation() &&
          step.getMain().getLeft().matches(prev.getMain().getLeft()));
}


/**
 * Renders the top-level expression of a step into a node, returning
 * the node.  Omits surrounding parens if the step is a Call.
 *
 * TODO: Consider fleshing out the concept of display with fewer
 * parentheses.
 */
function renderWff(step) {
  var info = {asmSteps: []};
  var wff = step.wff;
  var $wff;
  if (step.ruleName == 'asImplication') {
    // Display absolutely everything in this case.
    $wff = wff.render(info, 0);
    wff.node = dom($wff);
    return dom($wff);
  } else if (step.ruleName === 'consider' ||
             step.ruleName === 'considerPart' ||
             step.ruleName === 'given') {
    // Op is always "=" or "==".
    var op = wff.getBinOp().toUnicode();
    var power = Toy.getPrecedence(wff.getBinOp());
    // The right side renders on the left here so any changes to it appear
    // on the right side in following steps.
    //
    // Give the WFF its own node, but it won't be practical to select it
    // because it has no "real estate" of its own.  In practice this just
    // displays its RHS.
    //
    // Note that levels of nesting here are as in " ... == <rhs>"
    // renderings, so the same levels of flexbox nesting works for both.
    wff.node = dom(exprJq().append(wff.getRight().renderTopConj(info, 0)));
    return wff.node;
  } else if (wff.isCall2('=>')) {
    var asmPart = wff.getLeft();
    var mainPart = wff.getRight();
    var mainOnly = allImplicit(asmPart, step);
    var power = mainOnly ? 0 : Toy.getPrecedence(wff.getBinOp());
    // Render the RHS (consequent) as the main.
    mainPart.node = (renderWithElision(mainPart, step) ||
                     dom(mainPart.renderTopConj(info, power)));

    if (mainOnly) {
      // All assumptions are implicit, so the rendering is just the
      // main part.
      return mainPart.node;
    }
    // In this case we want one more level of flexbox to ensure the
    // mainPart is a flexbox.  Specify it with a class.
    if (mainPart.isCall2('==')) {
      $(mainPart.node).addClass('flexBox');
    }
    // There is at least one explicit assumption.
    var explicit = asmPart;
    // Descend into left parts of a chain of assumptions until the
    // right side argument is explicit or only one member left in the
    // chain.  The resulting chain will contain only explicit assumptions.
    while (explicit.isCall2('&') &&
           (explicit.getRight().isTypeCond() ||
            findAsmStep(explicit.getRight(), step.asmSteps))) {
      explicit = explicit.getLeft();
    }
    // When rendering the step as a whole, take the rendering of the
    // explicit part as the rendering for the whole LHS of the
    // conditional.
    asmPart.node = dom(explicit.render(info, power));
    // Now render the entire wff into a node.  The renderer will stop
    // when it reaches the asmPart, because that already has a node.
    $wff = step.wff.render(info, 0);
    // But in the end we want the explicit part to be properly
    // associated with its own display, so fix up the assignments of
    // nodes.
    explicit.node = asmPart.node;
    asmPart.node = null;
    wff.node = dom($wff);
    return wff.node;
  } else {
    // The step is not a conditional.  Render it as the main.
    return wff.node = renderWithElision(wff, step) || dom(wff.renderTopConj(info, 0));
  }
};

/**
 * Renders the given expr of the given step with left elision if the
 * step has left elision, returning the DOM node result, otherwise
 * just returns a falsy value.  The result is a "fullExpr" node with
 * the ellipsis display, the operator, and the RHS of the equality.
 *
 * TODO: Consider changing this and its uses to precompute any special
 * rendering.
 */
function renderWithElision(expr, step) {
  var info = {asmSteps: []};
  if (expr.isCall2('=') && step.hasLeftElision) {
    var $expr = exprJq(true);
    expr.node = dom($expr);
    $expr.append('<span class=ellipsis>&hellip;</span> ',
                 // Display equivalences as equivs.  This eventually
                 // calls toUnicode, and if there is a type, displays
                 // appropriately.
                 expr.getBinOp().render(info, 0, true), ' ',
                 expr.getRight().renderTopConj(info, 0));
    return dom($expr);
  } else {
    return null;
  }
}

Expr.prototype.renderTopConj = function(info, minPower) {
  function annotateTopConj(expr) {
    if (expr.isCall2('&')) {
      expr.getBinOp().breakAfter = true;
      annotateTopConj(expr.getLeft());
    }
  }
  annotateTopConj(this);
  return this.render(info, minPower);
};

/**
 * Returns the first assumption step in the list such that asm matches
 * the assumption, if there is one, else a falsy value.
 */
function findAsmStep(asm, asmSteps) {
  return Toy.each(asmSteps, function(step) {
      // Note that members of asmSteps have the form a => b.
      var lhs = step.wff.getLeft();
      if (lhs.matches(asm)) {
        return step;
      }
    });
}

/**
 * Truthy iff the given term is an assumption that is "in scope"
 * for the step, or is a conjunction of allImplicit terms.
 * (This makes the whole term implicit.)
 */
function allImplicit(expr, step) {
  return (expr.isTypeCond() ||
          findAsmStep(expr, step.asmSteps) ||
          (expr.isCall2('&') &&
           allImplicit(expr.getLeft(), step) && 
           allImplicit(expr.getRight(), step)));
}

/**
 * Build and return a jQuery of class "expr", and mark as "fullExpr"
 * if the optional "full" argument is truthy.
 */
function exprJq(full) {
  var $expr = $('<span class=expr></span>');
  if (full) {
    $expr.addClass('fullExpr');
  }
  return $expr;
}

/**
 * Returns an array CSS class names to add to an Expr node for a
 * variable having the specified name.
 */
function specialClasses(name) {
  if (Toy.isVariableName(name)) {
    return ['italic'];
  }
  switch(name) {
  case 'T':
  case 'F':
    return ['trueFalse'];
  case '&':
    return ['logicAnd'];
  case '|':
    return ['logicOr'];
  case '==':
    return ['equiv'];
  case '*':
    return ['multiply'];
  default:
    return [];
  }
}

/**
 * Create and return a text node containing a space.
 */
function space() {
  return document.createTextNode(' ');
}

function textNode(text) {
  return document.createTextNode(text);
}

// NOTE that some methods on Expr and its subclasses appear here.

// render(info, minPower)
//
// Render this expression into a new DOM node, returning a jQuery
// object for the node.  Sets the expression's "node" property to
// refer to the DOM node created to enclose this expression.  Should
// be done only once to any given expression.
//
// If the expr already has a node, just return a jQuery for the node,
// to enable special rendering of certain exprs beforehand.
//
// The rendering is in the context of the given "info" step
// information, which must have property asmSteps as in a step.
//
// TODO: This property is currently unused because assumptions are
// either rendered normally or not at all.  Consider removing the
// argument.
//
// Omits parentheses around an expression that uses an operator
// if the operator's precedence is at least minPower.
//
// The optional third argument is used only by Atom rendering, and if
// truthy indicates that the expression represents a function (or
// syntactically an operator).
//

Atom.prototype.render = function(info, minPower, isFn) {
  if (this.node) {
    return $(this.node);
  }

  // Note that this does not style any subscript differently than
  // the main part of the variable name.
  var $expr = exprJq(!isFn);
  this.node = dom($expr);
  var aStep = findAsmStep(this, info.asmSteps);
  if (aStep) {
    $expr.addClass('stepRef');
    // Note that this requires the unrendered proof step to be already
    // linked to a rendering with proper stepNumber:
    $expr.append(aStep.rendering.stepNumber);
    return $expr;
  }

  var name = this.toHtml();
  if (!isFn && this.isOperator()) {
    name = '(' + name + ')';
  }
  specialClasses(this.pname).forEach(function(cl) { $expr.addClass(cl); });
  $expr.html(name);
  return $expr;
};

// Private to effectivePower.
var useParens = {
  '|': new Toy.Set().addAll(['&']),
  '=>': new Toy.Set().addAll(['=>', '=']),
  '==': new Toy.Set().addAll(['=>'])
};

/**
 * Computes the effective precedence of the given outer binary
 * operator Atom when the inner expression is one of its operands.
 * The result will be either its normal precedence or one more than
 * the precedence of innerOp if innerOp is listed for the operator in
 * the useParens table.
 *
 * The effect is to force parentheses around the inner expression if
 * it is an of an operand of the outer operator.
 */
function effectivePower(op, inner) {
  if (inner.isCall2()) {
    var innerOp = inner.getBinOp();
    var specialOps = useParens[op.pname];
    if (specialOps && specialOps.has(innerOp.pname)) {
      return Toy.getPrecedence(innerOp) + 1;
    }
  }
  return Toy.getPrecedence(op);
}

// minPower is the precedence required to do without parentheses.
Call.prototype.render = function(info, minPower) {
  if (this.node) {
    return $(this.node);
  }

  var self = this;
  var $expr = exprJq(true);
  this.node = dom($expr);
  // Step number (string) in case rendering is tracking source steps
  // and this term has a sourceStep.
  var stepNum = (Toy.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  if (stepNum) {
    $expr.append('$', stepNum);
  }

  var aStep = findAsmStep(this, info.asmSteps);
  if (aStep) {
    $expr.addClass('stepRef');
    // Note that this requires the unrendered proof step to be already
    // linked to a rendering with proper stepNumber:
    $expr.append(aStep.rendering ? aStep.rendering.stepNumber : '?');
    return $expr;
  }

  // True if reporting the source step, or if the main operator has
  // precedence less than minPower.
  var parens = stepNum;
  if (!parens) {
    var prec = Toy.getPrecedence;
    var myPower = self.isCall1()
      ? prec(self.fn)
      : (self.isCall2() ? prec(self.getBinOp()) : Toy.namePower - 1);
    parens = minPower > myPower;
  }

  if (parens) {
    $expr.append('(');
  }
  if (this.isCall2()) {
    var op = this.getBinOp();
    // In other words, the effective power of this expr's operator, for
    // purposes of deciding whether to parenthesize argument expressions.
    function thisPower(subExpr) {
      return effectivePower(op, subExpr);
    }
    // This is a call on a named function of two arguments.
    if (Toy.isInfixDesired(op)) {
      // Render as infix, e.g. "x + y"
      var left = this.getLeft();
      var right = this.getRight();
      if (op.name in {'*': true, '/': true}) {
        // Render these without extra whitespace.
        var $fn = exprJq().append(left.render(info, thisPower(left)),
                                  op.render(info, 0, true));
        this.fn.node = dom($fn);
        $expr.append($fn, right.render(info, thisPower(right) + 1));
      } else if (op.name == '**' && right.isNumeral()) {
        // Integer exponent: display as superscript without making
        // the exponent selectable by itself.  This makes it practical
        // to select the entire expression.
        var $left = exprJq().append(left.render(info, thisPower(left)));
        $expr.append($left,
                     $('<sup>').append(right.getNumValue()));
      } else {
        // A typical binary operator invocation, e.g. x + y.
        var $fn = exprJq().append(left.render(info, thisPower(left)), ' ',
                                  op.render(info, 0, true));
        this.fn.node = dom($fn);
        var afterOp = op.breakAfter ? '<br>\n' : ' ';
        $expr.append($fn, afterOp, right.render(info, thisPower(right) + 1));
      }
    } else {
      // Anything else render like "f x y".
      // We could render the function part with less parens by
      // reducing the required power by 1 here, but then we might want
      // to reorganize the code for rendering ordinary function calls.
      var $fn = exprJq()
        .append(this.fn.fn.render(info, Toy.namePower + 1, true), ' ',
                this.fn.arg.render(info, Toy.namePower + 1));
      this.fn.node = dom($fn);
      $expr.append($fn, ' ', this.arg.render(info, Toy.namePower + 1));
    }
  } else if (Toy.isInfixDesired(this.fn)) {
    // Infix operator, but only one argument: render like "(+) x"
    // Parenthesize both function and argument if they are calls.
    $expr.append('(', this.fn.render(info, 0), ') ',
                 this.arg.render(info, Toy.namePower + 1));
  } else if (!this.fn.displaysIdentifier()) {
    // Function call with non-identifier operator.
    // Display the function adjacent to its argument, but precede both
    // with a non-breaking space to the left to help the user select
    // this expression, and to set them off from preceding infix operator
    // or other text.  Examples are "forall" and "exists".
    if (this.fn.name === 'neg' && this.arg.isNumeral()) {
      // Render e.g. neg 7 as -(7) to distinguish from a negative
      // number.
      $expr.append(this.fn.render(info, 0, true),
                   '(', this.arg.render(info, Toy.unaryPower), ')');
    } else {
      // Unary operator; ensure space before, then op and arg.
      $expr.append(' ', this.fn.render(info, 0, true),
                   this.arg.render(info, Toy.unaryPower));
    }
  } else {
    // Normal function call: "f x" or " ... x".
    $expr.append(this.fn.render(info, Toy.namePower + 1, true), ' ',
                 this.arg.render(info, Toy.unaryPower));
  }
  if (parens) {
    $expr.append(')');
  }
  return $expr;
};

Lambda.prototype.render = function(info, minPower) {
  if (this.node) {
    return $(this.node);
  }

  var $expr = exprJq(true);
  this.node = dom($expr);
  var stepNum = (Toy.trackSourceSteps
                 && this.sourceStep
                 && this.sourceStep.rendering.stepNumber);
  if (stepNum) {
    $expr.append('$' + stepNum);
  }
  $expr.append('{');
  $expr.append(this.bound.render(info, 0));
  $expr.append('. ');
  var $body = this.body.render(info, 0);
  $expr.append($body);
  $expr.append('}');
  return $expr;
};

/**
 * Copies this step into a renderable proof step, copying its wff
 * deeply.  Does not copy any information related to rendering.
 *
 * TODO: Make this a factory for producing StepDisplay objects.
 */
Step.prototype.copyToRender = function() {
  // Note: does not copy the "ordinal" property, for no
  // great reason.
  var freeVars = this.wff.freeVars();
  var bindings = null;
  for (key in freeVars) {
    bindings = new Bindings(key, key, bindings);
  }
  var wff = this.wff.copyForRendering(bindings);
  // TODO: Make the step be a StepDisplay.
  var step = wff;
  // Flag it as a Step (actually StepDisplay)
  step.wff = wff;
  step.details = this.details;
  step.ruleName = this.ruleName;
  // Some elements of ruleArgs may refer to originals of other steps.
  step.ruleArgs = this.ruleArgs;
  // ruleDeps refers to originals of other steps.
  step.ruleDeps = this.ruleDeps;
  step.hasHyps = this.hasHyps;
  // Assumption steps in scope for this step, including the step
  // itself.  If an assumption step is in scope, the term it
  // introduces can be abbreviated in this step display.
  // Initialized when the step is connected with the proof display.
  step.asmSteps = null;
  // If truthy, this term will render as an ellipsis.
  return step;
};

// In fact, this method is really for StepDisplay objects.
Step.prototype.addUser = function() {
  this.users++;
  $(this.stepNode).addClass('hasUsers');
  // It would be nice to do this, but in Chrome hover events
  // don't work right with this code.
  // $(this.stepNode).find('.deleteStep').prop('disabled', true);
};

Step.prototype.removeUser = function() {
  this.users--;
  if (this.users <= 0) {
    $(this.stepNode).removeClass('hasUsers');
    // It would be nice to do this, but in Chrome hover events
    // don't work right with this code.
    // $(this.stepNode).find('.deleteStep').prop('disabled', false);
  }
};

// copyForRendering()
//
// Makes and returns a deep copy of this Expr, copying all parts
// including occurrences of Vars, so rendering can add distinct
// annotations to each occurrence.  Currently copies only logical
// structure and the sourceStep property (to help rendering of
// hypotheses).  Intended only for use in rendering.
//
//
Atom.prototype.copyForRendering = function(bindings) {
  var name = Toy.getBinding(this.name, bindings) || this.pname;
  var result = new Atom(name);
  result.node = null;
  result.sourceStep = this.sourceStep;
  return result;
};

Call.prototype.copyForRendering = function(bindings) {
  var result = new Call(this.fn.copyForRendering(bindings),
                        this.arg.copyForRendering(bindings));
  result.node = null;
  result.sourceStep = this.sourceStep;
  return result;
};

Lambda.prototype.copyForRendering = function(bindings) {
  var findBinding = Toy.findBinding;
  var bound = this.bound;
  var name = this.bound.name;
  var origName = name;
  if (this.bound.isGeneratedBound()) {
    // When copying a binding of the generatedBound kind, the copy
    // tries to replace it with a variable that has a simpler name
    // different than any name bound in this context (or free in the
    // entire wff).  It retains the base part (with no numeric suffix),
    // trying first just the base, then successive suffixes until finding
    // one with no binding in this scope.
    var base = bound.parseName().name;
    name = base;
    var counter = 0;
    while (true) {
      if (!Toy.findBindingValue(name, bindings)) {
        break;
      }
      counter++;
      name = base + '_' + counter;
    }
  }

  var newBindings = (name == origName
                     ? bindings
                     : new Bindings(origName, name, bindings));
  var result =
    Toy.lambda(Toy.varify(name), this.body.copyForRendering(newBindings));
  result.node = null;
  result.sourceStep = this.sourceStep;
  return result;
};

/**
 * Returns an array of the renderable steps leading up to and
 * including the given step, sorted by ordinal.  The "unrendered"
 * aspect is helpful for rendering subproofs, furthermore currently a
 * step only remembers one rendering, and removal of the rendering
 * from the display deletes the association with the underlying step.
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
 * subproofDisplay property of the step to the ProofDisplay for the
 * subproof.
 */
function renderSubproof(step) {
  var controller = getProofDisplay(step);
  var $node = renderInference(step);
  $(step.stepNode).addClass('hasSubproof');
  step.subproofDisplay = $node.data('proofDisplay');

  // Animate display of the subproof.  While sliding in the display,
  // also smoothly scroll the window to keep the given step at the
  // same place in the window.
  var oldTop = $(window).scrollTop();
  var oldHeight = $(document).height();
  $node.insertBefore(step.stepNode);
  var growth = $(document).height() - oldHeight;
  $node.hide();
  // Do the actual animations after computing the net change
  // in document height.
  $node.show({duration: 200});
  // Really this line animates the window scrollTop, but this
  // is the magic formula that does it across browsers.
  $('html, body').animate({scrollTop: oldTop + growth}, 200);
}

/**
 * Clear any subproof of this step and any subproofs of its steps
 * recursively.  Remove the subproofDisplay property from the step.
 *
 * The second argument is true when no UI action is desired.
 */
function clearSubproof(step, internal) {
  // TODO: Consider ways to clean up this whole function.
  var controller = step.subproofDisplay;
  if (controller) {
    delete step.subproofDisplay;
    controller.steps.forEach(function(step) {
        // Record that the rendering is gone.
        step.original.rendering = null;
        // Clear any rendered subproof for the step.
        // Avoid scrolling any inner subproofs.
        clearSubproof(step, true);
      });
    var container = $(controller.node).closest('.inferenceDisplay');
    if (!internal) {
      // Compute the net change in document height.
      var oldTop = $(window).scrollTop();
      var oldHeight = $(document).height();
      container.toggle(false);
      var growth = $(document).height() - oldHeight;
      container.toggle(true);
      // Do the actual animations, similar to the ones in renderSubproof.
      container.hide(
                     {duration: 200,
                      complete: function() {
                         $(step.stepNode).removeClass('hasSubproof');
                         // Remove after hiding.
                         container.remove();
                       }});
      $('html, body').animate({scrollTop: oldTop + growth}, 200);
    }
  }
}

/**
 * True iff step1 and step2 are rendered adjacent to each other,
 * with step1 first.
 */
function adjacentSteps(step1, step2) {
  step1 = step1.rendering;
  step2 = step2.rendering;
  var controller = getProofDisplay(step1);
  var controller2 = getProofDisplay(step2);
  if (controller2 !== controller) {
    return false;
  }
  var index1 = controller.steps.indexOf(step1);
  var index2 = controller.steps.indexOf(step2);
  return index2 == index1 + 1;
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
  var info = Toy.getRuleInfo(step);
  var description = info.description;
  var useDefault = true;
  if (description[0] === '=') {
    useDefault = false;
    // Expand the description with the named function.
    var fn = stepFormatters[description.slice(1)];
    assert(fn, 'No step formatter "{1}"',  description.slice(1));
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
                  function(markup) { return expandMarkup(step, markup)});
  d2 = d2.replace(/[{].*?[}]/g,
                  function(markup) { return expandMarkup(step, markup)});
  // If a rule has "assert" as its last step, that is its only
  // step, because "assert" has no dependencies.  So we treat the
  // rule as an axiom, regardless of whether it has parameters.
  // Facts may be asserted when used, but proved later on request,
  // TODO: Allow facts to be flagged as axioms so their displays
  //   can be distinguished from other facts, perhaps by simply
  //   omitting the 'proof' property.
  var classes = (step.ruleName == 'fact' ||
                 (step.details &&
                  step.details.ruleName !== 'assert' &&
                  Toy.modes.subproofs)
                 ? 'ruleName link'
                 : 'ruleName');
  // black up-pointing small triangle
  var hider = '<span class=subproofIndicator>\u25b4</span>';
  var $d1 = ($('<span>')
             .prop({className: classes, title: info.tooltip})
             .append(hider, ' ', d1, ' ', hider));
  var stepRefs = useDefault ? defaultStepRefs(step, description) : '';
  return $('<span>').append($d1, d2, stepRefs);
}

/**
 * Computes replacement text for rule description markup.  Occurrences
 * of {step}, {step1}, {step2}, {equation}, {implication}, and
 * {siteStep} expand to the step number of the step argument.
 *
 * Appearances of {term} or {bool} as appropriate display as the term;
 * {var} as the variable name, {site} as the term at the site; {terms}
 * (or {bools}) displays as a comma-separated list of all those
 * inputs.  Unknown markup passes through, e.g. lambdas -- {x. f x}.
 */
function expandMarkup(step, markup) {
  function argStep(place) {
    var arg = step.ruleArgs[place];
    return arg.rendering || arg;
  }
  // Given an array of places, as stored in the value of an "inputs"
  // property of a rule (e.g. rule.inputs.step), and an index into
  // them, returns a step number or phrase ending in a step number,
  // for the nth element.  Also accepts a plain number as if it were a
  // 1-element array.
  function stepNumber(places, index) {
    if (places === undefined) {
      return '?';
    }
    var place = (typeof places === 'number' && index === 0
                 ? places
                 : places[index]);
    if (place) {
      var stepArg = argStep(place - 1);
      if (markupRest && adjacentSteps(stepArg, step)) {
        return '';
      } else {
        return markupRest + '<span class=stepReference>' +
          stepArg.stepNumber + '</span>';
      }
    } else {
      // If the index is out of range return '?'.
      return '?';
    }
  }
  var info = Toy.getRuleInfo(step);
  if (markup.match(/^\{[a-z][_0-9]*[.]/)) {
    // It looks like a lambda, not markup!
    return markup;
  }
  // Does it look like {<word>} or {<text> <word>}, where <text> may
  // contain whitespace?
  var matches = markup.match(/^\{(.*? ?)([a-zA-Z0-9]+)\}$/);
  var markupRest = matches[1];
  var markupName = matches[2];
  switch (markupName) {
  case 'string':
    return Toy.escapeHtml(step.ruleArgs[info.inputs.string - 1]);
  case 'step':
  case 'step1':
    return stepNumber(info.inputs.step, 0);
  case 'step2':
    return stepNumber(info.inputs.step, 1);
  case 'equation':
  case 'equation1':
    return stepNumber(info.inputs.equation, 0);
  case 'equation2':
    return stepNumber(info.inputs.equation, 1);
  case 'implication':
    return stepNumber(info.inputs.implication, 0);
  case 'siteStep':
    return stepNumber(info.inputs.site, 0);
  case 'bool':
  case 'bools':
  case 'term':
  case 'terms':
    var places = info.inputs[markupName.startsWith('bool') ? 'bool' : 'term'];
    if (places == null) {
      return markup;
    }
    // Convert number to array.
    if (typeof places === 'number') {
      places = [places];
    }
    var terms = places.map(function(place) {
        var term = Toy.termify(step.ruleArgs[place - 1]);
        return termDisplay(term);
      });
    return terms.join(', ');
  case 'shortFact':
    var place = info.inputs.bool[0] || info.inputs.bool;
    var bool = Toy.termify(step.ruleArgs[place - 1]);
    if (bool.isCall2('=>')) {
      bool = bool.getRight();
    }
    return termDisplay(bool);
  case 'var':
    var place = info.inputs.varName[0] || info.inputs.varName;
    return Toy.termify(step.ruleArgs[place - 1]).toHtml();
  case 'site':
    var place = info.inputs.site[0] || info.inputs.site;
    var siteStep = argStep(place - 1);
    var term = siteStep.get(step.ruleArgs[place]);
    return term.toHtml();
  default:
    // Pass it through unchanged.
    return markup;
  }
}

/**
 * Returns an HTML display of the given term, as in step descriptions.
 */
function termDisplay(term) {
  var text = term.toHtml();
  return (text[0] === '(') ? text.slice(1, -1) : text;
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
    html += siteRefs.map(function(s) { return s.rendering.stepNumber}).join(', ');
  }
  if (stepRefs.length) {
    html += stepRefs.length > 1 ? ' using steps ' : ' using step ';
    html += stepRefs.map(function(s) { return s.rendering.stepNumber}).join(', ');
  }
  return html;
}


/**
 * Formatting functions for steps.  The function should return
 * an HTML description string.
 */
var stepFormatters = {
  definition: function(step) {
    var result = 'definition of ' + Toy.unicodify(step.ruleArgs[0]);
    if (step.ruleArgs.length == 2) {
      result += ' ' + step.ruleArgs[1];
    }
    return result;
  },
  changeVar: function(step) {
    var step0 = step.ruleArgs[0];
    var path = step.ruleArgs[1];
    var target = step0.get(path);
    return 'rename ' + target.bound;
  },
  simpleApply: function(step) {
    var step0 = step.ruleArgs[0];
    step0 = step0.rendering || step0;
    var path = step.ruleArgs[1];
    var target = step0.get(path);
    assert(target instanceof Toy.Call);
    assert(target.fn instanceof Toy.Lambda);
    return 'apply function of ' + target.fn.bound.toHtml();
  },
  // TODO: Treat "apply" as a rewrite using arbitrary definitions.
  apply: function(step) {
    var step0 = step.ruleArgs[0];
    step0 = step0.rendering || step0;
    var path = step.ruleArgs[1];
    var target = step0.get(path);
    if (target instanceof Toy.Call) {
      var fn = target.fn;
      if (fn instanceof Toy.Lambda) {
        return 'apply function of ' + target.fn.bound.toHtml();
      } else if (target.isCall2()) {
        return 'apply definition of ' + target.getBinOp().toUnicode();
      } else {
        return 'apply definition of ' + fn.toUnicode();
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
    return 'substitute for ' + keys.join(', ') + ';; {in step step}';
  },
  tautInst: function(step) {
    var taut = step.ruleArgs[0];
    if (typeof taut === 'string') {
      taut = Toy.parse(taut);
    }
    return 'instance of tautology ' + taut.toHtml();
  }
};

/**
 * Given a proof step, renders a header and the proof steps
 * of its as-yet-unrendered details within a container DIV with CSS
 * class inferenceDisplay.  Sets the 'proofDisplay' data property of
 * the node to refer to the new ProofDisplay.  If the step is
 * rendered, the details are rendered with step numbers relative to
 * its own step number.
 *
 * Returns the new container jQuery DIV.
 *
 * TODO: Consider starting each subproof with a shallow-copied
 *   step that marks its beginning and links to its original.
 *   The idea is to separate the concept of subproof from
 *   rendering.  Rule wrapper code might do this automatically.
 */
function renderInference(step) {
  var steps = unrenderedDeps(step.details);
  var prefix = '';
  var stepNum = step.stepNumber;
  if (stepNum) {
    // The stepNum could be a nonempty string, or undefined, or a
    // numeric ordinal.  This looks like the only part affected by the
    // step being renderable (or not).
    var match = String(stepNum).match(/(.*?)([0-9]+)$/);
    if (match) {
      prefix = match[1] + (match[2] - 1) + '.';
    }
  }
  var controller =
    new ProofDisplay({stepPrefix: prefix, parentStep: step});
  controller.setSteps(steps);
  var tooltip = Toy.escapeHtml(Toy.getRuleInfo(step).tooltip || '');
  var $subproof = $('<div class=inferenceDisplay></div>');
  if (step.ruleName === 'fact') {
    var $header = $('<div class=proofHeader><b>Proof of <span class=math>'
                    + step.toHtml()
                    + '</span></b><br>'
                    + '<i>' + tooltip + '</i>'
                    + ' <span class=subproofHider>hide &#x25be;</span></div>');
    var $details = null;
  } else {
    var $header = $('<div class=proofHeader>' +
                    '<span class=subproofHider>hide &#x25be;</span>' +
                    ' <span class="techDetailsButton noselect">' +
                    '  more info</span>' +
                    '</div>');
    var $details = $('<div class="techDetails hidden">' +
                     '<b>' + (step.ruleArgs.length ? 'Rule ' : 'Proof of ') +
                     step.ruleName + '</b> ' +
                     computeHeaderArgInfo(step) + '<br>' +
                     '<i>' + tooltip + '</i>' +
                     '</div>');
  }
  $header.find('.subproofHider')
    .on('click', function() { clearSubproof(step); });
  $subproof.append($header);
  if ($details) {
    $subproof.append($details);
    var $button = $header.find('.techDetailsButton');
    $button.on('click', function() {
        $button.text($button.text().trim() == 'more info'
                     ? 'less info'
                     : 'more info');
        $details.toggle(100);
      });
  }
  $subproof.append(controller.node);
  $subproof.data('proofDisplay', controller);
  return $subproof;
}

/**
 * Renders a proof of steps that derive a given step.  Renders the
 * unrendered steps up to and including the given step, appending the
 * display to the given Node.  Returns a new ProofDisplay containing
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
  var controller = new ProofDisplay();
  controller.setSteps(steps);
  var renderTime = Math.ceil(new Date().getTime() - startRender);
  var stats = '';
  if (millis != null) {
    stats = '<span class=ruleStats>Proof '
      + Math.ceil(millis) + ' msec, rendering '
      + renderTime + ' msec, ' + nSteps + ' steps</span>';
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
  function mathSpan(html) {
    return '<span class=math>' + html + '</span>';
  }
  var argInfo = '';
  for (var i = 0; i < step.ruleArgs.length; i++) {
    var arg = step.ruleArgs[i];
    var argText;
    if (arg instanceof Toy.Expr) {
      translated = arg.rendering || arg;
      argText = mathSpan(translated.toHtml());
    } else if (typeof arg == 'string' && arg.match(/^(\(|T$|F$)/)) {
      // Is 'T' or 'F' or '(.*'
      argText = mathSpan(Toy.mathMarkup(arg));
    } else if (typeof arg == 'string' && arg[0] != '/') {
      argText = arg;
    } else if (typeof arg == 'string' || arg instanceof Toy.Path) {
      // Ignore paths and strings that look like paths.
      continue;
    } else {
      // E.g. mappings/objects
      argText = '<code>' + Toy.debugString(arg) + '</code>';
    }
    if (argInfo) {
      argInfo += ', ';
    }
    argInfo += argText;
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
// that references the DOM node that has the display for that
// expression.  From each of these nodes the node for its proof
// step (Inference) is accessible, and from the node for a proof
// step, the inference itself accessible.  From any of these nodes
// the node of the entire proof is accessible, and from it the Proof
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
 * a rendered proof.  Returns null if there is none.
 */
function getProofStep(node) {
  return $(getStepNode(node)).data('proofStep');
}

/**
 * Gets the DOM node of a rendered proof given the node of
 * one of its steps or of an expression in a step.
 */
function getStepsNode(node) {
  return dom($(node).closest('.proofSteps'));
}

/**
 * Get a jQuery for the parent node containing the top-level proof and
 * subproofs where this rendered step can be found.  That parent node
 * is currently not part of a ProofDisplay, but by convention should
 * contain only the top-level proof and its subproofs.
 */
function getTopProofContainer(step) {
  return $(step.stepNode).closest('.proofEditor');
}

/**
 * Gets the ProofDisplay of a rendered term or step, or the node of
 * one.  Returns null if the term or step is not rendered.
 *
 * TODO: Split this into at least two different things when there is
 * an actual Step class.
 */
function getProofDisplay(expr) {
  if (expr instanceof Expr && expr.isProved()) {
    return expr.proofDisplay;
  } else {
    var node = expr instanceof Toy.Expr ? expr.node : expr;
    if (!node) {
      return null;
    }
    var ancestor = $(node).closest('.proofDisplay');
    return ancestor.data('proofDisplay');
  }
}


/**
 * Returns the expression associated with a DOM node, specifically an
 * Expr whose node property is the given node.  Returns a falsy value
 * if there is none.
 */
function getExpr(node) {
  // Go up to the proof step then look through all subexpressions.
  var step = getProofStep(node);
  return (step &&
          step.search(function (expr) { return expr.node == node; },
                      true));
}


//// EVENT HANDLING

/**
 * Handle mouseovers on subexpressions.  The event target can
 * be any part of a proof node.
 */
function exprHandleOver(event) {
  var selector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  var target = event.target;
  var $expr = $(target).closest(selector);
  // Could be no elements in $expr.
  $expr.addClass('hover');
  var proofDisplay = getProofDisplay(target);
  if (proofDisplay && !proofDisplay.selection &&
      proofDisplay.isSelectAllowed()) {
    // Only show these if nothing selected and no form is displayed.
    // Flag as ".popped" the first parent .expr containing an ".above",
    // if any.
    $expr.add($expr.parents('.fullExpr'))
      .filter(function() { return $(this).children('.above').length})
      // Adding the two sets puts the result in document order.
      // Self/nearest parent should then be last.
      .last()
      .toggleClass('popped', true);
  }
  // Show textual path to current expression (if enabled).
  var proofStep = Toy.normalReturn(getProofStep, target);
  if (proofStep) {
    var path = proofStep.pathTo(function(expr) { return expr.node == target});
    hoverShowPath(proofStep, path);
  }
};

/**
 * Handle mouseouts on subexpressions.
 */
function exprHandleOut(event) {
  var selector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  var $expr = $(event.target).closest(selector) || $(event.target);
  $expr.removeClass('hover');
  // Unmark any "popped" ancestor.  See exprHandleOver.
  $expr.add($expr.parents('.fullExpr'))
    .filter(function() { return $(this).children('.above').length})
    .last()
    .toggleClass('popped', false);
  // Clear display of the textual hover path.
  var $display = $('#hoverPath');
  if ($display) {
    // Do nothing if there is no bottom panel.
    $display.html('');
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
 * Defines how to display the hovered path.  Highlighting of the
 * DOM node is handled elsewhere.
 */
function hoverShowPath(wff, path) {
  var $display = $('#hoverPath');
  if ($display.length) {
    // If there is no bottom panel, do nothing.
    var expr = wff.get(path);
    var pathStr = path ? path.toString() : '';
    $display.html(pathStr);
  }
}

/**
 * Event handler for "hover" events on proof steps.
 * Shows decorations such as the deleter.
 */
function hoverStep(step, direction, event) {
  var action = direction == 'in' ? addClass : removeClass;

  // Always add or remove the "hover" class to the step node
  // as the mouse goes in or out.
  action(step.stepNode, 'hover');

  // Highlight steps that establish assumptions used by this one.
  Toy.assumptionsUsed(step.original).forEach(function(assumed) {
      if (assumed.rendering) {
        action(assumed.rendering.stepNode, 'assumed');
      }
    });
}

/**
 * Renders "info" about the given rendered step in response to
 * hovering over a step's .stepHoverMark element.  Now renders the
 * entire step rather than just assumptions.  Also makes the box
 * visible.
 */
function fillHoverInfoBox(proofEditor, step) {
  var $box = $(step.stepNode).find('.hoverInfoBox');
  if ($box.children().length == 0) {
    var info = {asmSteps: []};
    var copy = step.original.copyToRender();
    copy.annotateWithTypes();
    var message = proofEditor ? proofEditor.progressMessage(step) : '';
    var $msgs = $('<div class=pre>').append(message);
    var $step = $('<div class=flex>');
    // TODO: The hack does not really help flex layout here, but with
    //   more work it should be able to help.
    $step.append(hackOnRendering(copy.wff.render(info, 0)));
    $box.append($step, $msgs);
  }
  $box.toggle(true);
}

/**
 * Handles hovering over the stepSelector area of a step by
 * highlighting inputs to the step, references to it, and steps
 * establishing assumptions used by it.
 */
function hoverStepSelector(step, direction, event) {
  var entering = direction === 'in';

  // Highlight or unhighlight the step and step number.
  $(step.stepNode).find('.stepAndNum').toggleClass('hover', entering);

  // When entering a step, highlight all references to it.
  // When leaving remove highlights from all references.
  var container = getTopProofContainer(step);
  container.find('span.stepReference').each(function() {
    if (entering) {
      if (this.innerHTML == step.stepNumber) {
        $(this).addClass('referenced');
      }
    } else {
      $(this).removeClass('referenced');
    }
  });

  // Highlight steps that provide inputs to this one.
  // Use rule-specific hover actions, or default.
  var handler = getHoverHandler(step);
  // TODO: pass a boolean instead of an action.
  var action = entering ? addClass : removeClass;
  if (handler) {
    // If there is a hover handler for this type of inference, apply it.
    handler(step, action);
  } else {
    // If no handler apply or remove default highlighting.
    step.ruleDeps.forEach(function(dep) {
      if (dep.rendering) {
        action(dep.rendering.stepNode, 'dep');
      }
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
  // These are selections in the input step.
  var selections = Toy.stepSites(step);
  // Highlight the input sites expressions for the step while hovered.
  selections.forEach(function(expr) {
    action(expr.node, 'site');
  });

  var deeper = step.wff.isCall2('=>') && step.ruleDeps[0].wff.isCall2('=');
  var right = Toy.path('/right');

  // Show the corresponding subexpressions of this step if possible.
  // Note: this is likely to require overrides in some rules.
  Toy.stepPaths(step).forEach(function(path) {
    try {
      var main = deeper ? step.wff.getRight() : step.wff;
      action(main.get(path).node, 'site');
    } catch(err) {
      console.warn('Cannot hover in step', step.$$);
      console.warn('Hover got error', err.message);
    }
  });
}

/**
 * Hover handler for "r" and "replace".
 */
function hoverReplace(step, action) {
  hoverAsRewriter(step, action);
  var args = step.original.ruleArgs;
  var eqnStep = args[0].rendering;
  action(eqnStep.stepNode, 'dep');
}

// Arguments to the handler functions are an inference
// and the operation is "addClass" or "removeClass".
var hoverHandlers = {
  r: hoverReplace,
  rplace: hoverReplace,
  rRight: hoverReplace,
  replace: hoverAsRewriter,
  replaceEither: function(step, action) {
    // Same as hoverReplace, but the equation is args[2].
    // TODO: Calling hoverAsRewriter does not work when this replaces
    //   a right side.  Fix so it does work.
    hoverAsRewriter(step, action);
    var args = step.original.ruleArgs;
    var eqnStep = args[2].rendering;
    action(eqnStep.stepNode, 'dep');
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
  useDefinition: hoverReplace,
  instEqn: function(step, action) {
    var args = step.original.ruleArgs;
    // Input equation.
    var eqn = args[0].rendering;
    // Name of variable being instantiated.
    var varName = args[2].ruleName;
    action(eqn.stepNode, 'dep');
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
    action(input.stepNode, 'dep');
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
    action(input.stepNode, 'dep');
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

function addBottomPanel($node) {
  $node = $node || $(document.body);
  var style = ('position: fixed; width: 100%; background-color: white; '
               + 'bottom:0px; left: 0em; border-top: 1px solid black');
  var div = $('<div id="bottomPanel" style="' + style + '"></div>');
  div.append('Path: <span id=hoverPath></span>');
  $node.append(div);
}


//// Settable parameters

Toy.showOrdinals = false;


//// Export public names.

Toy.dom = dom;
Toy.eachArgType = eachArgType;
Toy.stepPaths = stepPaths;
Toy.stepSites = stepSites;

Toy.proofToyState = proofToyState;
Toy.ProofEditor = ProofEditor;
Toy.ProofDisplay = ProofDisplay;
Toy.unrenderedDeps = unrenderedDeps;
Toy.renderInference = renderInference;
Toy.renderProof = renderProof;
Toy.addBottomPanel = addBottomPanel;
Toy.getStepNode = getStepNode;
Toy.getProofStep = getProofStep;
Toy.getStepsNode = getStepsNode;
Toy.getExpr = getExpr;

// For debugging
Toy._adjacentSteps = adjacentSteps;
Toy._effectivePower = effectivePower;

// For testing:
Toy._formattedStepInfo = formattedStepInfo;
Toy._specialClasses = specialClasses;

// Global parameter to enable hover highlighting everywhere.
Toy.highlightAllHovers = true;

// Global parameter to suppress displaying hypotheses such as "(R x)".
Toy.suppressRealTypeDisplays = true;

// UI config parameter, see its usage.
Toy.showStepHoverMark = false;

// Detect if the device has a touch screen, e.g. a tablet.
// Mobile jQuery 1.1 does this same test.
Toy.hasTouchEvents = 'ontouchend' in document;

// Control whether to use an Autocompleter vs. plain SELECT element.
// To turn on use of the AutoCompleter, remove "false &".  This
// leaves it off in any case for touch screen systems.
Toy.useAutocompleter = false && !Toy.hasTouchEvents;

// Global parameter to suppress GUI selection of function names
// and the "Curried part" of an infix call.
Toy.simplifiedSelections = true; // Alternatively: Toy.hasTouchEvents;

// Name of event when the user touches the screen or clicks the mouse.
// Note: when using 'mousedown' as the TOUCHDOWN event Chrome has been
// observed to unfocus the keyboard on the subsequent mouseup event,
// an unwanted effect.
var TOUCHDOWN = Toy.hasTouchEvents ? 'touchstart' : 'mousedown';

// Override these properties on the page to get custom modes of
// display and/or operation.
Toy.modes = {
  subproofs: true
};

})();
