// Copyright Crispin Perdue.  All rights reserved.

// This file implements rendering of proofs and proof steps.
// For the deductive system itself see theorems.js.

//// Initialization and utilities


// Set all of this up immediately on load, but avoiding changes
// to the global environment except in namespace "Toy".
(function() {

'use strict';

// Use the application's assert function.
var assert = Toy.assertTrue;

// Misc utility functions are here.
const dom = Toy.dom;

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
 * Setting up a "destroyed" handler on a node will cause the handler
 * to run when the node is removed from the DOM using jQuery's .remove
 * method, as in:
 *
 * $(node).on('destroyed', function() { "do stuff" })
 *
 * This could make it easier to manage information such as
 * associations between proof steps and their renderings.  The handler
 * fires as it is being unbound, so avoid explicitly unbinding.
 */
jQuery.event.special.destroyed = {
  remove: function(o) {
    if (o.handler) {
      o.handler.apply(this, arguments);
    }
  }
}

/**
 * Calls the given function, remembering and restoring the jQuery
 * scrollTop on completion.  Use this to stabilize the scrolling
 * position around code that may make it jump.
 */
function keepScroll(fn) {
  let top = $('html').scrollTop();
  let result = fn();
  $('html').scrollTop(top);
  return result;
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

/**
 * Given a rendered step and rendered term within it, this finds the
 * term's right neighbor term if there is one, or returns null.  The
 * right neighbor of b is c in either (b + c) or ((a + b) + c) where
 * "+" indicates any binary operator(s).
 */
function getRightNeighbor(step, term) {
  var pathToTerm = step.prettyPathTo(term);
  var parentPath = pathToTerm.upTo('/left') || pathToTerm.upTo('/left/right');
  var rightNeighbor = (parentPath
                       ? step.get(parentPath).getRight()
                       : null);
  return rightNeighbor;
}


//// ProofDisplay

// TODO: Extend these to support proof steps that can take more
// than one selection.

// DOM representation notes:
//
// <div class=proofDisplay>
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
 * proofEditor: ProofEditor for this ProofDisplay, or null if there is
 *   none.  Also works if this shows a subproof, as initialized by
 *   subproof rendering (renderInference).
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
  const self = this;
  var controller = this;
  this.steps = [];
  // Set (array) of selected steps.
  // TODO: Implement this.
  this.selections = [];
  // Single selected step when exactly one is selected, or null.
  this.selection = null;
  // If a step is being suggested, the rendered version of the step.
  this.suggesting = null;
  // Prefix string for each step.
  this.stepPrefix = properties.stepPrefix || '';
  this.parentStep = properties.parentStep || null;
  this.prevStep = properties.prevStep || null;
  this.proofEditor = properties.proofEditor || null;

  // Only official "proof nodes" are permitted to have class proofDisplay.
  var $node = $('<div class="proofDisplay logicZone">' +
             '<div class=proofSteps></div>' +
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

  // Saved width of the proofSteps DIV contentRect.
  // Connection to the DOM will trigger resize events.
  // The initial zero value will cause the steps to be
  // reindented as soon as they are connected.
  self.savedWidth = 0;
  Toy.onResize(this.stepsNode, entry => {
    const width = entry.contentRect.width;
    if (width !== self.savedWidth) {
      self.steps.forEach(s => {
        const step = s.rendering;
        step.wff.reIndent();
      });
      self.savedWidth = width;
    }
  });
}

/**
 * Returns the last step of this display, or a null
 * value if the display is empty.
 */
ProofDisplay.prototype.getLastStep = function() {
  var steps = this.steps;
  return steps[steps.length - 1];
}

/**
 * Notify that the proof has changed.
 */
ProofDisplay.prototype.proofChanged = function() {
  if (this.proofEditor) {
    this.proofEditor._refresher.activate();
    // This next only needed on account of rules.given as of 02/2017.
    this.proofEditor.ruleMenu.refresh();
  }
};

/**
 * Notify that the selection has changed.
 */
ProofDisplay.prototype.selectionChanged = function() {
  const editor = this.proofEditor;
  if (editor) {
    editor.ruleMenu.refresh();
  }
};

/**
 * Sets the steps of this proof control to be renderings of the ones
 * in the given array of nonrenderable steps.
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
 * Hides any suggested step, doing necessary bookkeeping.
 */
ProofDisplay.prototype.hideSuggestion = function() {
  var node = this.suggesting;
  if (node) {
    // This does not remove event listeners and data.  To be safe,
    // they will be removed when the RuleMenu is updated.
    $(node).detach();
    this.suggesting = null;
  }
};

/**
 * Renders the given "real" proof step as a suggestion.  Returns a DOM
 * node containing either the rendered step, or HTML with a suitable
 * message.
 */
ProofDisplay.prototype.stepSuggestion = function(step) {
  // Rules that wind up doing nothing generally return one of their
  // inputs, and that input would already be rendered.  This is a
  // quick hack way to detect that.  Suggested steps have a rendering,
  // but it is not attached to the document.
  if (step.rendering && document.contains(step.rendering.stepNode)) {
    return this.suggestionMessage('nothing to do');
  }
  var rendered = step.rendering || this.renderStep(step);
  if (rendered) {
    rendered.stepNumber = '&ndash;';
    renderStepNumber(rendered);
    var node = rendered.stepNode;
    $(node).addClass('stepSuggestion');
    return node;
  }
  return this.suggestionMessage('failed to render step ' +
                                step.toUnicode());
};

/**
 * Returns a DOM node with styling appropriate for a suggestion, given
 * a string or other suitable argument to jQuery.append.
 */
ProofDisplay.prototype.suggestionMessage = function(message) {
  var $div = $('<div class="proofStep stepSuggestion stepMessage">');
  $div.append(message);
  return $div[0];
};

/**
 * Inserts the given DOM node into the spot set aside for suggestions,
 * i.e. after all the display's steps.
 */
ProofDisplay.prototype.suggest = function(node) {
  this.hideSuggestion();
  $(this.stepsNode).closest('.proofDisplay').append(node);
  this.suggesting = node;
};


/**
 * Create and return a renderable step to display the given real step
 * within the given display.
 *
 * This also sets up event handlers for click and hover events within
 * the step.  Does not insert the new node into the document.
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
 * - A rendered step has a set of "users", which are other rendered
 *   steps that depend directly on the step via a single possibly
 *   derived inference step.
 *
 * - When a rendered step has a subproof display open, its
 *   "subproofDisplay" property refers to the subproof's ProofDisplay.
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
  assert(!step.rendering, 'Already rendered', step);
  var copy = step.stepFullCopy();
  copy.users = new Set();
  copy.ordinal = step.ordinal;
  step.rendering = copy;
  copy.rendering = copy;
  step.original = step;
  copy.original = step;
  copy.proofDisplay = this;
  copy.subproofDisplay = null;
  var node = this.renderStep1(copy);
  $(node).addClass('noticeInsert');
  // Reindent when inserted into the DOM:
  node.oninsert = function() {
    copy.wff.reIndent();
  }
  return $(node).data('proofStep');
};

/**
 * Adds a rendering of the given "real" proof step to the end
 * of the control's proof, assigning it the stepNumber for its
 * position.
 *
 * Returns the rendered version, or null if adding to the
 * proof display failed.
 */
ProofDisplay.prototype.addStep = function(step) {
  var self = this;
  var rendered = self.renderStep(step);
  $(self.stepsNode).append(rendered.stepNode);
  this.steps.push(rendered);
  rendered.stepNumber =  (this.prevStep
                          ? '<span class=stepNumPlaceholder/>'
                          : (Toy.showOrdinals
                             ? step.ordinal
                             : this.stepPrefix + this.steps.length));
  renderStepNumber(rendered);
  step.ruleDeps.forEach(function(s) {
    if (self == getProofDisplay(s.rendering)) {
      s.rendering.addUser(rendered);
    }
  });
  this.proofChanged();
  return rendered;
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
 * deselecting it if selected.  Only triggers refreshing of menus if
 * the step was selected.
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
  step.original.rendering = null;
  var display = getProofDisplay(step);
  step.ruleDeps.forEach(function(s) {
      if (getProofDisplay(s.rendering) == display) {
        s.rendering.removeUser(step);
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
  assert(step.users.size === 0, 'Cannot remove used step {1}', step);
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
 * handling accordingly.  Can turn on hoverHighlighting, but never
 * turns it off.
 */
ProofDisplay.prototype.setEditable = function(state) {
  this._editable = state;
  if (state) {
    this.setHoverHighlighting(state);
  }
  $(this.node).toggleClass('editable', !!state);
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
 * Handles selection of an expression in a step.  Deselects any
 * selected expression in the ProofDisplay, and selects the given one
 * unless already selected.
 */
ProofDisplay.prototype.handleExprClick = function(expr) {
  const editor = this.proofEditor;
  if (editor) {
    // TODO: Fix this string to avoid variables with ".".
    editor.$copyText.val(expr.toString());
    editor.$copyText.select();
  }
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
 * Most of the work for renderStep gets done here.  The step
 * must be renderable.
 */
ProofDisplay.prototype.renderStep1 = function(step) {
  var self = this;

  // Make an object for rendering of the whole step.
  var $proofStep = $('<div class=proofStep>');
  // This object will have the display of the step, step number, and
  // all of its controls, everything except the step info display with
  // rule name and such.  In some ways it would be nice for this to be
  // a regular DIV with two inline-block children, but the first is
  // itself a flex box with (vertically) centered items, and it does
  // not align vertically with its sibling unless this is also a flex
  // box also with centered children.
  var $step = $('<span class=stepAndControls>');
  $proofStep.append($step);
  // If editable, add deleter.
  if (self.isEditable()) {
    $step.append('<button class="fa fa-120 fa-times-circle deleteStep"' +
                 ' title="Delete step">');
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
                         '<div class="hoverInfoBox invisible"></div>'));
  }
  // If editable, add checkbox.
  if (self.isEditable()) {
    $step.append('<input type=checkbox class="stepSelector checkbox">');
  }
  const $numArea = ($('<span class="stepNumArea stepSelector">')
                    .append('[<span class=stepNumber></span>]'));
  // If the "hover mark" is not configured, put the hoverInfoBox
  // inside the stepNumArea and show it on hover when the shift key is
  // down, see below.
  if (!Toy.showStepHoverMark) {
    $numArea.append('<div class="hoverInfoBox invisible"></div>');
  }
  // This span is highlighted when the whole step is hovered or selected.
  const $stepAndNum = ($('<span class=stepAndNum>')
                       .append($numArea));
  $step.append($stepAndNum);
  $proofStep.append('<span class=stepInfo></span>');
  if (self.isEditable()) {
    $proofStep.addClass('withDeleter');
  }
  $proofStep.data('proofStep', step);
  step.stepNode = dom($proofStep);
  var elide = wantLeftElision(step, self);
  // This initializes hasLeftElision.
  step.hasLeftElision = elide;
  var $wff = $(renderWff(step));
  hackOnRendering($wff);
  $stepAndNum.append($('<wffblock->').append($wff));
  $proofStep.find('.stepInfo').html(formattedStepInfo(step));

  // Event handling:

  // Expr hovering is already handled by delegation in
  // ProofDisplay.setEditable.
  //
  // TODO: Consider using delegation more extensively.

  const selector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  function handleGeneralClick(event) {
    var $expr = $(event.target).closest(selector) || $(event.target);
    if ($expr.is('.fn') && !event.shiftKey) {
      $expr = $expr.parent().closest(selector);
    }
    var expr = getExpr(dom($expr));
    // Ignore clicks on tooltips, popups and such that may be
    // descendants of the step's node.
    if (expr) {
      self.handleExprClick(expr);
      // Select only the innermost Expr.
      // stopImmediatePropagation does not seem to be required here.
      event.stopPropagation();
    }
  }
  $proofStep.on(TOUCHDOWN, selector, handleGeneralClick);

  $proofStep.on('mouseenter mouseleave', '.stepSelector', function(event) {
      hoverStepSelector(step, event.type === 'mouseenter' ? 'in' : 'out');
    });

  $proofStep.on('mouseenter', '.stepNumArea', function(event) {
      if (!Toy.showStepHoverMark && event.shiftKey) {
        fillHoverInfoBox(self.proofEditor, step);
      }
    });
  $proofStep.on('mouseleave', '.stepNumArea', function(event) {
      $step.find('.hoverInfoBox').toggleClass('invisible', true);
    });
  $proofStep.on('mouseenter', '.ellipsis', function(event) {
      fillHoverInfoBox(self.proofEditor, step);
    });
  $proofStep.on('mouseleave', '.ellipsis', function(event) {
      $step.find('.hoverInfoBox').toggleClass('invisible', true);
    });

  $proofStep.on('mouseenter', '.stepHoverMark', function(event) {
      // If the stepHoverMark is not configured "in", this will not
      // happen.
      fillHoverInfoBox(self.proofEditor, step);
    });
  $proofStep.on('mouseleave', '.stepHoverMark', function(event) {
      $step.find('.hoverInfoBox').toggleClass('invisible', true);
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
    if (step.users.size === 0) {
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
        fillDetails(step);
        // Track these events in Matomo.
        Toy.trackAppEvent('ShowSubproof');
        renderSubproof(step);
      }
    });
  }
  return dom($proofStep);
};

/**
 * Builds and returns a potentially nested array if given a Call,
 * otherwise returns this.
 *
 * Terminology: a term may be "broken before" if a line break and suitable
 * indentation may be inserted before its DOM node.  A term is
 * splittable if breaks are allowed between its parts in case it has
 * parts.  Representation:
 *
 * Atom: the term.
 *
 * Lambda: the term.
 *
 * Call: array of two or more elements for the function and
 * potentially "extended" arguments, in textual order.  Thus an infix
 * function is second in the array rather than first.  Extended
 * arguments come from "uncurrying", and calls to infix functions can
 * also be uncurried, e.g. function composition as infix, applied to
 * some input value.  All of the elements are splittable, and all but
 * the first may be broken before.
 *
 * "Chains" of infix calls to the same operator, or + and - or * and /
 * are flattened to put all arguments and operator terms are at the
 * same level in the tree, reducing nesting of terms to the left.
 *
 * Right operands of infix operators and the argument to an ordinary
 * function may or may not be converted to arrays.
 */
Expr.prototype.formatTerm = function() {
  const power = Toy.getPrecedence;
  const term = this;
  if (term instanceof Call) {
    if (term.isInfixCall()) {
      const op = term.getBinOp();
      const left = term.getLeft();
      const right = term.getRight();
      // const rightTree = right.formatTerm();
      const leftTree = left.formatTerm();
      if (left.isInfixCall()) {
        const leftOp = left.getBinOp();
        if (power(leftOp) === power(op)) {
          return leftTree.concat(op, right);
        } else {
          return [left, op, right];
        }
      } else {
        return [left, op, right];
      }
    } else {
      const fn = term.fn.formatTerm();
      // This concat always appends one element to the array.
      return (fn instanceof Array ? fn : [term.fn])
        .concat([term.arg]);
    }
  } else {
    return term;
  }
};

/**
 * This is for debugging.  It returns a string that indicates the
 * levels of indenting for a term consisting of Calls and Atoms.
 */
Expr.prototype.indentTree = function() {
  const cvt = a => {
    if (a instanceof Call) {
      return cvt(a.formatTerm());
    } else if (a instanceof Array) {
      return '[' + a.map(cvt).join(' ') + ']';
    } else if (a instanceof Atom) {
      return a.toUnicode(true);
    } else {
      return a;
    }
  };
  return cvt(this);
};

/**
 * Redoes the indentation of the given rendered term.
 *
 * Removes any previously-inserted line breaks, then recomputes
 * and inserts line breaks to avoid horizontal overflow if possible.
 * The relevant tree here is based on Expr.formatTerm, which determines
 * depth of nesting of indentation of subterms of this.
 *
 * The first pass inserts breaks before top-level terms of that tree.
 * Then if any top-level terms still overflow it descends into those
 * to reindent them in turn.
 *
 * From outside, call this with no arguments.
 */
Expr.prototype.reIndent = function(depth, portWidth) {
  depth = depth || 1;
  // To log details, remove the "false" in the next line.
  const log = (...args) => false && console.log('>'.repeat(depth), ...args);
  const top = this;
  if (!top.node.offsetParent) {
    log('No offset parent:', top.node, top.node.innerText);
    return;
  }

  const isInfix = term => {
    return term.node && term.node.classList.contains('infix');
  }
  const offset = term => term.node.offsetLeft + term.node.offsetWidth;
  const breakBefore = term => {
    // The "ch" unit approximates the width of an average character.
    // The approximate padding calculation here could be replaced by
    // insertion of invisible text that is the prefix needed before
    // any additional indentation.
    const $span = $('<span class=linebreak>').css({paddingRight: depth + 'ch'});
    $(term.node).before('<br class=linebreak>', $span);
  };
  const pw = portWidth;
  portWidth = portWidth || top.node.offsetParent.clientWidth - 10;

  pw || log('Port:', portWidth);
  log('Indenting', this.$$);
  // Remove all linebreak elements (inserted by breakBefore).
  depth === 1 && $(this.node).find('.linebreak').remove();

  // Get indenting info and apply it to insert linebreaks.
  const a = top.formatTerm();
  if (a instanceof Array) {
    // In other words, "this" is a Call.
    for (let i = 1; i < a.length; i++) {
      const term = a[i];
      if (term.node) {
        const right = offset(term);
        // The term overflows the port width.
        if (right > portWidth && !isInfix(term)) {
          log('Right over:', right);
          // Move the term or preceding infix operator to the left
          // by inserting a linebreak before it.
          const j =
            (i > 0 && a[i - 1] instanceof Expr && isInfix(a[i - 1])
             ? i - 1
             : i);
          if (j > 0) {
            const prev = a[j - 1];
            if (prev &&
                !(prev instanceof Atom && prev.toUnicode().length < 4)) {
              log('Break at:', a[j].$$);
              // Things that overflow their space get moved to the
              // left with a linebreak before them.  This is the first
              // priority for fitting expressions into the horizontal
              // space available.
              breakBefore(a[j]);
            }
          }
        }
      }
    }
    a.forEach((e, i) => {
      if (e.node) {
        const right = offset(e);
        log('e:', right, e.$$);
        if (right > portWidth) {
          log('Right:', right);
          // If a term still overflows, try to re-indent it.
          e.reIndent(depth + 1, portWidth);
        }
      }
    });
  } else if (top instanceof Lambda) {
    top.body.reIndent(depth + 1, portWidth);
  }
};

/**
 * Fills in the details of a renderable step.  A no-op unless the step
 * is a use of rules.fact in which the proof of the fact was deferred,
 * in which case this may set the details of the step and its
 * original.
 */
function fillDetails(step) {
  const original = step.original;
  // This code knows the structure of results produced by
  // asserted facts, either in getResult (when the proof is not
  // invoked), or in asFactProver (when there is no proof).
  //
  // TODO: This will be the place to handle omission of details
  //   in a proof sent back by a worker thread, when the full
  //   proof is overly long.
  if (original.ruleName == 'fact') {
    var details = original.details;
    // Even a fact asserted with its proof deferred may have
    // a step to change the names of free variables.
    // Dig down beyond that step.
    if (details && details.ruleName == 'instMultiVars') {
      details = details.ruleArgs[0];
    }
    if (details.ruleName == 'assert') {
      // The fact was asserted based on its statement, deferring
      // the proof.  Substitute an actual proof, creating it if
      // necessary.  First create a new Step object.
      var copy = (original instanceof Call
                  ? new Call(original.fn, original.arg)
                  : original instanceof Atom
                  ? new Atom(original.pname)
                  // Impossible for a step!
                  : null);
      // Get a real proof.
      var result0 = Toy.proveResult(copy);
      // Convert the variable names in the actual proof to the
      // ones mentioned in the usage of the fact.
      // This map should be OK as it is just a renaming.
      var map = copy.matchSchema(result0);
      // If for some reason there is no mapping, proceed without it,
      // ignoring the issue.
      result0 = map ? Toy.rules.instMultiVars(result0, map) : result0;
      // Caution!! This modifies the details of the input step.
      step.details = original.details = result0;
    }
  }
}

/**
 * This is a postprocessing hack to simplify the DOM tree for a term
 * after it has been constructed by the normal rendering process.
 * This removes .expr nodes that have no other classes,
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
 * Returns the rendered step immediately previous to this one
 * in the same ProofDisplay, otherwise the previous rendered step
 * of the ProofDisplay's parent step (recursively if needed).
 *
 * As a special case, if the proofDisplay has a prevStep property
 * returns that (for dedicated step suggestion ProofDisplays).
 *
 * If the the given rendered step has a ProofDisplay, but is not
 * among its steps, this takes it to immediately follow the last
 * of the displayed steps.
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
  } else if (index == 0) {
    var parent = proofDisplay.parentStep;
    if (parent) {
      return prevRenderedStep(parent);
    }
  } else {
    return proofDisplay.getLastStep();
  }
}

/**
 * Returns boolean value, true iff the given step has a
 * prevRenderedStep with assumptions that are sameAs
 * the assumptions of the given step.
 */
function sameAsPrevAsms(step) {
  if (step.isCall2('=>')) {
    const prev = prevRenderedStep(step);
    return (prev && prev.isCall2('=>') &&
            step.getLeft().sameAs(prev.getLeft()));
  } else {
    return false;
  }
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
  // So-called left elision is currently disabled by the following
  // line of code. Comment it out to get previous behavior:
  return false;
  if (step.ruleName == 'display') {
    return false;
  }
  var prev = prevRenderedStep(step);
  return (prev && prev.isEquation() && step.isEquation() &&
          step.getMain().getLeft().matches(prev.getMain().getLeft()));
}


/**
 * Renders the top-level expression of a renderable step into a node,
 * returning the node.  Omits surrounding parens if the step is a
 * Call, as it usually is.
 *
 * TODO: Consider fleshing out the concept of display with fewer
 * parentheses.
 */
function renderWff(step) {
  var wff = step.wff;
  var $wff;
  if (step.ruleName === 'display' ||
      step.ruleName === 'addTheorem') {
    // Just render everything in a couple of special cases.
    return dom(wff.renderTopConj(0));

  } else if (step.ruleName === 'assume' ||
      step.ruleName === 'consider' ||
      step.ruleName === 'considerPart' ||
      step.ruleName === 'given') {
    // All of these omit some unnecessary part of the display for
    // readability.
    //
    // The right side renders on the left here so any changes to it appear
    // on the right side in following steps.
    //
    // Give the WFF its own node, but it won't be practical to select it
    // because it has no "real estate" of its own.  In practice this just
    // displays its RHS.
    //
    // Note that levels of nesting here are as in " ... == <rhs>"
    // renderings, so the same levels of flexbox nesting works for both.
    wff.node = renderWithElisionSpace(wff);
    return wff.node;
  } else if (wff.isCall2('=>')) {

    // There are assumptions.
    const asmPart = wff.getLeft();
    const mainPart = wff.getRight();

    const power = Toy.getPrecedence(wff.getBinOp());
    // Render the main part.
    const node = (step.hasLeftElision
                  ? renderWithElision(mainPart)
                  : dom(mainPart.renderTopConj(power + 1)));

    // In this case we want one more level of flexbox to ensure the
    // mainPart is a flexbox.  Specify it with a class.
    // TODO: Reconsider this.
    if (mainPart.isCall2('==')) {
      $(mainPart.node).addClass('flexBox');
    }
    if (sameAsPrevAsms(step)) {
      if (step.hasLeftElision) {
        // Don't even render an ellipsis for the assumptions in this case.
        return wff.node = node;
      } else {
        // Render the assumptions as an ellipsis.
        asmPart.node = dom(exprJq()
                           .append('<span class=ellipsis>&hellip;</span>'));
      }
    }
    mainPart.node = node;
    // Now render the entire wff into a node.  The renderer will stop
    // when it reaches the asmPart and when it reaches the mainPart,
    // because they already have nodes.
    $wff = step.wff.render(0);
    wff.node = dom($wff);
    return wff.node;
  } else if (wff.isCall2('==')) {

    // The WFF is a top-level equivalence.
    const left = wff.getLeft();
    const right = wff.getRight();
    const power = Toy.getPrecedence(wff.getBinOp());
    // Render the right part.
    const node = dom(right.renderTopConj(power + 1));

    const prev = prevRenderedStep(step);
    if (prev && prev.isCall2('==') && step.getLeft().sameAs(prev.getLeft())) {
      // Render the LHS as an ellipsis.
      left.node = dom(exprJq()
                      .append('<span class=ellipsis>&hellip;</span>'));
    }
    right.node = node;
    // Now render the entire wff into a node.  The renderer will stop
    // when it reaches the left and right parts, because they already
    // have nodes.
    $wff = step.wff.render(0);
    wff.node = dom($wff);
    return wff.node;
  } else {

    // The step is not a conditional or equivalence.
    return wff.node = (step.hasLeftElision
                       ? renderWithElision(wff)
                       : dom(wff.renderTopConj(0)));
  }
};

/**
 * Renders the given expr of the given step with left elision.  The
 * expr must be a call2, and this will treat the function/operator as
 * infix.  The result is a "fullExpr" node with the ellipsis display,
 * the operator, and the RHS of operator.
 *
 * TODO: Consider changing this and its uses to precompute any special
 * rendering.
 */
function renderWithElision(expr) {
  expr.assertCall2();
  var $expr = exprJq(true);
  expr.node = dom($expr);
  $expr.append('<span class=ellipsis>&hellip;</span> ',
               // Display equivalences as equivs.  This eventually
               // calls toUnicode, and if there is a type, displays
               // appropriately.
               expr.getBinOp().render(0, true), ' ',
               expr.getRight().renderTopConj(0));
  return dom($expr);
}

/**
 * Somewhat like renderWithElision, but with the ellipsis not visible,
 * just occupying space.
 */
function renderWithElisionSpace(expr) {
  expr.assertCall2();
  var $expr = exprJq();
  expr.node = dom($expr);
  const $op = expr.getBinOp().render(0, true);
  $op.addClass('invisible');
  $expr.append($('<span class=ellipsis>')
               .append('<span class=invisible>&hellip;</span>'),
               ' ', expr.getRight().renderTopConj(0));
  return dom($expr);
}

Expr.prototype.renderTopConj = function(minPower) {
  function annotateTopConj(expr) {
    if (expr.isCall2('&')) {
      annotateTopConj(expr.getLeft());
    }
  }
  annotateTopConj(this);
  return this.render(minPower);
};

/**
 * Truthy iff the given term is a conjunction of allImplicit terms.
 * (This makes the whole term implicit.)
 */
function allImplicit(expr, step) {
  return (expr.isTypeCond() ||
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

/**
 * Copies this non-rendered term and renders the result, returning a
 * DOM node containing the rendering.  This is called by the step
 * editor to render terms and their replacements into the menu
 * display.  Often no type information is present, e.g. fact goals.
 * Goals are not deduced, so it is not entirely clear whether pure
 * type inference can be relied on to supply the correct type
 * assignments.
 *
 * TODO: Consider trying to make the rendering of variable names here
 *   consistent with the the names presented in the actual step
 *   renderings.
 */
Expr.prototype.renderTerm = function() {
  const copy = this.copyWithTypes();
  const jq = copy.render(0);
  return jq[0];
};

/**
 * Render this expression into a new DOM node, returning a jQuery
 * object for the node.  Sets the expression's "node" property to
 * refer to the DOM node created to enclose this expression.  Should
 * be done only once to any given expression.
 *
 * If the expr already has a node, just return a jQuery for the node,
 * to enable special rendering of certain exprs beforehand.
 *
 * Omits parentheses around an expression that uses an operator
 * if the operator's precedence is at least minPower.
 *
 * The optional second argument is used only by Atom rendering, and if
 * truthy indicates that this Atom appears in "fn" position in the
 * syntax tree.
 */
Atom.prototype.render = function(minPower, isFn) {
  if (this.node) {
    return $(this.node);
  }

  // Note that this does not style any subscript differently than
  // the main part of the variable name.
  var $expr = exprJq(true);
  this.node = dom($expr);

  // This line says "render without parens if it occurs in function
  // position or is not syntactically an operator".
  var name = this.toHtml(isFn || !this.isOperator());
  specialClasses(this.pname).forEach(function(cl) { $expr.addClass(cl); });
  if (isFn) {
    // ".fn" nodes cause enclosing expression to highlight by default
    // rather than themselves.
    $expr.addClass('fn');
  }
  $expr.html(name);
  return $expr;
};

// Private to effectivePower.
var useParens = {
  '|': new Set(['&']),
  '=>': new Set(['=>', '=']),
  '==': new Set(['=>'])
};

/**
 * Computes the effective precedence of the given outer binary
 * operator Atom when the inner expression is one of its operands.
 * The result will be either its normal precedence or one more than
 * the precedence of innerOp if innerOp is listed for the operator in
 * the useParens table.
 *
 * The effect is to force parentheses around the inner expression if
 * it is an operand of the outer operator.
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
Call.prototype.render = function(minPower) {
  if (this.node) {
    return $(this.node);
  }

  var self = this;
  var $expr = exprJq(true);
  this.node = dom($expr);

  const prec = Toy.getPrecedence;
  const myPower = (self.isCall1()
                   ? prec(self.fn)
                   : self.isCall2()
                   ? prec(self.getBinOp())
                   : Toy.namePower - 1);
  const parens = minPower > myPower;

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
      const $op = op.render(0, true);
      // This next helps UI code find infix operators.
      $op.addClass('infix');
      if (op.name in {'*': true, '/': true}) {
        // Render these without extra whitespace.
        var $fn = exprJq().append(left.render(thisPower(left)), $op);
        this.fn.node = dom($fn);
        $expr.append($fn, right.render(thisPower(right) + 1));
      } else if (op.name == '**' && right.isNumeral()) {
        // Integer exponent: display as superscript without making
        // the exponent selectable by itself.  This makes it practical
        // to select the entire expression.
        var $left = exprJq().append(left.render(thisPower(left)));
        $expr.append($left,
                     $('<sup>').append(right.getNumValue()));
      } else {
        // A typical binary operator invocation, e.g. x + y.
        var $fn = exprJq().append(left.render(thisPower(left)), ' ', $op);
        this.fn.node = dom($fn);
        $expr.append($fn, ' ', right.render(thisPower(right) + 1));
      }
    } else {
      // Anything else render like "f x y".
      // We could render the function part with less parens by
      // reducing the required power by 1 here, but then we might want
      // to reorganize the code for rendering ordinary function calls.
      var $fn = exprJq()
        .append(this.fn.fn.render(Toy.namePower + 1, true), ' ',
                this.fn.arg.render(Toy.namePower + 1));
      this.fn.node = dom($fn);
      $expr.append($fn, ' ', this.arg.render(Toy.namePower + 1));
    }
  } else if (Toy.isInfixDesired(this.fn)) {
    // Infix operator, but only one argument: render like "(+) x"
    // Parenthesize both function and argument if they are calls.
    $expr.append('(', this.fn.render(0), ') ',
                 this.arg.render(Toy.namePower + 1));
  } else if (this instanceof Atom && !this.fn.displaysIdentifier()) {
    // Function call with non-identifier operator, or lambda.
    // Display the function adjacent to its argument, but precede both
    // with a non-breaking space to the left to help the user select
    // this expression, and to set them off from preceding infix operator
    // or other text.  Examples are "forall" and "exists".
    if (this.fn.name === 'neg' && this.arg.isNumeral()) {
      // Render e.g. neg 7 as -(7) to distinguish from a negative
      // number.
      $expr.append(this.fn.render(0, true),
                   '(', this.arg.render(Toy.unaryPower), ')');
    } else {
      // Unary operator; ensure space before, then op and arg.
      $expr.append('&nbsp;', this.fn.render(0, true),
                   this.arg.render(Toy.unaryPower));
    }
  } else {
    // Other function call, e.g. just one or more than 2 args.
    $expr.append(this.fn.render(Toy.namePower, true), ' ',
                 this.arg.render(Toy.unaryPower));
  }
  if (parens) {
    $expr.append(')');
  }
  return $expr;
};

Lambda.prototype.render = function(minPower) {
  if (this.node) {
    return $(this.node);
  }

  var $expr = exprJq(true);
  this.node = dom($expr);
  $expr.append('{');
  $expr.append(this.bound.render(0));
  $expr.append('. ');
  var $body = this.body.render(0);
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
Step.prototype.stepFullCopy = function() {
  // Note: does not copy the "ordinal" property, for no
  // great reason.
  const wff = this.wff.copyWithTypes();
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
  return step;
};

// In fact, this method is really for StepDisplay objects.
Step.prototype.addUser = function(user) {
  this.users.add(user);
  $(this.stepNode).addClass('hasUsers');
  // It would be nice to do this, but in Chrome hover events
  // don't work right with this code.
  // $(this.stepNode).find('.deleteStep').prop('disabled', true);
};

Step.prototype.removeUser = function(user) {
  assert(this.users.has(user), 'Step {1} does not have user {2}', this, user);
  this.users.delete(user);
  if (this.users.size === 0) {
    $(this.stepNode).removeClass('hasUsers');
    // It would be nice to do this, but in Chrome hover events
    // don't work right with this code.
    // $(this.stepNode).find('.deleteStep').prop('disabled', false);
  }
};

/**
 * Returns truthy value iff this Step object is rendered.
 */
Step.prototype.isRendered = function() { return this == this.rendering; };

/**
 * Removes "minor" conditions from the assumptions, returning an Expr.
 * This is specific to real numbers.
 */
Step.prototype.shortForm = function() {
  const infix = Toy.infixCall;
  const asms = this.getAsms();
  let shorts = null;
  if (asms) {
    asms.scanConj(asm => {
      if (asm.likeSubgoal()) {
        shorts = shorts ? infix(shorts, '&', asm) : asm;
      }
    });
    return shorts ? infix(shorts, '=>', this.getRight()) : this.getRight();
  } else {
    return this;
  }
};

/**
 * Given a rendered step, returns it and all rendered steps derived from
 * it, recursively, not including the given step.
 */
Step.prototype.descendants = function() {
  assert(this.isRendered(), 'Not a rendered step: {1}', this);
  const result = new Set();
  function traverse(step) {
    // Dependencies are never circular, so the membership test is
    // optional.
    if (!result.has(step)) {
      result.add(step);
      step.users.forEach(traverse);
    }
  }
  this.users.forEach(traverse);
  return result;
}

// deepCopy()
//
// Makes and returns a deep copy of this Expr, copying all parts
// including occurrences of Vars, so each occurrence can have distinct
// annotations, as needed for rendering and currently used by type
// inference.  Can operate on either renderable or nonrenderable
// terms.  The copy has no type information.
//
Atom.prototype.deepCopy = function() {
  // TODO: Consider whether it is best to use the pname here.
  return new Atom(this.pname);
};

Call.prototype.deepCopy = function() {
  return new Call(this.fn.deepCopy(),
                  this.arg.deepCopy());
};

Lambda.prototype.deepCopy = function() {
  return new Lambda(this.bound.deepCopy(),
                    this.body.deepCopy());
};

/**
 * Returns an array of the plain steps leading up to and including the
 * given step, sorted by ordinal.  The "unrendered" aspect provides
 * support for rules that are "inline", adding zero or more steps to
 * the displayed proof.  It is also helpful for rendering subproofs,
 * furthermore currently a step only remembers one rendering, and
 * removal of the rendering from the display deletes the association
 * with the underlying step.
 *
 * Dependencies are determined by the ruleDeps of steps encountered.
 * If any alleged dependency is not proved, this ignores it.
 */
function unrenderedDeps(step) {
  var result = [];
  const visited = new Set();
  // Traverses the dependency graph, recording a copy of every step
  // and building an array of all of the original steps.
  function visitWithDeps(step) {
    if (!step.isProved()) {
      return;
    }
    if (!step.rendering && !visited.has(step)) {
      result.push(step);
      visited.add(step);
      step.ruleDeps.forEach(function(dep) { visitWithDeps(dep); });
    }
  }
  visitWithDeps(step);
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
  const $subproof = renderInference(step);
  const $step = $(step.stepNode);
  $step.addClass('hasSubproof');
  const editable = $step.is('.proofDisplay.editable .proofStep');
  // If not editable we animate the window scrollTop, but this
  // is the magic formula that does it across browsers.
  const $port = (editable
                 ? $step.closest('.proofDisplay.editable > .proofSteps')
                 : $('html, body'));
  step.subproofDisplay = $subproof.data('proofDisplay');

  const contentHeight =
        () => editable ? $port.prop('scrollHeight') : $(document).height();
  const scrollY =
        () => editable ? $port.scrollTop() : $(window).scrollTop();
  // Animate display of the subproof.  While sliding in the display,
  // also smoothly scroll the window to keep the given step at the
  // same place in the window.
  const oldTop = scrollY();
  const oldHeight = contentHeight();
  $subproof.insertBefore(step.stepNode);
  // reIndent here, synchronously, so the computed new height
  // will be correct.
  $subproof.data('proofDisplay').steps
    .forEach(step => step.rendering.reIndent());
  const growth = contentHeight() - oldHeight;
  // Immediately set the height to zero without changing
  // the width.
  $subproof.slideUp(0);
  // Then animate the insertion.
  $subproof.slideDown({duration: 200});
  // Use jQuery, there is no CSS property for the scrollTop.
  $port.animate({scrollTop: oldTop + growth}, 200);
}

/**
 * Clear any subproof of this step and any subproofs of its steps
 * recursively.  Remove the subproofDisplay property from the step.
 *
 * The second argument is true when no UI action is desired.
 */
function clearSubproof(step, internal) {
  const controller = step.subproofDisplay;
  if (controller) {
    step.subproofDisplay = null;
    const $step = $(step.stepNode);
    const editable = $step.is('.proofDisplay.editable .proofStep');
    const $port = (editable
                   ? $step.closest('.proofDisplay.editable > .proofSteps')
                   : $('html, body'));
    controller.steps.forEach(function(step) {
        // Record that the rendering is gone.
        step.original.rendering = null;
        // Clear any rendered subproof for the step.
        // Avoid scrolling any inner subproofs.
        clearSubproof(step, true);
      });
    const $subproof = $(controller.node).closest('.inferenceDisplay');
    if (!internal) {
      const contentHeight =
            () => (editable
                   ? $port.prop('scrollHeight')
                   : $(document).height());
      const scrollY =
            () => editable ? $port.scrollTop() : $(window).scrollTop();
      // Compute the net change in content/document height.
      const oldTop = scrollY();
      const oldHeight = contentHeight();
      $subproof.slideUp(0);
      const growth = contentHeight() - oldHeight;
      $subproof.slideDown(0);
      // Do the actual animations, similar to the ones in renderSubproof.
      $subproof.slideUp(
                     {duration: 200,
                      complete: function() {
                         $step.removeClass('hasSubproof');
                         // Remove after hiding.
                         $subproof.remove();
                       }});
      $port.animate({scrollTop: oldTop + growth}, 200);
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
 * Returns HTML text describing the renderable step, displayed after
 * the formula on each proof line.  This is an HTML description of a
 * proof step followed by references to other steps this one depends
 * on.  This finds the description in the rule's 'description'
 * property as a template.  Expands paired braces using expandMarkup.
 * Any text after a ";;" pair is formatted as arguments to the rule.
 *
 * Automatically formats site-type dependencies as "in step ... ".
 * If there is no markup that refers to steps, formats other step
 * dependencies as "using step(s) ... ".
 */
function formattedStepInfo(step) {
  var info = Toy.getRuleInfo(step);
  var description = info.description;
  var useDefault = true;
  if (typeof description === 'function') {
    description = description(step);
  }
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
                  // If the details are already rendered, there is no
                  // point in displaying in the link style.
                  !step.details.rendering &&
                  Toy.modes.subproofs)
                 ? 'ruleName link'
                 : 'ruleName');
  // black up-pointing small triangle
  var hider = (classes === 'ruleName'
               ? ''
               : '<span class=subproofIndicator>\u25b4</span>');
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
 * Occurrences of {fact} and {shortFact} expand to the first "bool"
 * input, {shortFact} showing the "shortForm".  In the future these
 * two might show the step number where appropriate.
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
  // for the nth array element -- except if the indicated step is
  // adjacent to the described step, returns an empty string.  Also
  // accepts a plain number as if it were a 1-element array.  If the
  // index is out of range, returns "?".
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
  case 'fact':
  case 'shortFact':
    var place = info.inputs.bool[0] || info.inputs.bool;
    var bool = Toy.mathParse(step.ruleArgs[place - 1]);
    return termDisplay(markupName === 'fact' ? bool : bool.shortForm());
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
  const html = term.toHtml();
  const text = (html[0] === '(') ? html.slice(1, -1) : html;
  return '<span class=term>' + text + '</span>'
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
  renameBound: function(step) {
    var step0 = step.ruleArgs[0];
    var path = step.ruleArgs[1];
    var target = step0.get(path);
    return 'rename ' + target.bound;
  },
  reduce: function(step) {
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
    for (const key in map) {
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
 * Given a rendered proof step, renders a header and the proof steps
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
  const editor = getProofDisplay(step).proofEditor;
  var controller = new ProofDisplay({stepPrefix: prefix,
                                     parentStep: step,
                                     proofEditor: editor});
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
      const translated = arg.rendering || arg;
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
 * within the step or its DOM node.  If no such, returns a nullish.
 */
function getStepNode(expr) {
  const node = expr instanceof Toy.Expr ? expr.node : expr;
  return node.closest('.proofStep');
}

/**
 * Gets the proof step (Expr) of the step that renders
 * in part into the given DOM Node.  Also accepts an Expr of
 * a rendered proof.  Returns null if there is none.
 */
function getProofStep(node) {
  const stepNode = getStepNode(node);
  return stepNode && $(stepNode).data('proofStep');
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
 * Gets the ProofDisplay of a rendered term or either kind of step, or
 * the node of one.  Returns null if the term or step is not rendered.
 *
 * TODO: Split this into at least two different things when there is
 * an actual Step class.
 */
function getProofDisplay(expr) {
  if (expr instanceof Expr && expr.isProved()) {
    return (expr.proofDisplay ||
            (expr.rendering && expr.rendering.proofDisplay));
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
  const selector = Toy.simplifiedSelections ? '.fullExpr' : '.expr';
  const target = event.target;
  const $target = $(target);

  var $expr = $target.closest(selector);
  if ($expr.is('.fn') && !event.shiftKey) {
    // In case the node is for a function name or operator,
    // go up to the node of the enclosing expression.
    $expr = $expr.parent().closest(selector);
  }
  // Then add a hover to the one desired DOM node.
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
  // This appears to depend on mouseout events firing before the
  // related mouseenter event as described at
  // https://www.w3.org/TR/DOM-Level-3-Events/#events-mouseevent-event-order.
  const $target = $(event.target);
  // Remove hovers from all nodes of this proof step.
  $target.closest('.proofStep').find('.expr.hover').removeClass('hover');

  // Unmark any "popped" ancestor.  See exprHandleOver.
  $target.add($target.parents('.fullExpr'))
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
 * handlers.  Currently does nothing if node is null, which can occur
 * when terms are not visible.
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
    var copy = step.original.stepFullCopy();
    var message = proofEditor ? proofEditor.progressMessage(step) : '';
    var $msgs = $('<div class=pre>').append(message);
    var $step = $('<div class=flex>');
    // TODO: The hack does not really help flex layout here, but with
    //   more work it should be able to help.
    $step.append(hackOnRendering(copy.wff.render(0)));
    $box.append($step, $msgs);
  }
  $box.toggleClass('invisible', false);
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

  // TODO: pass a boolean instead of an action.
  const action = entering ? addClass : removeClass;
  // Highlight steps that provide inputs to this one.
  step.ruleDeps.forEach(function(dep) {
      if (dep.rendering) {
        action(dep.rendering.stepNode, 'dep');
      }
    });
  // Rule instantiateVar uses a path to identify a variable.
  if (step.ruleName != 'instantiateVar') {
    // These are selections in the input step.
    const selections = Toy.stepSites(step);
    // Highlight the input sites expressions for the step while hovered.
    selections.forEach(function(expr) {
        action(expr.node, 'site');
      });
  }
  // Also use any rule-specific hover actions.
  var handler = getHoverHandler(step);
  if (handler) {
    // If there is a hover handler for this type of inference, apply it.
    handler(step, action);
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
 * For rewrite rules also highlight the part of the result step
 * that is the replacement.  This assumes that the second ruleDep
 * supplies the equation, which may be implicit in case of
 * rules that replace T with a step or a step's consequent.
 */
function hoverAsRewriter(step, action) {
  // This becomes the first ("target") dep or undefined if nonexistent.
  const target = step.ruleDeps[0];
  if (!target) {
    debugger;
    return;
  }

  const twff = target.wff;
  const targetIsCond = twff.isCall2('=>');
  const stepIsCond = step.isCall2('=>');
  // True iff this step is conditional, but the target was not.
  // The replacement term ends up deeper in the formula.
  const deeper = stepIsCond && !targetIsCond;
  // True iff the target is conditional, but this step is not.
  // The replacement term ends up shallower in the formula.
  const shallower = targetIsCond && !stepIsCond;

  // Show the corresponding subexpressions of this step if possible.
  // Note: this is likely to require overrides in some rules.
  // This is almost always a single path.
  Toy.stepPaths(step).forEach(function(target_path) {
    const tPath = twff.asPath(target_path);
    // This site could use an actual "catch" to suppress errors,
    // but at this time we are preferring to debug any that occur.
    Toy.catchAborts(() => {
      if (tPath.isEnd()) {
        action(step.wff.node, 'site');
      } else if (targetIsCond && tPath.isLeft()) {
        // Without special support we do not have a reasonable
        // way to find the replacement, but can get a good guess
        // when the replacement is (implicitly) T.
        //
        // TODO: Consider recording the replacement term in the
        //   implementation of each rewriting rule, and accessing
        //   it here to highlight it.
        //
        // TODO: Also consider removing newly-introduced T from
        //   conjunctions within the rewriter code, and rendering
        //   the replaced term with a strikeout or similar to
        //   indicate that it is removed.
        const tee = Toy.parse('T');
        const found = step.getLeft()
              .eachConjunct(term => term.sameAs(tee) && term);
        found && action(found.node, 'site');;
        // TODO: We also need to provide some degree of support for
        //   normal equational rewrites applied to assumptions.
      } else {
        const path = shallower ? tPath.rest : tPath;
        const main = deeper ? step.wff.getRight() : step.wff;
        action(main.get(path).node, 'site');
      }
    });
  });
}

/**
 * Hover handler for "r".
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
  rRight: hoverAsRewriter,
  useDefinition: hoverReplace,
  replace: hoverAsRewriter,
  r1: hoverAsRewriter,
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
    const args = step.original.ruleArgs;
    const input = args[0];
    const path = args[1];
    const call = input.rendering.get(path);
    const body = call.fn.body;
    const varName = call.fn.bound.name;
    body.findAll(varName,
                   function(v) { action(v.node, 'occur'); },
                   step.get(path),
                   function(expr) { action(expr.node, 'new'); });
  },
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
  instantiateVar: function(step, action) {
    var args = step.original.ruleArgs;
    // Input step.
    var input = args[0].rendering;
    // Name of variable being instantiated.
    var varName = args[0].get(args[1]).name;
    action(input.stepNode, 'dep');
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
    action(input.stepNode, 'dep');
    input.findAll(varName,
                  function(_var) { action(_var.node, 'occur'); },
                  step,
                  function(expr) { action(expr.node, 'new'); });
  },
  // TODO: instMultiVars
  instForall: function(step, action) {
    const args = step.original.ruleArgs;
    const input = args[0].rendering;
    const path = args[1];
    action(input.stepNode, 'dep');
    const lambda = input.get(path).arg;
    // Name of variable being instantiated.
    const varName = lambda.bound.name;
    const body = lambda.body;
    body.findAll(varName,
                 function(_var) { action(_var.node, 'occur'); },
                 step.get(path),
                 function(expr) { action(expr.node, 'new'); });
  }
};


//// Settable parameters

Toy.showOrdinals = false;


//// Export public names.

Toy.keepScroll = keepScroll;
Toy.eachArgType = eachArgType;
Toy.stepPaths = stepPaths;
Toy.stepSites = stepSites;
Toy.getRightNeighbor = getRightNeighbor;

Toy.ProofDisplay = ProofDisplay;
Toy.unrenderedDeps = unrenderedDeps;
Toy.renderInference = renderInference;
Toy.renderProof = renderProof;
Toy.fillDetails = fillDetails;

Toy.getStepNode = getStepNode;
Toy.getProofStep = getProofStep;
Toy.getStepsNode = getStepsNode;
Toy.getExpr = getExpr;
Toy.getProofDisplay = getProofDisplay;

// For debugging
Toy._adjacentSteps = adjacentSteps;
Toy._effectivePower = effectivePower;

// For testing:
Toy._formattedStepInfo = formattedStepInfo;
Toy._expandMarkup = expandMarkup;
Toy._specialClasses = specialClasses;

// Global parameter to enable hover highlighting everywhere.
Toy.highlightAllHovers = true;

// Global parameter to suppress displaying assumptions such as "(R x)".
// Not yet in use.
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
