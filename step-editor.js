// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('step-editor', function(Y) {

//// PROOF STEP EDITOR

// CSS class names beginning with "sted-" are reserved to
// the step editor.  Access to nodes through their class
// should always work in the context of the step editor's node.
// Classes are:
//
// sted-input: The main input field, has auto-completion.
// sted-label: Text label of the main input field.
// sted-paste: Button for pasting the selected part of a WFF.
// sted-hint:  Contains textual hint for use of the input field.
//
// Behavior of the hint message:
// Hint is initially on, but turned off by keyboard focus.
// Resetting the step editor turns it back on, as if the editor
// were brand new.


/**
 * Fields: node, input, completer.
 */
function StepEditor(controller) {
  this._hint = 'Enter WFF, axiom, or theorem by name, or select rule target';
  // Create a DIV with the step editor content.
  var div = Y.Node.create('<div class=stepEditor></div>');
  div.append('<div style="clear: both"><span style="float: right">'
             + '<input type=button value="Paste" class=sted-paste'
             + ' style="visibility: hidden">'
             + '<input class=sted-remove type=button value="x"></span>'
             // TODO: decide whether to have a label here.
             // + '<span class=sted-label>Wff </span>'
             + '<input class=sted-input maxlength=200></div>');
  this.node = div;
  this.input = div.one('.sted-input');
  // Make the input field into an autocompleter.
  var ac = this.stepEditorInput();
  this.completer = ac;
  var remover = div.one('.sted-remove');
  remover.on('click', function() { controller.hideStepEditor(); });
}

/**
 * Puts the step eeditor back in the initial state from the
 * user's point of view.
 */
StepEditor.prototype.reset = function() {
  // Initially the input field displays a hint.
  this.input.set('value', this._hint);
  this.input.addClass('hinted');
}

/**
 * Make and return an autocompleter that uses the input field.
 */
StepEditor.prototype.stepEditorInput = function() {
  var self = this;
  this.reset();
  var input = this.input;
  function focus() {
    if (input.get('value') == self._hint) {
      input.set('value', '');
      input.removeClass('hinted');
    }
    // Cause the autocompleter to query and display the results now.
    ac.sendRequest(input.get('value'));
  }
  input.on('focus', focus);
  var config = {resultFilters: ['startsWith'],
                resultHighlighter: 'startsWith',
                source: Y.theoremNames,
                inputNode: input,
                render: true,
                minQueryLength: 0,
                maxResults: 25
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
  return ac;
};

Y.StepEditor = StepEditor;

}, '0.1', {requires: ['array-extras', 'expr', 'autocomplete',
                      'autocomplete-filters', 'autocomplete-highlighters']});
