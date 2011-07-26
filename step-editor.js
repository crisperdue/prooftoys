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


function StepEditor(controller) {
  // Create a DIV with the step editor content.
  var div = Y.Node.create('<div class=stepEditor></div>');
  div.append('<div style="clear: both"><span style="float: right">'
             + '<input type=button value="Paste" class=sted-paste'
             + ' style="visibility: hidden">'
             + '<input class=sted-remove type=button value="x"></span>'
             + '<span class=sted-label>Wff </span>'
             + '<input class=sted-input maxlength=200></div>');
  var input = div.one('.sted-input');
  // Make the input field into an autocompleter.
  var ac = stepEditorInput(input);
  var remover = div.one('.sted-remove');
  remover.on('click', function() { div.remove(); });

  this.controller = controller;
  this.node = div;
  this.completer = ac;
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
 * Displays the proof step editor at the given index in the proof,
 * setting it as the stepEditor.  If the index is greater than the
 * index of any proof step, appends it at the end.
 */
function showStepEditor(controller, position) {
  var ed = new StepEditor(controller);
  addChild(controller.stepsNode, position, ed.node);
}

/**
 * Make and return an autocompleter using the given input field (node).
 */
function stepEditorInput(input) {
  var hint = 'Axiom, theorem, tautology, or name -- try (';
  function maybeHint() {
    if (input.get('value') == '') {
      input.set('value', hint);
      input.addClass('hinted');
    }
  }
  function unHint() {
    if (input.get('value') == hint) {
      input.set('value', '');
      input.removeClass('hinted');
    }
  }
  maybeHint();
  input.on('blur', maybeHint);
  input.on('focus', unHint);
  var config = {resultFilters: ['startsWith'],
                resultHighlighter: 'startsWith',
                source: Y.theoremNames,
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
  return ac;
}

Y.showStepEditor = showStepEditor;

}, '0.1', {requires: ['array-extras', 'expr', 'autocomplete',
                      'autocomplete-filters', 'autocomplete-highlighters']});
