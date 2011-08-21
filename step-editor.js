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
 * Fields: node, input, completer, controller.
 */
function StepEditor(controller) {
  this.controller = controller;
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

StepEditor.prototype.filteredRuleNames = function() {
  var controller = this.controller;
  var matches = [];
  var step = controller.selection;
  if (step) {
    var expr = step.selection;
    var bindingPath = expr && step.pathToBinding(function(e) {
        return e == expr;
      });
    var isBinding = !!bindingPath;

    /**
     * This determines what rule(s) are able to match inputs
     * that are selected.  If nothing is selected, only theorems
     * (with no input parameters) match.
     *
     * If something is selected, all rules that can use that input as
     * an argument are considered to match.  Each rule has a
     * descriptor of its arguments associated with its name.  The
     * descriptors are maps from keywords to argument number.
     * The descriptor keyword definitions are:
     *
     * step: Matches any proof step.
     * 
     * equation: Matches a proof step that is an equation.
     *
     * implication: Matches a proof step that is an implication.
     * 
     * term: Matches any term except the binding of a variable.
     * 
     * site: Matches like term, but the rule expects the term's step and
     *   path to the term as inputs.
     *
     * boundVar: Matches a variable binding (e.g. rule "changeVar").
     *
     */
    function matchesSelection(descriptor) {
      var require = descriptor;
      if (expr) {
        // An expression is selected
        if (isBinding) {
          return require.boundVar;
        } else if (require.term || require.site) {
          return true;
        } else {
          return false;
        }
      } else {
        // An entire step is selected.
        if (require.step) {
          return true;
        }
        var isEquation = step.isCall2('=');
        if (isEquation && require.equation) {
          return true;
        } else {
	  var isImplication = step.isCall2('-->');
	  if (isImplication && require.implication) {
	    return true;
	  } else {
            return false;
	  }
        }
      }
    }

    for (var name in Y.rules) {
      var descriptor = Y.rules[name].info.inputs;
      if (descriptor && matchesSelection(descriptor)) {
        matches.push(name);
      }
    }
    return matches;
  } else {
    // Nothing is selected.
    return Y.theoremNames;
  }
};

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
                source: Y.bind(this.filteredRuleNames, this),
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
