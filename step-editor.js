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
 * Fields: node, input, form, completer, controller.
 */
function StepEditor(controller) {
  var self = this;
  this.controller = controller;
  this._hint = 'Enter WFF, axiom, or theorem by name, or select rule target';
  // Create a DIV with the step editor content.
  var div = Y.Node.create('<div class=stepEditor style="clear: both"></div>');
  div.append('<span style="float: right">'
             + '<input type=button value="Paste" class=sted-paste'
             + ' style="visibility: hidden">'
             + '<input class=sted-remove type=button value="x"></span>');
  div.append('<input class=sted-input maxlength=200>'
	     + '<span class=sted-form></span>');
  this.node = div;
  this.input = div.one('.sted-input');
  this.form = div.one('.sted-form');
  // Make the input field into an autocompleter.
  this.completer = this.autoCompleter();
  var inputField = this.input;
  // Selection of anything offered goes through the "selection" path.
  inputField.on('keyup', function(event) {
    if (event.keyCode == 13) {
      var name = inputField.get('value');
      if (!(name in Y.rules)) {
	self.error('No rule ' + name);
      }
    }
  });
  var remover = div.one('.sted-remove');
  remover.on('click', function() { controller.hideStepEditor(); });
}

StepEditor.prototype.error = function(message) {
  // TODO: implement, really, through a message area.
  alert(message);
};

/**
 * Puts the step editor back in the initial state from the
 * user's point of view.
 */
StepEditor.prototype.reset = function() {
  // Initially the input field displays a hint.
  this.input.set('value', this._hint);
  this.input.addClass('hinted');
  this.input.removeClass('hidden');
  this.form.setContent('');
}

/**
 * Handler for autocompleter "selection" event.
 */
StepEditor.prototype.handleSelection = function(event) {
  var name = event.result.text;
  var rule = Y.rules[name];
  if (rule) {
    var template = rule.info.form;
    if (template) {
      // Not an empty string.  (If there is no template, the rule will
      // not be "offerable" and thus not selected.)
      this.input.addClass('hidden');
      this.form.setContent(template);
      return;
    } else {
      this.tryExecuteRule(rule);
    }
  }
};

/**
 * Fill in the arguments for the rule from any selection and content
 * of the form, and execute the rule with the arguments if there is
 * enough suitable information in the form and selection.  Update the
 * proof display with the new step on success.
 *
 * Return true on success, otherwise false.
 */
StepEditor.prototype.tryExecuteRule = function(rule) {
  var inputs = rule.info.inputs;
  var args = [];
  for (var type in inputs) {
    if (type in formTypes) {
      // TODO: Implement getting args from the form.
      return false;
    } else {
      var step = this.controller.selection;
      var expr = step && step.selection;
      if (expr) {
	if (type == 'site' && (typeof inputs.site) == 'number') {
	  // TODO: bindingSite ...
	  args[inputs.site - 1] = step.original;
	  args[inputs.site] = step.pathTo(function(e) { return e == expr; });
	}
      }  // TODO: No selected expression within the step.
    }
  }
  // Check that the args are all filled in.
  for (var i = 0; i < args.length; i++) {
    if (args[i] === undefined) {
      this.error('Undefined argument ' + i);
      return false;
    }
  }
  try {
    var result = rule.apply(null, args);
    this.controller.hideStepEditor();
    this.controller.addStep(result);
    return true;
  } catch(error) {
    this.error(error.message);
    return false;
  }
};

// All types that can be entered in a form.  Omits site and
// bindingSite, which are currently not supported in forms.
var formTypes = {
  term: true,
  funcall: true,
  step: true,
  equation: true,
  implication: true
};

// Datatypes that refer to proof steps.
var stepTypes = {
  step: true,
  equation: true,
  implication: true
};

StepEditor.prototype.filteredRuleNames = function() {
  var controller = this.controller;
  var step = controller.selection;
  var matches = [];
  for (var name in Y.rules) {
    if (this.offerable(name)) {
      matches.push(name);
    }
  }
  return matches;
};

/**
 * Returns true iff the rule name can be offered by autocompletion policy.
 *
 * The given ruleName must be in Y.rules.
 */
StepEditor.prototype.offerable = function(ruleName) {
  var info = Y.rules[ruleName].info;
  if (!('form' in info)) {
    return false;
  }
  var step = this.controller.selection;
  if (step) {
    return matchesSelection(step, ruleName);
  } else {
    var inputs = info.inputs;
    // None of the types in the descriptor are "step" types.
    // The policy is that the user must select something to
    // use rules that take a "step" type input.
    return !Y.Object.some(inputs, function(type) {
      return type in stepTypes;
    });
  }
};

/**
 * This matches a step against the inputs descriptor of an inference
 * rule.  The step is the selected proof step, ruleName is the name of
 * the rule to match against.  Only call this if a step or part of a
 * step is selected.
 *
 * If something is selected, this accepts rules that can use that input
 * as an argument.  Each rule has a descriptor of its arguments
 * associated with its name.  The descriptors are maps from keywords
 * to argument number.  The descriptor keyword definitions are:
 *
 * step: Matches any proof step.
 * 
 * equation: Matches a proof step that is an equation.
 *
 * implication: Matches a proof step that is an implication.
 * 
 * term: Matches any term except the binding of a variable.
 * 
 * funcall: Matches a call to anonymous function (lambda)
 *
 * site: Term in a step; the rule expects the term's step and path
 *   to the term as inputs.
 *
 * bindingSite: Matches a variable binding in a step (as in "changeVar").
 *
 */
function matchesSelection(step, ruleName) {
  var require = Y.rules[ruleName].info.inputs;
  if (!require) {
    // If there is no information about arguments, fail.
    return false;
  }
  // Selected expression (within a step).
  var expr = step.selection;
  if (require.bindingSite) {
    return !!(expr && step.pathToBinding(function(e) {
      return e == expr;
    }));
  } else if (require.site || require.funcall || require.term) {
    return !!expr;
  } else if (require.implication) {
    return step.isCall2('-->');
  } else if (require.equation) {
    return step.isCall2('=');
  } else {
    return require.step;
  }
}

/*
  // Is the selection a binding of a variable?
  var isBinding = !!(expr && step.pathToBinding(function(e) {
    return e == expr;
  }));
  if (expr) {
    // An expression is selected
    if (isBinding) {
      return require.bindingSite;
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
*/

/**
 * Make and return an autocompleter that uses the input field.
 */
StepEditor.prototype.autoCompleter = function() {
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
                maxResults: 25,
		activateFirstItem: true
  };
  var ac = new Y.AutoComplete(config);
  ac.on('select', function(e) {
    self.handleSelection(e);
  });
  return ac;
};

/**
 * True for objects with no enumerable properties.
 */
function empty(object) {
  for (var key in object) {
    return false;
  }
  return true;
}

Y.StepEditor = StepEditor;

}, '0.1', {requires: ['array-extras', 'expr', 'autocomplete',
                      'autocomplete-filters', 'autocomplete-highlighters']});
