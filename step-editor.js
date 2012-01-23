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
//
// Behavior of the hint message:
// Hint is initially on, but turned off by keyboard focus.
// Resetting the step editor turns it back on, as if the editor
// were brand new.

//
// Each rule has a descriptor of its arguments
// associated with its name.  The descriptors are maps from keywords
// to argument number.  The descriptor keyword definitions are:
//
// step: Matches any proof step.
// 
// equation: Matches a proof step that is an equation.
//
// implication: Matches a proof step that is an implication.
// 
// term: Matches any term.
// 
// reducible: Matches a call to anonymous function (lambda)
//
// varName: Name suitable for a variable.
//
// string: Arbitrary nonempty string.
//
// optString: Optional arbitrary string.
//
// site: Term in a step; the rule expects the term's step and path
//   to the term as inputs.
//
// bindingSite: Matches a variable binding in a step (as in "changeVar").
//


// All types that can be entered in a form.  Omits site, bindingSite,
// and reducible, which are currently not supported in forms.
var formTypes = {
  term: true,
  varName: true,
  string: true,
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

// Datatypes that refer to sites within a step.  None of these are
// in formTypes.  Does not include term or varName.
var siteTypes = {
  site: true,
  bindingSite: true,
  reducible: true
};


/**
 * A ProofControl can have only one StepEditor.  It appears at the end
 * of an editable proof.
 *
 * TODO: Support essential step editing such as justification of an assumed
 * step, for steps that already exist.  Also rearranging proofs.
 *
 * Fields: node, input, form, completer,
 * controller.
 */
function StepEditor(controller) {
  var self = this;
  this.controller = controller;
  this._hint = 'Enter axiom or theorem name; for inference select target first';
  // Create a DIV with the step editor content.
  var div = Y.Node.create('<div class=stepEditor style="clear: both"></div>');
  div.append('<input class=sted-input maxlength=200>'
	     + '<span class=sted-form></span>');
  div.append('<input class=sted-clear type=button value=x '
	     + 'title="Clear the input">');
  this.node = div;
  this.input = div.one('.sted-input');
  this.form = div.one('.sted-form');
  // Make the input field into an autocompleter.
  this.completer = this.autoCompleter();
  this.reset();
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
  // Keyup events bubble to here from the inputs in the form.
  this.form.on('keyup', function(event) {
    if (event.keyCode == 13) {
      self.tryExecuteRule(true);
    }
  });
  var clearer = div.one('.sted-clear');
  clearer.on('click', function() { self.reset(); });
}

/**
 * Handle errors in the step editor.  Displays step information in an
 * element named "proofErrors" if there is one.
 */
StepEditor.prototype.error = function(message) {
  if (Y.errors.length) {
    var last = Y.errors[Y.errors.length - 1];
    var proofNode = Y.one('#proofErrors');
    if (proofNode) {
      proofNode.append('<p><b>Errors: (' + Y.errors.length
		       + ') ' + last.message + '</b></p>');
      if (last.step) {
	proofNode.append(Y.renderProof(last.step).node);
      }
    }
  }
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
  // If a form was shown, now show the name input field.
  this.input.removeClass('hidden');
  // Make the user focus again to see the autocompleter.
  this.input.blur();
  this.completer.hide();
  this.form.setContent('');
  this.form.rule = null;
};

/**
 * Handler for autocompleter "selection" event.
 */
StepEditor.prototype.handleSelection = function(event) {
  var name = event.result.text;
  var rule = Y.rules[name];
  if (rule) {
    this.form.rule = rule;
    var template = rule.info.form;
    if (template) {
      // Template is not empty.  (If there is no template, the rule will
      // not be "offerable" and thus not selected.)
      this.input.addClass('hidden');
      this.form.setContent(template);
      addClassInfo(this.form);
      if (!usesSite(rule)) {
	this.addSelectionToForm(rule);
      }
    }
    this.tryExecuteRule(false);
  }
};

/**
 * Computes whether a rule needs a "site" type as an input.
 */
function usesSite(rule) {
  var inputs = rule.info.inputs;
  for (var type in inputs) {
    if (type in siteTypes) {
      return true;
    }
  }
  return false;
}

/**
 * Adds class=step, class=term, etc. to each form element according
 * to its name -- same as the name, but stripping off any numeric suffix,
 * e.g. step2 --> step.
 */
function addClassInfo(form) {
  form.all('input').each(function(node) {
    var name = node.get('name');
    var match = name.match(/^.+?(\d*)$/);
    className = (match && match[1]) || name;
    node.addClass(className);
  });
}

/**
 * Try to fill in a field of the form with the selection.  For
 * steps this will be a reference to the step, and for terms it
 * will be a textual rendering of the selected expression.
 */
StepEditor.prototype.addSelectionToForm = function(rule) {
  var controller = this.controller;
  var step = controller.selection;
  if (step) {
    var expr = step.selection;
    var form = this.form;
    var n = step.stepNumber;
    // Search for the first input field that is compatible with the
    // selection and fill it in with selection information.
    form.all('input').some(function(field) {
      var fieldType = field.get('name').match(/^(.*?)\d*$/)[1];
      if (expr) {
	// TODO: Don't use the selection as a term if it will be used
	// by the rule as a site.
	if (fieldType == 'term') {
	  field.set('value', expr.toString());
	  return true;
	} else {
	  return false;
	}
      } else {
	if (fieldType == 'step'
	    || (fieldType == 'equation' && step.unHyp().isCall2('='))
	    || (fieldType == 'implication' && step.unHyp().isCall2('-->'))) {
	  field.set('value', n);
	  return true;
	} else {
	  return false;
	}
      }
    });
  }
};

/**
 * Fill in the arguments for the rule from any selected site and
 * content of the form, and execute the rule with the arguments if
 * there is enough suitable information in the form and selection.
 * Update the proof display with the new step on success.
 *
 * Return true on success, otherwise false.
 */
StepEditor.prototype.tryExecuteRule = function(reportFailure) {
  var rule = this.form.rule;
  var args = [];
  this.fillWithSelectedSite(args);
  try {
    this.fillFromForm(args);
  } catch(error) {
    // The form is not ready, fail silently.
    if (reportFailure) {
      this.error(error.message);
    }
    return false;
  }
  // Check that the args are all filled in.
  for (var i = 0; i < args.length; i++) {
    if (args[i] === undefined) {
      if (reportFailure) {
	this.error('Undefined argument ' + i);
      }
      return false;
    }
  }
  try {
    var result = rule.apply(null, args);
    this.controller.addStep(result);
    this.reset();
    return true;
  } catch(error) {
    this.error(error.message);
    return false;
  }
};

/**
 * Fill in an argument from the selection if there is a selected
 * expression (not a selected step) and an argument that needs that
 * type.  Reports an error to the user if preconditions are not met.
 */
StepEditor.prototype.fillWithSelectedSite = function(args) {
  var rule = this.form.rule;
  var inputs = rule.info.inputs;
  for (var type in inputs) {
    if (type in siteTypes) {
      var step = this.controller.selection;
      var expr = step && step.selection;
      if (expr) {
	var position = inputs[type];
	if ((typeof position) == 'number') {
	  args[position - 1] = step.original;
	  args[position] = step.pathTo(function(e) { return e == expr; });
	  // Only fill in one argument (pair) from the selection.
	  break;
	} else {
	  // TODO: Someday support multiple sites per rule.
	  this.error('Internal error: only one site supported per rule.');
	}
      } else {
	this.error('Expression not selected');
      }
    }
  }
};

/**
 * Fills in the arguments array with information from the form.
 */
StepEditor.prototype.fillFromForm = function(args) {
  var self = this;
  var rule = this.form.rule;
  this.form.all('input').each(function(node) {
    // The "name" attribute of the input should be the name of an input type,
    // possibly followed by some digits indicating which input.
    var name = node.get('name');
    var match = name.match(/^(.+?)(\d*)$/);
    if (match) {
      var type = match[1];
      // Non-empty when referring to one of multiple args of the
      // same type.  Then the value of the descriptor is a list.
      var which = match[2];
      var inputs = rule.info.inputs;
      var argNum = which ? inputs[type][which - 1] : inputs[type];
      if (!argNum) {
	throw new Error('Internal error: no input descriptor for type ' + type);
      }
      args[argNum - 1] = self.parseValue(node.get('value'), type);
    } else {
      Y.log('Unrecognized input name: ' + name);
    }
  });
};

/**
 * Parses the string value according to its type, which can
 * be any of the formTypes.  Returns an Expr for step or term
 * types.  Throws an Error if it detects the input is not valid.
 */
StepEditor.prototype.parseValue = function(value, type) {
  switch (type) {
  case 'step':
  case 'equation':
  case 'implication':
    if (!value.match(/\d+/)) {
      throw new Error('Not a number: ' + value);
    }
    var index = Number(value) - 1;
    if (index < 0 || index >= this.controller.steps.length) {
      throw new Error('No such step: ' + value);
    }
    return this.controller.steps[Number(value) - 1].original;
  case 'term':
    var tokens = Y.tokenize(value);
    // Throws an error if parsing fails:
    var expr = Y.parse(tokens);
    if (tokens.length) {
      throw new Error('Extra input: "', + tokens[0] + '"');
    }
    return expr;
  case 'varName':
    // Accepts names allowable for user-created variables.
    if (value.match('^[a-zA-Z]+$')) {
      return value;
    } else {
      throw new Error('Illegal variable name: ' + value);
    }
  case 'string':
    if (value.length) {
      return value;
    } else {
      throw new Error('Empty field');
    }
  case 'optString':
    return value;
  default:
    throw new Error('Type not parseable: ' + type);
  }
};

/**
 * Returns a list of names of "offerable" rules, sorted
 * alphabetically.
 */
StepEditor.prototype.filteredRuleNames = function() {
  var controller = this.controller;
  var step = controller.selection;
  var matches = [];
  for (var name in Y.rules) {
    if (this.offerable(name)) {
      matches.push(name);
    }
  }
  matches.sort();
  return matches;
};

/**
 * Returns true iff the rule name can be offered by autocompletion policy.
 * Only rules with a "form" property are offerable at all.  If so --
 *
 * If the proof has a current selection, the rule is offerable if
 * acceptsSelection returns true given the selected step, rule name, and
 * third argument of false.
 *
 * Otherwise only rules that take no step and no site are offerable.
 *
 * This assumes the given ruleName is in Y.rules.
 */
StepEditor.prototype.offerable = function(ruleName) {
  var info = Y.rules[ruleName].info;
  if (!('form' in info)) {
    return false;
  }
  var step = this.controller.selection;
  if (step) {
    // Something is selected.  Check if the rule accepts the
    // selection.
    return acceptsSelection(step, ruleName, false);
  } else {
    // No selection, pass only rules that take no step or site.
    var inputs = info.inputs;
    return !Y.Object.some(inputs, function(value, type) {
      return type in stepTypes || type in siteTypes;
    });
  }
};

/**
 * This matches a step against the inputs descriptor of an inference
 * rule.  The step is the selected proof step, ruleName is the name of
 * the rule to match against.  Only call this if a step or part of a
 * step is selected.  The boolean argument determines whether a term
 * should be considered acceptable or not.
 *
 * If something is selected, this accepts rules that can use that input
 * as an argument.
 */
function acceptsSelection(step, ruleName, acceptTerm) {
  var accept = Y.rules[ruleName].info.inputs;
  if (!accept) {
    // If there is no information about arguments, fail.
    return false;
  }
  // Selected expression (within a step).
  var expr = step.selection;
  if (expr) {
    return (accept.site
	    || (acceptTerm && accept.term)
	    || (accept.bindingSite && step.pathToBinding(function(e) {
	      return e == expr;
	    }))
	    || (accept.reducible
		&& expr instanceof Y.Call
		&& expr.fn instanceof Y.Lambda));
  } else {
    return (accept.step
	    || (accept.equation && step.unHyp().isCall2('='))
	    || (accept.implication && step.unHyp().isCall2('-->')));
  }
}

/**
 * Make and return an autocompleter that uses the input field.
 */
StepEditor.prototype.autoCompleter = function() {
  var self = this;
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
  // TODO: Replace this hack with something more principled.
  // This helps make sure that the autocompleter list disappears when
  // the input field is no longer focused.
  input.on('blur', function() {
    Y.later(1000, null, function() { ac.hide(); });
  });
  var config = {resultFilters: ['startsWith'],
                resultHighlighter: 'startsWith',
		resultFormatter: resultFormatter,
                source: Y.bind(this.filteredRuleNames, this),
                inputNode: input,
                render: true,
                minQueryLength: 0,
                maxResults: 25,
		activateFirstItem: true
  };
  var ac = new Y.AutoComplete(config);
  // Do this after the event so actions such as updating the input
  // field override the default action.
  ac.after('select', function(e) {
    self.handleSelection(e);
  });
  return ac;
};

/**
 * Used by the autocompleter to convert highlighted results into
 * fully-formatted results with hints.  Accepts a query and result list,
 * return a list of HTML-formatted results.
 */
function resultFormatter(query, results) {
  return Y.Array.map(results, function (result) {
    var ruleName = result.text;
    var info = Y.rules[ruleName].info;
    var hint = info.hint || info.comment || '';
    return result.highlighted + '<i style="color: gray"> - ' + hint + '</i>';
  });	
}

Y.StepEditor = StepEditor;

}, '0.1', {requires: ['array-extras', 'expr', 'autocomplete',
                      'autocomplete-filters', 'autocomplete-highlighters']});
