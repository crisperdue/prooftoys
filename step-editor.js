// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('step-editor', function(Y) {

// Make application assertions available through "assert".
var assert = Y.assertTrue;

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

/**
 * Applies the action to each integer index and "form type" of each of
 * the arguments described by a rules "inputs" descriptor.  Indexes
 * passed to the action are zero-based, not 1-based as in the
 * descriptors.  Currently does not include indexes of paths not
 * explicitly described.
 */
function eachArgType(ruleName, action) {
  var inputs = Y.rules[ruleName].info.inputs;
  Y.each(inputs, function(where, type) {
    if (typeof where == 'number') {
      action(where - 1, type);
    } else {
      Y.each(where, function(position) {
        action(position - 1, type);
      });
    }
  });
}

// All types that can be entered in a form.  Omits site, bindingSite,
// and reducible, which are currently not supported in forms.
var formTypes = {
  term: true,
  varName: true,
  string: true,
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
// in formTypes.
var siteTypes = {
  site: true,
  bindingSite: true,
  reducible: true
};

/**
 * Given a step, rendered or not, uses its rule information to return
 * a list of paths used in it to refer to subexpressions of inputs.
 */
function stepPaths(step) {
  assert(step.isStep(), 'Not a step: ' + step);
  var results = [];
  var args = step.ruleArgs;
  eachArgType(step.ruleName, function(position, type) {
      if (siteTypes.hasOwnProperty(type)) {
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
    if (siteTypes.hasOwnProperty(type)) {
      var source = step.ruleArgs[position];
      if (source.rendering) {
        results.push(source.rendering.locate(step.ruleArgs[position + 1]));
      }
    }
  });
  return results;
}

/**
 * A ProofControl can have only one StepEditor.  It appears at the end
 * of an editable proof.
 *
 * TODO: Support essential step editing such as justification of an assumed
 * step, for steps that already exist.  Also rearranging proofs.
 *
 * Fields:
 * node: DIV with the step editor's HTML.
 * form: SPAN to hold the argument input form.
 * ruleSelector: rule selector control.
 * controller: ProofControl.
 */
function StepEditor(controller) {
  var self = this;
  this.controller = controller;

  // Create a DIV with the step editor content.
  var div = Y.Node.create('<div class=stepEditor style="clear: both"></div>');
  var selector = Y.Node.create('<span></span>');
  div.append(selector);
  this.form = Y.Node.create('<span class=sted-form></span>');
  div.append(this.form);
  var clearer = Y.Node.create('<input class=sted-clear type=button value=x '
	                      + 'title="Clear the input">');
  div.append(clearer);
  var sr = ('<input class=sted-save-restore type=button '
            + 'value="Save/restore ..." '
            + 'title="Save or restore proof state">');
  this.saveRestore = Y.Node.create(sr);
  div.append(this.saveRestore);
  this.node = div;

  // Install a rule selector
  if (Y.useAutocompleter) {
    var hint =
      'Enter axiom or theorem name; for inference select target first';
    var html = '<input class=sted-input maxlength=200 title="' + hint + '">';
    var input = Y.Node.create(html);
    selector.append(input);
    this.ruleSelector =
      new RuleSelector(input,
                       Y.bind('filteredRuleNames', this),
                       Y.bind('handleSelection', this));
  } else {
    var widget = new BasicRuleSelector(Y.bind('filteredRuleNames', this),
                                       Y.bind('handleSelection', this));
    this.ruleSelector = widget;
    selector.append(widget.node);
  }
  
  // Install event handlers.
  clearer.on('click', function() { self.reset(); });
  // Keyboard events bubble to here from the inputs in the form.
  // Use "keydown" because "keyup" would catch the "up" event from
  // the Enter key in the autocompleter field.
  this.form.on('keydown', function(event) {
    if (event.keyCode == 13) {
      self.tryExecuteRule(true);
    }
  });
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
 * Puts the step editor back in the initial state from the user's
 * point of view: visible with empty input, no rule-specific form.
 */
StepEditor.prototype.reset = function() {
  this.ruleSelector.reset();
  this.ruleSelector.node.removeClass('hidden');
  this.form.setContent('');
};

/**
 * Attempt to take keyboard focus.
 */
StepEditor.prototype.focus = function() {
  this.ruleSelector.focus();
};

/**
 * Handler for ruleSelector selection of a rule name.
 */
StepEditor.prototype.handleSelection = function() {
  var rule = Y.rules[this.ruleSelector.ruleName];
  if (rule) {
    var template = rule.info.form;
    if (template) {
      // Template is not empty.  (If there is no template at all, the
      // rule will not be "offerable" and thus not selected.)
      this.ruleSelector.node.addClass('hidden');
      this.form.setContent(template);
      addClassInfo(this.form);
      if (!usesSite(rule)) {
	this.addSelectionToForm(rule);
      }
      // Focus the first INPUT element of the form.
      var input = this.form.one('input');
      input.focus();
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
 * e.g. step2 ==> step.
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
 *
 * TODO: Modify spec and implementation to just add step references
 * but not selected expressions to the form.  Selected expressions are
 * sites, which do not appear in forms.
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
	    || (fieldType == 'implication' && step.unHyp().isCall2('==>'))) {
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
  // TODO: Get it together on failure reporting here.
  var rule = Y.rules[this.ruleSelector.ruleName];
  var args = [];
  this.fillWithSelectedSite(args);
  try {
    this.fillFromForm(args);
  } catch(error) {
    // The form is not ready, fail.
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
  var value = false;
  try {
    if (Y.profileName) {
      // Collect CPU profiling information.
      console.profile(Y.profileName);
    }
    var result = rule.apply(null, args);
    this.controller.addStep(result);
    this.controller.deselectStep();
    this.controller.proofChanged();
    this.reset();
    this.focus();
    value = true;
  } catch(error) {
    this.error(error.message);
  }
  if (Y.profileName) {
    console.profileEnd();
  }
  return value;
};

/**
 * Fill in an argument from the selection if there is a selected
 * expression (not a selected step) and an argument that needs that
 * type.  Reports an error to the user if preconditions are not met.
 */
StepEditor.prototype.fillWithSelectedSite = function(args) {
  var rule = Y.rules[this.ruleSelector.ruleName];
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
  var rule = Y.rules[this.ruleSelector.ruleName];
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
    var binOps = {'+': true, '-': true, '*': true, '/': true};
    // TODO: Change all infix parsing so the following hack
    //   becomes superfluous.
    // The following is just a hack so you can type "- 3" as
    // input to e.g. rules.applyToBoth with the usual meaning.
    if (expr.isCall1() && expr.fn.name in binOps) {
      expr = lambda(x, Y.infixCall(x, expr.fn, expr.arg));
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
 * alphabetically, but with axiom names changed to start instead with
 * "x", i.e. "xiom".
 */
StepEditor.prototype.filteredRuleNames = function() {
  var controller = this.controller;
  var step = controller.selection;
  var matches = [];
  for (var name in Y.rules) {
    display = name.replace(/^axiom/, 'xiom');
    if (this.offerable(name)) {
      matches.push(display);
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
  var info = Y.rules[ruleName].info;
  var accept = info.inputs;
  if (!accept) {
    // If there is no information about arguments, fail.
    return false;
  }
  // Selected expression (within a step).
  var expr = step.selection;
  if (expr) {
    if (info.template) {
      // The rule has a "rewriting template", given as the name
      // of the fact to use in rewriting.
      assert(typeof accept.site === 'number',
             function() {
               return 'Rule ' + ruleName + ' must use exactly 1 site.';
             });
      var thm = Y.getTheorem(info.template);
      var template = info.templateSide == 'right'
        ? thm.unHyp().getRight()
        : thm.unHyp().getLeft();
      return !!expr.findSubst(template);
    } else {
      // TODO: prevent selection of bound variables as terms.
      return (accept.site
              || (acceptTerm && accept.term)
              || (accept.bindingSite && expr instanceof Y.Lambda)
              || (accept.reducible
                  && expr instanceof Y.Call
                  && expr.fn instanceof Y.Lambda));
    }
  } else {
    return (accept.step
	    || (accept.equation && step.unHyp().isCall2('='))
	    || (accept.implication && step.unHyp().isCall2('==>')));
  }
}


//// RULE SELECTOR

/**
 * Constructor.  Arguments are input, an input field; source, a
 * function that returns autocompleter results; and selectionHandler,
 * a function of no arguments to call when there is a new selection.
 *
 * Public properties:
 *   node: the DOM node of the rendering.
 *   ruleName: name of currently selected rule.
 */
function RuleSelector(input, source, selectionHandler) {
  var self = this;
  this._input = input;
  this.node = input;
  this.ruleName = '';
  var align = Y.WidgetPositionAlign;
  var config = {resultFilters: ['startsWith'],
                resultHighlighter: 'startsWith',
		resultFormatter: resultFormatter,
                source: source,
                inputNode: input,
                render: true,
                minQueryLength: 0,
		activateFirstItem: true,
  };
  var ac = new Y.AutoCompleteList(config);
  this._completer = ac;
  // Do this after the event so handler actions such as updating the
  // input field override the default action.
  ac.after('select', function(event) {
      self.ruleName = event.result.text.replace(/^xiom/, 'axiom');
      selectionHandler();
    });
  input.on('focus', function() {
      if (input.get('value') == '') {
        // Query on "initial" focus, working around autocomplete
        // behavior that only queries on keystrokes.
        ac.sendRequest('');
      }
    });
}

/**
 * Used by the autocompleter to convert highlighted results into
 * fully-formatted results with hints.  Accepts a query and result list,
 * return a list of HTML-formatted results.
 */
function resultFormatter(query, results) {
  return Y.Array.map(results, function (result) {
      var ruleName = result.text.replace(/^xiom/, 'axiom');
      var info = Y.rules[ruleName].info;
      var hint = Y.Escape.html(info.hint || info.comment || '');
      return result.highlighted + '<i style="color: gray"> - ' + hint + '</i>';
    });	
}

/**
 * Return the RuleSelector to a "fresh" state, with no text in the
 * input field and no choices filtered out.
 */
RuleSelector.prototype.reset = function() {
  this._input.set('value', '');
  // Send an empty request to make sure the completer is laid out wide
  // enough to accommodate the widest lines.
  this._completer.sendRequest('');
}

/**
 * Take keyboard focus if the underlying widget can do so.
 */
RuleSelector.prototype.focus = function() {
  var self = this;
  window.setTimeout(function() { self._input.focus(); }, 0);
};


//// BASICRULESELECTOR

function BasicRuleSelector(source, selectionHandler) {
  this.source = source;
  var elt = document.createElement('select');
  // Note temporary dummy display text:
  elt.add(new Option('--', ''));
  var node = this.node = new Y.Node(elt);
  this.reset();
  var self = this;
  node.on('change', function() {
      var elt = node.getDOMNode();
      self.ruleName = elt.options[elt.selectedIndex].value;
      selectionHandler();
    });
}

/**
 * Return the RuleSelector to a "fresh" state, with no rule selected,
 * options matching the current selection(s).
 */
BasicRuleSelector.prototype.reset = function() {
  var elt = this.node.getDOMNode();
  // Delete all rule options, leave just the "choose rule" option.
  elt.options.length = 1;
  // This should behave very much like the resultFormatter function:
  Y.each(this.source(), function(name) {
      var ruleName = name.replace(/^xiom/, 'axiom');
      var info = Y.rules[ruleName].info;
      var hint = info.hint || info.comment || '';
      elt.add(new Option(name + ' - ' + hint, ruleName));
    });
  var header = elt.options[0];
  elt.options[0].text = ((elt.options.length == 1)
                         ? '-- Select step or expression --'
                         : '-- Choose rule or select step/expression --');
  this.node.set('selectedIndex', 0);
  this.ruleName = '';
};

/**
 * Take keyboard focus if the underlying widget can do so.
 * This is a harmless no-op on known touchscreen devices.
 */
BasicRuleSelector.prototype.focus = function() {
  var node = this.node;
  window.setTimeout(function() { node.focus(); }, 0);
};


//// INITIALIZATION

// Global variable, name to use for CPU profiles, or falsy to disable:
Y.profileName = '';

Y.stepTypes = stepTypes;
Y.siteTypes = siteTypes;

Y.StepEditor = StepEditor;
Y.stepPaths = stepPaths;
Y.stepSites = stepSites;
Y.eachArgType = eachArgType;

}, '0.1', {requires: ['array-extras', 'expr', 'autocomplete',
                      'autocomplete-filters', 'autocomplete-highlighters']});
