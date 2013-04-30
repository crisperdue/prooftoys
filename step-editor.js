// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

(function() {

// Make application assertions available through "assert".
var assert = Toy.assertTrue;

//// PROOF STEP EDITOR

// CSS class names beginning with "sted-" are reserved to
// the step editor.  Access to nodes through their class
// should always work in the context of the step editor's node.
// The CSS classes are:
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
 * A ProofControl can have only one StepEditor.  It appears at the end
 * of an editable proof.
 *
 * TODO: Support essential step editing such as justification of an assumed
 * step, for steps that already exist.  Also rearranging proofs.
 *
 * Fields:
 * jq: DIV with the step editor's HTML.
 * form: jQuery SPAN to hold the argument input form.
 * saveRestore: jQuery button to control the save/restore area.
 * controller: ProofControl to edit
 */
function StepEditor(controller) {
  // Make this available to all inner functions.
  var self = this;

  self.controller = controller;

  // Create a DIV with the step editor content.
  var div = $('<div class=stepEditor style="clear: both"></div>');
  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<input class=sted-clear type=button value=x title="Clear the input">');
  self.clearer.addClass('invisible');
  div.append(self.clearer);

  // Selector holds rule selector and related controls, shown
  // and hidden as a group.
  var selectorSpan = $('<span class=ruleSelector></span>');
  div.append(selectorSpan);
  self._selectorSpan = selectorSpan;

  self.form = $('<span class=sted-form></span>');
  div.append(self.form);

  // TODO: Make this appear and disappear with the rule selector,
  // or move it somewhere else.
  var noform = $('<div style="margin-left: 1.5em"/>');
  div.append(noform);
  self.saveRestore =
    $('<input class=sted-save-restore type=button '
      + 'value="Save/restore proof ..." '
      + 'title="Save or restore proof state">')
  noform.append(self.saveRestore);
  // TODO: add more content here: div.append('<div>Hello World</div>');
  self.jq = div;

  // Install a rule selector
  if (Toy.useAutocompleter) {
    throw new Error('Autocompleter no longer supported');
  } else {
    // Append the actual rule selector.
    var widget = new BasicRuleSelector(self, $.proxy(self, 'handleSelection'));
    self.ruleSelector = widget;
    selectorSpan.append(widget.jq);

    // Append checkbox to control "all rules"
    selectorSpan.append('<label class=sted-show-all>' +
                        '<input type=checkbox>show all&nbsp;</label>');
    // Step editor has state controlling whether to show all rules.
    self.showAll = false;
    selectorSpan.find('input:checkbox').on('click', function(event) {
        self.showAll = this.checked;
        self.ruleSelector.offerAxioms = !self.ruleSelector.offerAxioms;
        self.reset();
      });
  }
  
  // Install event handlers.
  self.clearer.on('click', function() { self.reset(); });
  // Keyboard events bubble to here from the inputs in the form.
  self.form.on('keydown', function(event) {
    if (event.keyCode == 13) {
      // <enter> key was hit
      self.tryExecuteRule(true);
    }
  });
}

$.extend(StepEditor.prototype, {

  showSaveRestore: function(value) {
    this.saveRestore.toggle(value);
  },

  displayShowAll: function(value) {
    this._selectorSpan.find('label.sted-show-all').toggle(value);
  }

});



/**
 * Handle errors in the step editor.  Displays step information in an
 * element named "proofErrors" if there is one.
 */
StepEditor.prototype.error = function(message) {
  if (Toy.errors.length) {
    var last = Toy.errors[Toy.errors.length - 1];
    var proofJQ = $('#proofErrors');
    if (proofJQ.length) {
      proofJQ.append('<p><b>Errors: (' + Toy.errors.length
		       + ') ' + last.message + '</b></p>');
      if (last.step) {
        Toy.renderProof(last.step, proofJQ);
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
  this._selectorSpan.removeClass('hidden');
  this.clearer.addClass('invisible');
  this.form.html('');
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
  var value = this.ruleSelector.ruleName;
  var rule = Toy.rules[value];
  if (rule) {
    var template = rule.info.form;
    if (template) {
      // Template is not empty.  (If there is no template at all, the
      // rule will not be "offerable" and thus not selected.)
      this._selectorSpan.addClass('hidden');
      this.clearer.removeClass('invisible');
      this.form.html(template);
      addClassInfo(this.form);
      if (!usesSite(rule)) {
	this.addSelectionToForm(rule);
      }
      // Focus the first empty text field of the form.
      this.form.find('input:text').each(function() {
          if (!this.value) {
            this.focus();
            return false;
          }
        });
    }
    this.tryExecuteRule(false);
  } else if (value.slice(0, 5) === 'fact ') {
    var siteStep = this.controller.selection;
    if (!siteStep || !siteStep.selection) {
      this.error('No selected site');
      return false;
    }
    return this.tryRule(Toy.rules.rewriteWithFact,
                        [siteStep.original,
                         siteStep.pathTo(siteStep.selection),
                         value.slice(5)]);
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
  form.find('input').each(function() {
      // Note: the pattern matches any string.
      var className = this.name.match(/^(.*?)\d*$/)[1];
      $(this).addClass(className);
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
    form.find('input').each(function() {
      var fieldType = this.name.match(/^(.*?)\d*$/)[1];
      if (expr) {
	// TODO: Don't use the selection as a term if it will be used
	// by the rule as a site.
	if (fieldType == 'term') {
          // TODO: Use printing that is guaranteed reversible.
	  this.value = expr.toString();
          // Stop iteration.
	  return false;
	}
      } else {
	if (fieldType == 'step'
	    || (fieldType == 'equation' && step.unHyp().isCall2('='))
	    || (fieldType == 'implication' && step.unHyp().isCall2('==>'))) {
	  this.value = n;
          // Stop iteration.
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
  var rule = Toy.rules[this.ruleSelector.ruleName];
  // Initialize the args array length to be the number of its
  // named arguments.
  var args = new Array(rule.length);
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
  if (args.length != rule.length) {
    Toy.logError('Rule received unnamed arguments: ' + rule);
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
  return this.tryRule(rule, args);
};

/**
 * Try to run the given rule (function) with the given
 * rule arguments.  Catches and reports any errors.
 */
StepEditor.prototype.tryRule = function(rule, args) {
  var value = false;
  try {
    if (Toy.profileName) {
      // Collect CPU profiling information.
      console.profile(Toy.profileName);
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
  if (Toy.profileName) {
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
  var rule = Toy.rules[this.ruleSelector.ruleName];
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
  var rule = Toy.rules[this.ruleSelector.ruleName];
  $(this.form).find('input').each(function() {
    // The "name" attribute of the input element should be the name of
    // an input type, possibly followed by some digits indicating
    // which rule argument it will supply.
    var name = this.name;
    var match = name.match(/^(.+?)(\d*)$/);
    if (match) {
      var type = match[1];
      // Non-empty when referring to one of multiple args of the same
      // type.  Then the value of the entry in rule.info.inputs is a
      // list.
      var which = match[2];
      var inputs = rule.info.inputs;
      var argNum = which ? inputs[type][which - 1] : inputs[type];
      if (!argNum) {
	throw new Error('Internal error: no input descriptor for type ' + type);
      }
      // Fill in the actual argument.
      args[argNum - 1] = self.parseValue(this.value, type);
    } else {
      Toy.logError('Unrecognized input name: ' + name);
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
    var tokens = Toy.tokenize(value);
    // Throws an error if parsing fails:
    var expr = Toy.parse(tokens);
    if (tokens.length) {
      throw new Error('Extra input: "', + tokens[0] + '"');
    }
    var binOps = {'+': true, '-': true, '*': true, '/': true};
    // TODO: Change all infix parsing so the following hack
    //   becomes superfluous.
    // The following is just a hack so you can type "- 3" as
    // input to e.g. rules.applyToBoth with the usual meaning.
    if (expr.isCall1() && expr.fn.name in binOps) {
      expr = lambda(x, Toy.infixCall(x, expr.fn, expr.arg));
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
  var matches = [];
  for (var name in Toy.rules) {
    display = name.replace(/^axiom/, 'xiom');
    if (this.offerable(name)) {
      matches.push(display);
    }
  }
  matches.sort();
  return matches;
};

/**
 * Returns a list of names of rules that are "offerable" in the
 * sense of "offerable" returning true and offerOk returning true.
 */
StepEditor.prototype.offerableRuleNames = function() {
  var matches = [];
  for (var name in Toy.rules) {
    if (this.offerable(name) && this.offerOk(name)) {
      matches.push(name);
    }
  }
  matches.sort();
  return matches;
};

/**
 * Rulename-based rule offering policy function.  Returns a truthy value
 * iff current policy is to show the rule.
 */
StepEditor.prototype.offerOk = function(name) {
  if (this.showAll) {
    return true;
  } else {
    var labels = Toy.rules[name].info.labels;
    return labels.basic;
  }
}

/**
 * Returns true iff the rule name can be offered by the UI.
 * Only rules with a "form" property are offerable at all.  If so --
 *
 * If the proof has a current selection, the rule is offerable if
 * acceptsSelection returns true given the selected step, rule name, and
 * third argument of false.
 *
 * Otherwise only rules that take no step and no site are offerable.
 *
 * This assumes the given ruleName is in Toy.rules.
 */
StepEditor.prototype.offerable = function(ruleName) {
  var info = Toy.rules[ruleName].info;
  if (!('form' in info)) {
    return false;
  }
  var step = this.controller.selection;
  if (step) {
    // Something is selected.  Check if the rule accepts the
    // selection.
    return acceptsSelection(step, ruleName, false);
  } else {
    // No selection, the rule must take no step or site.
    for (type in info.inputs) {
      // Use "in", the type will not be an object method name.
      if (type in stepTypes || type in siteTypes) {
        return false;
      }
    }
    return true;
  }
};

$.extend(StepEditor.prototype, {

  offerableFacts: function() {
    var facts = [];
    var step = this.controller.selection;
    if (step) {
      var expr = step.selection;
      if (expr) {
        Toy.eachFact(function(fact) {
          var goal = fact.goal;
          if (goal.isEquation()) {
            var lhs = goal.eqnLeft();
            if (expr.matchSchema(lhs)) {
              facts.push(fact);
            }
          }
        });
      }
    }
    return facts;
  }
});

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
  var info = Toy.rules[ruleName].info;
  var accept = info.inputs;
  if (!accept) {
    // If there is no information about arguments, fail.
    return false;
  }
  // Selected expression (within a step).
  var expr = step.selection;
  if (expr) {
    if (info.isRewriter && info.using) {
      // The rule has a "rewriting template", given as the name
      // of the fact to use in rewriting.
      assert(typeof accept.site === 'number',
             function() {
               return 'Rule ' + ruleName + ' must use exactly 1 site.';
             });
      return !!expr.findSubst(info.using.unHyp().getLeft());
    } else {
      // TODO: prevent selection of bound variables as terms.
      return (accept.site
              || (acceptTerm && accept.term)
              || (accept.bindingSite && expr instanceof Toy.Lambda)
              || (accept.reducible
                  && expr instanceof Toy.Call
                  && expr.fn instanceof Toy.Lambda));
    }
  } else {
    return (accept.step
	    || (accept.equation && step.unHyp().isCall2('='))
	    || (accept.implication && step.unHyp().isCall2('==>')));
  }
}


/**
 * Used by the rule menu creator to convert one query result into a
 * fully-formatted menu entry with hints.  Accepts a query and result
 * object, returns a possibly HTML-formatted result.  The optional
 * boolean useHtml controls generation of HTML vs. non-HTML Unicode
 * text.
 */
function ruleMenuFormatter(query, result, useHtml) {
  var ruleName = result.text.replace(/^xiom/, 'axiom');
  var info = Toy.rules[ruleName].info;
  if (Toy.isEmpty(info.inputs)) {
    // It is an axiom or theorem with no inputs.
    // Axiom or theorem hints are treated as HTML, unlike all others!
    if (info.hint) {
      return info.hint;
    }
    var thmText;
    if (info.formula) {
      thmText = Toy.unicodify(info.formula);
    } else {
      var thm = Toy.getTheorem(ruleName);
      thmText = thm.unHyp().toUnicode();
      thmText = thmText.replace(/^\((.*)\)$/, '$1');
    }
    if (ruleName.substring(0, 5) === 'axiom') {
      return 'axiom ' + thmText;
    } else {
      return 'theorem ' + thmText;
    }
  } else if (info.formula) {
    return Toy.unicodify(info.formula);
  } else {
    var hint = info.hint || info.comment || '';
    if (useHtml) {
      return '<i style="color: gray">' + hint + '</i>';
    } else {
      return Toy.unicodify(hint);
    }
  }
}


//// BASICRULESELECTOR

function BasicRuleSelector(stepEditor, selectionHandler, options) {
  var self = this;
  self.stepEditor = stepEditor;
  self.ruleName = '';

  // TODO: put this state in the step editor.
  self.offerAxioms = options && options.axioms;

  // Rule chooser:
  var ruleChooser = $('<select/>');
  // The first option tells the user to select something,
  // message determined later.
  ruleChooser.append($('<option/>',
                       {text: '-- Apply a rule --', value: ''}));

  /* TODO:
  var thmChooser = $('<select/>');
  thmChooser.append($('<option/>',
                      {text: '-- Select an axiom or theorem --', value: ''}));

  var proverChooser = $('<select/>');
  proverChooser.append($('<option/>',
                         {text: '-- Prove a simple theorem --',
                             value: ''}));
  */

  this.jq = ruleChooser;

  this.reset();

  ruleChooser.change(function() {
      var elt = ruleChooser[0];
      self.ruleName = elt.options[elt.selectedIndex].value;
      selectionHandler();
    });
}

/**
 * Return the RuleSelector to a "fresh" state, with no rule selected,
 * offered items compatible the currently-selected step or term.
 */
BasicRuleSelector.prototype.reset = function() {
  var self = this;
  var elt = self.jq[0];
  // Delete all rule options, leave just the "choose rule" option.
  elt.options.length = 1;
  // Map from rule display text to rule name.
  var byText = {};
  var texts = [];
  self.stepEditor.offerableRuleNames().forEach(function(name) {
      var ruleName = name.replace(/^xiom/, 'axiom');
      if (self.offerAxioms || ruleName.slice(0, 5) != 'axiom') {
        var text = ruleMenuFormatter(null, {text: ruleName}, false);
        texts.push(text);
        byText[text] = ruleName;
      }
    });
  self.stepEditor.offerableFacts().forEach(function(fact) {
    var expr = Toy.getStatement(fact);
    var id = expr.dump();
    if (expr.isEquation() && expr.isCall2('==>')) {
      expr = expr.getRight();
    }
    var text = expr.toUnicode();
    if (text[0] === '(') {
      text = text.slice(1, -1);
    }
    text = 'use ' + text;
    texts.push(text);
    byText[text] = 'fact ' + id;
  });
  texts.sort(function(a, b) { return a.localeCompare(b); });
  texts.forEach(function(text) {
      elt.add(new Option(text, byText[text]));
    });
  var header = elt.options[0];
  elt.options[0].text = ((elt.options.length == 1)
                         ? '-- First select a term or step above --'
                         : '-- Choose a rule to apply --');
  elt.selectedIndex = 0;
  self.ruleName = '';
};

/**
 * Take keyboard focus if the underlying widget can do so.
 * This is a harmless no-op on known touchscreen devices.
 */
BasicRuleSelector.prototype.focus = function() {
  var jq = this.jq;
  window.setTimeout(function() { jq.focus(); }, 0);
};


//// INITIALIZATION

// Global variable, name to use for CPU profiles, or falsy to disable:
Toy.profileName = '';

Toy.stepTypes = stepTypes;
Toy.siteTypes = siteTypes;

Toy.StepEditor = StepEditor;

})();
