// Copyright 2011, 2012, 2013 Crispin Perdue.  All rights reserved.

// Set everything up immediately on load, avoiding changes to
// the global environment except through namespace "Toy".
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
 * $node: DIV with the step editor's HTML.
 * form: jQuery SPAN to hold the argument input form.
 * proofControl: ProofControl to edit
 * controller: ProofEditor containing this StepEditor.
 * lastRuleTime: Milliseconds consumed by last esecution of tryRule.
 * lastRuleSteps: Steps used by last execution of tryRule.
 *
 * showRuleType: Selects type of rules to show, as determined by offerOk.
 *   Takes effect when this editor is reset.
 * showRules: List of individual rules to show.  Takes effect when this
 *   editor is reset.
 */
function StepEditor(controller) {
  // Make this available to all inner functions.
  var self = this;

  self.controller = controller;
  self.proofControl = controller.proofControl;
  self.lastRuleTime = 0;
  self.lastRuleSteps = 0;

  // Create a DIV with the step editor content.
  var div = $('<div class=stepEditor style="clear: both"></div>');
  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<input class=sted-clear type=button value=x title="Clear the input">');
  self.clearer.addClass('hidden');
  div.append(self.clearer);
  self.form = $('<span class=sted-form></span>');
  div.append(self.form);
  self.$node = div;

  self.showRuleType = 'algebra';
  self.showRules = [];

  // Attach the "ruleWorking" to the ProofControl node so
  // it doesn't move when steps are inserted.
  $(self.proofControl.node)
    .append($('<div class=ruleWorking/>').text('Working . . . '));
  var widget = new BasicRuleSelector(self);
  self.ruleSelector = widget;
  div.append(widget.$node);
             
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

/**
 * Marks this StepEditor as busy in the UI.
 */
StepEditor.prototype._setBusy = function(busy, complete) {
  this.$node.toggleClass('busy', busy);
  var $working = $(this.proofControl.node).find('.ruleWorking');
  if (busy) {
    var offset = this.ruleSelector.$node.offset();
    // The node needs to be shown to set its offset.
    $working.toggle(true);
    $working.offset({left: offset.left + 40, top: offset.top + 25});
    // Then  turn it off and fade it back in.
    $working.toggle(false).fadeIn(200, complete);
  } else {
    $working.fadeIn(0).fadeOut(1000, complete);
  }
};

/**
 * Handle errors in the step editor.  Displays step information in an
 * element named "proofErrors" if there is one.
 */
StepEditor.prototype.error = function(message) {
  // TODO: implement, really, through a message area.
  window.alert(message);
};

/**
 * Report the error through the DOM and help the user debug in case it
 * has a "step" property.
 */
StepEditor.prototype.report = function(error) {
  var $proofErrors = this.controller.$proofErrors;
  assert($proofErrors.length, 'proofJQ?');
  // Clicking _anywhere_ will actually clear the message.
  $proofErrors.show();
  $proofErrors.html('<button>X</button>');
  if (error instanceof Error) {
    $proofErrors.append('<b>Error: ' + error.message + '</b>');
    if (error.step) {
      Toy.renderProof(error.step, $proofErrors);
    }
  } else {
    // It should be a string.
    $proofErrors.append('<b>' + error + '</b>');
  }
};

/**
 * Puts the step editor back in the initial state from the user's
 * point of view: visible with empty input, no rule-specific form.
 */
StepEditor.prototype.reset = function() {
  this.clearer.addClass('hidden');
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
      this.clearer.removeClass('hidden');
      this.form.html(template);
      addClassInfo(this.form);
      if (!usesSite(rule)) {
	this.addSelectionToForm(rule);
      }
      // Focus the first empty text field of the form.
      this.form.find('input:text').each(function() {
          if (!this.value) {
            this.focus();
            // Abort the loop.
            return false;
          }
        });
    }
    this.tryExecuteRule(false);
  } else if (value.slice(0, 5) === 'fact ') {
    // Values "fact etc" indicate use of rewriteWithFact, and
    // the desired fact is indicated by the rest of the selection.
    var siteStep = this.proofControl.selection;
    if (!siteStep || !siteStep.selection) {
      this.error('No selected site');
    }
    tryRuleAsync(this,
                 Toy.rules.rewriteWithFact,
                 [siteStep.original,
                  siteStep.prettyPathTo(siteStep.selection),
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
 * e.g. step2 ==> step.  Also prevents autocompletion, basically because
 * some sites add autosuggest entries to fields named "term".
 */
function addClassInfo(form) {
  form.find('input').each(function() {
      // Note: the pattern matches any string.
      var className = this.name.match(/^(.*?)\d*$/)[1];
      $(this).addClass(className);
      $(this).attr('autocomplete', 'off');
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
  var proofControl = this.proofControl;
  var step = proofControl.selection;
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
    return;
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
      return;
    }
  }
  tryRuleAsync(this, rule, args);
};

/**
 * Runs StepEditor.tryRule, but only after the event handling loop has
 * returned to the top level so the display can update.  Marks the
 * step editor's DOM node as busy immediately so the display can
 * reflect its change in state.
 */
function tryRuleAsync(stepEditor, rule, args) {
  // Flag the step editor as busy via its DOM node.
  stepEditor._setBusy(true, function() {
      stepEditor.reset();
      Toy.afterRepaint(stepEditor._tryRule.bind(stepEditor, rule, args));
    });
}

/**
 * Tries to run the given rule (function) with the given rule
 * arguments, adding the result to this step editor's proof.  Catches
 * and reports any errors.  Returns true if the rule succeeded, false
 * if it catches an error.  Reports there was nothing to do if the
 * rule returns its input or a null value.
 *
 * Private to tryRuleAsync.
 */
StepEditor.prototype._tryRule = function(rule, args) {
  var result = null;
  var startTime = Date.now();
  var startSteps = Toy.getStepCounter();
  try {
    if (Toy.profileName) {
      // Collect CPU profiling information.
      console.profile(Toy.profileName);
    }
    result = rule.apply(null, args);
  } catch(error) {
    this.report(error);
    return;
  } finally {
    if (Toy.profileName) {
      console.profileEnd();
    }
    // Update the rule stats and show them.
    this.lastRuleTime = Date.now() - startTime;
    this.lastRuleSteps = Toy.getStepCounter() - startSteps;
    this.controller.containerNode
      .find('.ruleTime').text(Math.ceil(this.lastRuleTime));
    this.controller.containerNode
      .find('.ruleSteps').text(Math.ceil(this.lastRuleSteps));
    // Clear the initial invisible state.
    this.controller.containerNode
      .find('.ruleStats').toggleClass('invisible', false);
  }
  if (!result || result.rendering) {
    // The work is done, show that the prover is not busy.
    this._setBusy(false);
    // If there is already a rendering, Expr.justify must have found
    // that the "new" step was identical to one of its dependencies,
    // so don't try to add it.  The implementation only currently
    // supports one render per step anyway.
    this.report('nothing done');
  } else {
    this.proofControl.addStep(result);
    this.proofControl.deselectStep();
    // Clear the proof errors field.
    this.controller.$proofErrors.hide();
    // After the browser repaints, try simplifying the step
    // and adding the result to the proof if simplification
    // has any effect.
    var self = this;
    Toy.afterRepaint(function() {
        var simplified = Toy.rules.simplifyStep(result);
        self._setBusy(false);
        if (simplified && !simplified.rendering) {
          self.proofControl.addStep(simplified);
        }
      });
  }
  this.focus();
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
      var step = this.proofControl.selection;
      var expr = step && step.selection;
      if (expr) {
	var position = inputs[type];
	if ((typeof position) == 'number') {
	  args[position - 1] = step.original;
	  args[position] = step.prettyPathTo(expr);
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
    if (index < 0 || index >= this.proofControl.steps.length) {
      throw new Error('No such step: ' + value);
    }
    return this.proofControl.steps[Number(value) - 1].original;
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
      var x = Toy.parse('x');
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
 * Policy-based rule offering policy function.  Returns a truthy value
 * iff current policy is to show the rule.
 */
StepEditor.prototype.offerOk = function(name) {
  var labels = Toy.rules[name].info.labels;
  if (this.showRules.indexOf(name) >= 0) {
    return true;
  }
  switch (this.showRuleType) {
  case 'all':
    return true;
  case 'algebra':
    return labels.algebra || labels.display;
  case 'general':
    return labels.basic || labels.display || labels.algebra;
  default:
    throw new Error('Bad rule policy value');
  }
};

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
  var step = this.proofControl.selection;
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

  /**
   * Returns a list of fact objects that are offerable in the UI,
   * currently all that are equational (equation, possibly with
   * conditions).
   */
  offerableFacts: function() {
    var facts = [];
    var step = this.proofControl.selection;
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
 * Produces a rule menu entry from a ruleName, with "axiom"
 * potentially shortened to "xiom".  Result is currently text,
 * but may become HTML in the future.
 *
 * The term argument
 */
function ruleMenuText(ruleName, term) {
  ruleName = ruleName.replace(/^xiom/, 'axiom');
  var info = Toy.rules[ruleName].info;
  if (Toy.isEmpty(info.inputs)) {
    // It is an axiom or theorem with no inputs.
    if (info.menu) {
      return info.menu
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
  } else {
    // If there are inputs uses info.menu or some fallback.
    return Toy.unicodify((info.menu && Toy.format(info.menu, {term: term})) ||
                         info.formula || info.comment || '');
  }
}


//// BASICRULESELECTOR

function BasicRuleSelector(stepEditor, selectionHandler, options) {
  var self = this;
  self.stepEditor = stepEditor;
  self.ruleName = '';

  self._refresher = new Toy.Refresher(self.update.bind(self));

  // Rule chooser:
  self.$node = $('<div class=ruleSelector/>');
  self.update();

  self.$node.on('click', '.ruleItem', function(event) {
    var ruleName = $(this).data('ruleName');
    self.ruleName = ruleName;
    self.stepEditor.handleSelection();
  });
}

BasicRuleSelector.prototype.refresh = function() {
  this._refresher.activate();
}

/**
 * Return the RuleSelector to a "fresh" state, with no rule selected,
 * offered items compatible the currently-selected step or term.
 */
BasicRuleSelector.prototype.update = function() {
  var self = this;
  self.$node.empty();
  self.$node.fadeOut(0);
  self.$node.fadeIn();
  $header = $('<div class=rules-header/>');
  self.$node.append($header);
  var step = this.stepEditor.proofControl.selection;
  var term = step && step.selection;
  // Map from rule display text to rule name.
  var byDisplay = {};
  var displayTexts = [];
  self.stepEditor.offerableRuleNames().forEach(function(name) {
      var ruleName = name.replace(/^xiom/, 'axiom');
      var text = ruleMenuText(ruleName, term);
      displayTexts.push(text);
      byDisplay[text] = ruleName;
    });
  self.stepEditor.offerableFacts().forEach(function(fact) {
    var expr = Toy.getStatement(fact);
    var text = expr.toString();
    if (expr.isEquation() && expr.isCall2('==>')) {
      expr = expr.getRight();
    }
    var display = expr.toUnicode();
    if (display[0] === '(') {
      display = display.slice(1, -1);
    }
    display = 'use ' + display;
    displayTexts.push(display);
    // Value of the option; format of "fact <fact text>"
    // indicates that the text defines a fact to use in
    // rewriteWithFact.
    byDisplay[display] = 'fact ' + text;
  });
  displayTexts.sort(function(a, b) { return a.localeCompare(b); });
  displayTexts.forEach(function(display) {
      var $item = $('<div class="ruleItem noselect"/>');
      $item.text(display);
      $item.data('ruleName', byDisplay[display]);
      self.$node.append($item);
    });
  self.ruleName = '';
  // TODO: Generate smarter messages for rules that work without a UI
  //   selection (most theorems and theorem generators).
  $header.text(displayTexts.length
               ? 'Actions:'
               : 'Select a step or expression with a click.');
};

/**
 * Take keyboard focus if the underlying widget can do so.
 * This is a harmless no-op on known touchscreen devices.
 */
BasicRuleSelector.prototype.focus = function() {
  // var $node = this.$node;
  // window.setTimeout(function() { $node.focus(); }, 0);
};


//// INITIALIZATION

// Global variable, name to use for CPU profiles, or falsy to disable:
Toy.profileName = '';

Toy.stepTypes = stepTypes;
Toy.siteTypes = siteTypes;

Toy.StepEditor = StepEditor;

Toy.tryRuleAsync = tryRuleAsync;

})();
