// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

// Set everything up immediately on load, avoiding changes to
// the global environment except through namespace "Toy".
(function() {

// Make application assertions available through "assert".
var assert = Toy.assertTrue;

var format = Toy.format;


//// PROOF STEP EDITOR

// CSS class names beginning with "sted-" are reserved to
// the step editor.  Access to nodes through their class
// should always work in the context of the step editor's node.

// All types that can be entered in a form.  Omits site, bindingSite,
// and reducible, which are currently not supported in forms.  See
// See comments for ruleInfo in engine.js for details on the types.
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
 * A ProofDisplay can have only one StepEditor.  It appears at the end
 * of an editable proof.
 *
 * TODO: Support essential step editing such as justification of an assumed
 * step, for steps that already exist.  Also rearranging proofs.
 *
 * Fields:
 * $node: DIV with the step editor's HTML, has class stepEditor.
 * ruleName: name of rule selected from the RuleMenu; used with form
 *   information in tryExecuteRule.
 * form: jQuery SPAN to hold the argument input form.
 * proofDisplay: ProofDisplay to edit
 * stepSuggester: StepSuggester used to show possible "next steps" based
 *   on rules applicable to any current selection.
 * lastRuleTime: Milliseconds consumed by last execution of tryRule.
 * lastRuleSteps: Steps used by last execution of tryRule.
 *
 * showRuleType: Selects type of rules to show, as determined by offerApproved.
 *   Takes effect when this editor is reset.
 * showRules: List of individual rules to show.  Takes effect when this
 *   editor is reset.
 */
function StepEditor(proofEditor) {
  // Make this available to all inner functions.
  var self = this;

  // TODO: Reconsider the distinction and the relationship between the
  // StepEditor and ProofEditor.
  self._proofEditor = proofEditor;
  self.proofDisplay = proofEditor.proofDisplay;
  self.lastRuleTime = 0;
  self.lastRuleSteps = 0;
  self.ruleName = '';
  self.showRuleType = 'general';
  self.showRules = [];

  // Create a DIV with the step editor content.
  var $div = $('<div class=stepEditor/>');

  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<input class=sted-clear type=button value=x title="Clear the input">');
  self.clearer.addClass('hidden');
  self.form = $('<span class=sted-form></span>');
  // Proof errors display.
  self.$proofErrors = $('<div class="proofErrors hidden"></div>');
  self.$node = $div;

  self.$advice = $('<div class="advice hidden"><b>Select an expression ' +
                   'with a click, checkbox selects the step.</b></div>');

  // Attach the "ruleWorking" to the ProofDisplay node so
  // it doesn't move when steps are inserted.
  // TODO: Position the thing relative to the document each time it is
  //   displayed, removing a dependency on proofDisplay.
  $(self.proofDisplay.node)
    .append($('<div class=ruleWorking/>').text('Working . . . '));

  var menu = new RuleMenu(self);
  // Suppress solution status display when the mouse is within the
  // menu, leaving more room for step suggestions.
  menu.onEnter(function() { proofEditor.requestStatusDisplay(false); });
  menu.onLeave(function() { proofEditor.requestStatusDisplay(true); });
  self.ruleMenu = menu;

  // This will contain suggestions for next steps.
  self.stepSuggester = new StepSuggester(self);
  $div.append(self.clearer, self.form, self.$proofErrors,
              self.$advice, self.stepSuggester.$node, menu.$node);

  // Install event handlers.
  self.clearer.on('click', function() { self.reset(); });
  // Keyboard events bubble to here from the inputs in the form.
  self.form.on('keydown', function(event) {
    if (event.keyCode == 13) {
      // <enter> key was hit
      self.tryExecuteRule(true);
    }
  });
  self.form.on('click', 'button', function() { self.tryExecuteRule(true); });
  // Always clear the errors when clicked.
  self.$proofErrors.on('click', '.clearer', function() {
      self.$proofErrors.hide();
    });
}

StepEditor.prototype.refresh = function() {
  this.ruleMenu.refresh();
  this.stepSuggester.refresh();
};

/**
 * Returns the Expr selected in this StepEditor, or a falsy value if
 * there is none.
 */
StepEditor.prototype.selectedExpr = function() {
  var step = this.selection;
  return step && step.selection;
};

/**
 * Marks this StepEditor as busy or not in the UI.  See also
 * StepEditor.reset.
 */
StepEditor.prototype._setBusy = function(busy, complete) {
  this.$node.toggleClass('busy', busy);
  var $working = $(this.proofDisplay.node).find('.ruleWorking');
  if (busy) {
    // Temporarily turn on display of the ruleMenu to get its offset.
    this.ruleMenu.$node.toggleClass('hidden', false);
    var offset = this.stepSuggester.$node.offset();
    this.ruleMenu.$node.toggleClass('hidden', true);
    this.stepSuggester.$node.toggleClass('hidden', true);
    // and similarly for $working to set its offset.
    $working.toggle(true);
    $working.offset({left: offset.left + 40, top: offset.top + 5});
    // Then  turn it off and fade it back in.
    $working.toggle(false).fadeIn(200, complete);
  } else {
    // TODO: Consider adding hide / unhide methods to RuleMenu and
    //   StepSuggester instead of this rather crude dependency on their
    //   lengths.  The "unhide" would not necessarily remove the
    //   "hidden" style class, just set its visibility to "normal".
    this.ruleMenu.$node.toggleClass('hidden', this.ruleMenu.length === 0);
    this.stepSuggester.$node.toggleClass('hidden',
                                         !this.stepSuggester.showable());
    $working.fadeOut(200, complete);
  }
  // Clear the form.
  // TODO: Make these actions into a function/method, see "reset".
  this.clearer.addClass('hidden');
  this.form.html('');
  this.proofDisplay.setSelectLock(false);
};

/**
 * Reports the HTML message as an error in the step editor.
 */
StepEditor.prototype.error = function(message) {
  this.report('<b>' + message + '</b>');
};

/**
 * Report the error through the DOM and help the user debug in case it
 * has a "step" property.  The argument should be an Error object or
 * an HTML string.
 */
StepEditor.prototype.report = function(error) {
  var $proofErrors = this.$proofErrors;
  assert($proofErrors.length, 'proofJQ?');
  // Clicking _anywhere_ will actually clear the message.
  $proofErrors.show();
  $proofErrors.html('<button class=clearer>X</button>');
  if (error instanceof Error) {
    $proofErrors.append('<b>Error: ' + error.message + '</b>');
    if (error.step) {
      Toy.renderProof(error.step, $proofErrors);
    }
  } else {
    // It should be a string.
    $proofErrors.append(error);
  }
};

/**
 * Puts the step editor back in the initial state from the user's
 * point of view: visible with empty input, no rule-specific form,
 * available rules visible.  Does not clear any selection, and does
 * not affect the rules offered.  See also StepEditor._setBusy.
 */
StepEditor.prototype.reset = function() {
  this.clearer.addClass('hidden');
  this.form.html('');
  this.proofDisplay.setSelectLock(false);
  this._setBusy(false);
};

/**
 * Attempt to take keyboard focus.
 */
StepEditor.prototype.focus = function() {
  this.ruleMenu.focus();
};

/**
 * Handler for ruleMenu selection of a rule name.  Overall purpose is
 * to run the rule from information already available, otherwise to
 * display the input form.
 */
StepEditor.prototype.ruleChosen = function(ruleName) {
  // This method runs from a click, so a suggestion may well
  // be active.  Make sure it is not displayed.
  this.proofDisplay.hideSuggestion();
  this.ruleName = ruleName;
  var rule = Toy.rules[ruleName];
  if (rule) {
    var args = this.argsFromSelection(ruleName);
    if (this.checkArgs(args, rule.info.minArgs, false)) {
      tryRuleAsync(this, rule, args);
      return;
    }

    // Some args still need to be filled in; just show the rule's
    // form.

    var template = rule.info.form;
    // TODO: In the proof editor set up an event handler so the step editor
    //   can be aware of selections in the proof display (and also suppress
    //   selections instead of "selectLock").
    var step = this.proofDisplay.selection;
    var term = step && step.selection;
    var formatArgs = {term: (term && term.toHtml()) || '{term}'};
    if (template) {
      // These lines rely on reset of the step editor to return the hidden
      // status back to normal.
      // TODO: Probably the menu and suggester should have update methods
      //   that are sensitive to presence of a form or inference in progress.
      //   Code like this then would just tell them to refresh.
      this.ruleMenu.$node.toggleClass('hidden', true);
      this.stepSuggester.$node.toggleClass('hidden', true);
      // Template is not empty.  (If there is no template at all, the
      // rule will not be "offerable" and thus not selected.)
      this.clearer.removeClass('hidden');
      this.form.html(format(template, formatArgs));
      this.proofDisplay.setSelectLock(true);
      this.form.append(' <button>Go</button>');
      addClassInfo(this.form);
      if (!usesSite(rule)) {
	this.addSelectionToForm(rule);
      }
      // Focus the first empty text field of the form.
      this.form.find('input[type=text],input:not([type])').each(function() {
          if (!this.value) {
            this.focus();
            // Abort the loop.
            return false;
          }
        });
    } else {
      this.error(format('Rule needs a form: {1}', ruleName));
    }
  } else if (ruleName.slice(0, 5) === 'fact ') {
    // Values "fact etc" indicate use of rules.rewrite, and
    // the desired fact is indicated by the rest of the value.
    var siteStep = this.proofDisplay.selection;
    if (!siteStep || !siteStep.selection) {
      this.error('No selected site');
    }
    tryRuleAsync(this,
                 Toy.rules.rewrite,
                 [siteStep.original,
                  siteStep.prettyPathTo(siteStep.selection),
                  ruleName.slice(5)]);
  } else {
    assert(false, format('No such rule: {1}', ruleName));
  }
};

/**
 * Check that the given args Array is filled in with values that are
 * not instances of Error, and that up to minArgs, the values are not
 * the undefined value.  If reportError is true, report the problem in
 * the StepEditor, and in any case return true iff all is OK, else
 * false.  If the values are OK and some optional args are undefined,
 * truncate the args array to omit the unneeded undefined values.
 */
StepEditor.prototype.checkArgs = function(args, minArgs, reportError) {
  // Check that the args are all filled in.
  var required = (typeof minArgs == 'number'
                  ? minArgs
                  : args.length);
  for (var i = 0; i < args.length; i++) {
    var value = args[i];
    if (value === undefined && i < required) {
      if (reportError) {
        this.error('Undefined argument ' + i);
      }
      return false
    } else if (value instanceof Error) {
      if (reportError) {
	this.error(value.message);
      }
      return false;
    }
  }
  // Truncate the args array to omit optional args not supplied,
  // in case the rule looks at its arguments array.
  for (var i = required; i < args.length; i++) {
    if (args[i] === undefined) {
      args.length = i;
      break;
    }
  }
  return true;
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
 * e.g. step2 => step.  Also prevents autocompletion, basically because
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
 * Only call this if the rule does not use a site (usesSite).
 */
StepEditor.prototype.addSelectionToForm = function(rule) {
  var proofDisplay = this.proofDisplay;
  var step = proofDisplay.selection;
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
	    || (fieldType == 'implication' && step.unHyp().isCall2('=>'))) {
	  this.value = n;
          // Stop iteration.
	  return false;
	}
      }
    });
  }
};

/**
 * Fill in arguments for the rule named by the ruleMenu from the
 * current selection and the rule's input form, and if successful set
 * up actual execution and redisplay to occur after the UI has
 * opportunity to repaint.  If reportFailure is true, shows the
 * user any error message from calling fillFromForm.  Otherwise
 * just leaves the form up for the user to complete.
 */
StepEditor.prototype.tryExecuteRule = function() {
  // TODO: Get it together on failure reporting here.
  var ruleName = this.ruleName;
  var rule = Toy.rules[ruleName];
  var minArgs = rule.info.minArgs;
  var args = this.argsFromSelection(ruleName);
  this.fillFromForm(args);
  if (this.checkArgs(args, minArgs, true)) {
    tryRuleAsync(this, rule, args);
  }
};

/**
 * Turns on the editor's busy indicator and sets the rule up to run
 * with the given args as soon as the UI has opportunity to repaint.
 */
function tryRuleAsync(stepEditor, rule, args) {
  args.forEach(function(arg) {
      if (Toy.isProved(arg) && arg.isRendered()) {
        // Really all step arguments to all steps everywhere should be
        // non-renderable in the current implementation, but this situation
        // is arguably a greater risk than others.
        Toy.logError('Argument step ' + arg.stepNumber + ' is renderable.');
      }
    });
  // Flag the step editor as busy via its DOM node.
  stepEditor._setBusy(true, function() {
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
 * The rule runs with Toy.stepEditor set temporarily to this step
 * editor.
 *
 * Use this only in tryRuleAsync.
 */
StepEditor.prototype._tryRule = function(rule, args) {
  var self = this;
  var result = null;
  var startTime = Date.now();
  var startSteps = Toy.getStepCounter();
  try {
    if (Toy.profileName) {
      // Collect CPU profiling information.
      console.profile(Toy.profileName);
    }

    Toy.stepEditor = this;
    // Applies the rule here.
    result = rule.apply(null, args);
  } catch(error) {
    this._setBusy(false);
    this.report(error);
    return;
  } finally {
    Toy.stepEditor = null;
    if (Toy.profileName) {
      console.profileEnd();
    }
    // Update the rule stats and show them.
    this.lastRuleTime = Date.now() - startTime;
    this.lastRuleSteps = Toy.getStepCounter() - startSteps;
    // TODO: Consider providing an event with info the ProofEditor can
    //   use to display this info -- and move this code into handler.
    this._proofEditor.containerNode
      .find('.ruleTime').text(Math.ceil(this.lastRuleTime));
    this._proofEditor.containerNode
      .find('.ruleSteps').text(Math.ceil(this.lastRuleSteps));
    // Clear the initial invisible state.
    this._proofEditor.containerNode
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
    // TODO: Trigger an event and let the proofDisplay show the step,
    //   removing most of this code.  It may be desirable for the
    //   proof display to trigger another event after the step is
    //   successfully rendered, triggering auto-simplification.
    try {
      var top = $(window).scrollTop();
      this.proofDisplay.addStep(result);
    } catch(error) {
      this._setBusy(false);
      Toy.logError(error);
      error.message = 'Error rendering step ' + result + ': ' + error.message;
      this.report(error);
      debugger;
      return;
    }
    this.proofDisplay.deselectStep();
    // Make sure the proof errors field is cleared.
    this.$proofErrors.hide();
    // After the browser repaints, try simplifying the step
    // and adding the result to the proof if simplification
    // has any effect.
    Toy.afterRepaint(function() {
        var trial = autoSimplify(result);
        // If autoSimplify is a no-op, do not display the result.
        var simplified = (trial.sameAs(result)
                          ? result
                          : trial);
        self._setBusy(false);
        var steps = Toy.unrenderedDeps(simplified);
        var top2 = $(window).scrollTop();
        steps.forEach(function(step) {
            self.proofDisplay.addStep(step);
          });
        checkTop(top2);
      });
  }
  this.focus();
  checkTop(top);
};

/**
 * Supply this with an actual proof step.  If the rule has property
 * 'autoSimplify', this applies the value of the property to the step
 * as the auto-simplification.  If it returns a falsy value it will be
 * treated as a no-op (identity function).
 *
 * Otherwise if the step's rule has a "site" argument and global
 * variable Toy.autoSimplifyWholeStep is false, this simplifies the
 * site, otherwise it simplifies the whole step.
 */
function autoSimplify(step) {
  if (step.ruleArgs.length === 0) {
    // It is an axiom or theorem without parameters.
    // Simplification does not make sense, so don't do it.
    return step;
  }
  var simplifier = Toy.getRuleInfo(step).autoSimplify;
  if (simplifier) {
    // Call the rule's simplifier.  To suppress simplification,
    // supply a simplifier that does nothing.
    return simplifier(step) || step;
  }
  var path = Toy.getStepSite(step);
  if (path && !Toy.autoSimplifyWholeStep) {
    return Toy.rules.simplifySite(step, path) || assert(false);;
  } else {
    return Toy.rules.simplifyStep(step) || assert(false);
  }
}

/**
 * Returns the 1-based index of the position in the proof display
 * where the next step would be placed.  For automatic generation of
 * abbreviation variable names.
 */
StepEditor.prototype.slotIndex = function() {
  // New steps are always appended.
  return this.proofDisplay.steps.length + 1;
};

StepEditor.prototype.genAbbrevName = function() {
  return '$_' + this.slotIndex();
};

/**
 * Create and fill in part of the args array with the step or step and
 * path of the UI's selection if there is one, using the input
 * descriptor of of the StepEditor's current rule.  Currently not
 * picky about the detailed requirements of the various kinds of site
 * and step arguments.  Relies on other components to do these checks.
 */
StepEditor.prototype.argsFromSelection = function(ruleName) {
  var rule = Toy.rules[ruleName];
  var nargs = Math.max(rule.length, rule.info.maxArgs || 0);
  var args = new Array(nargs);
  var step = this.proofDisplay.selection;
  if (!step) {
    return args;
  }
  var expr = step.selection;
  var rule = Toy.rules[ruleName];
  var inputs = rule.info.inputs;
  // Fill in args information from a selection.
  if (expr) {
    var isSite = false;
    for (var type in siteTypes) {
      var input = inputs[type];
      if (input) {
        var position = Array.isArray(input) ? input[0] : input;
        args[position - 1] = step.original;
        args[position] = step.prettyPathTo(expr);
        isSite = true;
        // Only fill in one argument (pair) from the selection.
        break;
      }
    }
    if (!isSite && inputs.term) {
      var terms = inputs.term;
      var position = Array.isArray(terms) ? terms[0] : terms;
      args[position - 1] = expr;
    }
  } else {
    for (var type in stepTypes) {
      var input = inputs[type];
      if (input) {
        var position = Array.isArray(input) ? input[0] : input;
        args[position - 1] = step.original;
        // Only fill in one step.
        break;
      }
    }
  }
  return args;
};

/**
 * Fills in the arguments array with information from the form.
 */
StepEditor.prototype.fillFromForm = function(args) {
  var self = this;
  var rule = Toy.rules[this.ruleName];
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
 * types.  Returns an Error if it detects the input is not valid.
 * (Does not throw.)
 */
StepEditor.prototype.parseValue = function(value, type) {
  switch (type) {
  case 'step':
  case 'equation':
  case 'implication':
    if (!value.match(/^\d+$/)) {
      return new Error('Not a step number: ' + value);
    }
    var index = Number(value) - 1;
    if (index < 0 || index >= this.proofDisplay.steps.length) {
      return new Error('No such step: ' + value);
    }
    return this.proofDisplay.steps[Number(value) - 1].original;
  case 'bool':
    var expr = Toy.parse(value);
    var type = Toy.findType(expr);
    if (!(type === Toy.boolean || type instanceof Toy.TypeVariable)) {
      // Since variables do not have known types, some expressions may
      // have unknown types, and we allow that here.
      return new Error('Not a true/false expression:' + value);
    }
    return expr;
  case 'term':
    var expr = Toy.parse(value);
    var binOps = {'+': true, '-': true, '*': true, '/': true};
    // TODO: Change all infix parsing so the following hack
    //   becomes superfluous.
    // The following is just a hack so you can type "- <expr>" as
    // input to e.g. rules.applyToBoth with the usual meaning.
    if (expr.isCall1() && expr.fn.name in binOps) {
      var x = Toy.parse('x');
      expr = Toy.lambda(x, Toy.infixCall(x, expr.fn, expr.arg));
    }
    return expr;
  case 'varName':
    if (Toy.isVariableName(value)) {
      return value;
    } else {
      return new Error('Illegal variable name: ' + value);
    }
  case 'path':
    return Toy.path(value);
  case 'string':
    if (value.length) {
      return value;
    } else {
      return new Error('Empty field');
    }
  case 'optString':
    return value;

  default:
    return new Error('Type not parseable: ' + type);
  }
};

/**
 * Returns a list of names of rules that are "offerable" in the
 * sense of "offerable" returning true and offerApproved returning true.
 */
StepEditor.prototype.offerableRuleNames = function() {
  var matches = [];
  for (var name in Toy.rules) {
    if (this.offerable(name) && this.offerApproved(name)) {
      matches.push(name);
    }
  }
  matches.sort();
  return matches;
};

/**
 * Policy-based rule offering policy function based on this.showRules
 * and rule labels.  Returns a truthy value iff current policy is to
 * show the rule.
 */
StepEditor.prototype.offerApproved = function(name) {
  var labels = Toy.rules[name].info.labels;
  if (this.showRules.indexOf(name) >= 0) {
    return true;
  }
  switch (this.showRuleType) {
  case 'all':
    return true;
  case 'algebra':
    var expr = this.selectedExpr();
    return (expr && !expr.isReal()
            ? false
            : labels.algebra || labels.display);
  case 'general':
    return labels.basic || labels.display || labels.algebra;
  default:
    throw new Error('Bad rule policy value: ' + this.showRuleType);
  }
};

/**
 * Returns true iff the rule name can be offered by the UI.
 * Only rules with a "form" property are offerable at all.  If so --
 *
 * If the rule has a precheck and a single "inputs" declaration
 * of a kind that works with a selection, run the precheck and
 * return false if it is falsy.
 *  
 * Else if the proof has a current selection, the rule is offerable if
 * acceptsSelection returns true given the selected step and rule
 * name.
 *
 * Otherwise only rules that take no step and no site are offerable.
 */
StepEditor.prototype.offerable = function(ruleName) {
  var rule = Toy.rules[ruleName];
  var info = rule.info;
  // TODO: Test and then hopefully remove this test, which looks
  //   obsolete.
  if (!('form' in info)) {
    return false;
  }
  var step = this.proofDisplay.selection;
  if (step) {
    // Something is selected.
    var precheck = rule.precheck;
    var term = step.selection;
    var inputs = info.inputs;
    // See if the rule has a precheck that can "rule it out".
    // The rule must have a single input of a site or step type.
    if (precheck && Toy.mapSize(info.inputs) == 1 &&
        (term
         // This list needs to match siteTypes.
         ? inputs.site || inputs.bindingSite || inputs.reducible
         // This list needs to match stepTypes.
         : inputs.step || inputs.equation || inputs.implication)) {
      var ok = term ? precheck(step, step.pathTo(term)) : precheck(step);
      if (!ok) {
        return false;
      }
    }
    // Check if the rule accepts the selection.
    if (acceptsSelection(step, ruleName)) {
      // If the rule has a "toOffer" property, apply it as a further
      // test of offerability.
      var offerTest = info.toOffer;
      if (info.toOffer) {
        return offerTest(step, step.selection);
      }
      return true;
    }
  } else if (!info.form) {
    // The form property is present, but nothing in it, so
    // arguments cannot come from the form.
    return false;
  } else {
    // No selection, the rule must not require a step or site.
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
   * Returns a list of fact statements that are offerable in the UI,
   * currently all equational facts whose LHS matches the currently
   * selected term.
   *
   * In algebra mode, if the LHS is atomic, does not offer unless the
   * fact has the "algebra" label.
   */
  offerableFacts: function() {
    var self = this;
    var facts = [];
    var step = this.proofDisplay.selection;
    if (step) {
      var expr = step.selection;
      var TypeConstant = Toy.TypeConstant;
      // Returns true (a mismatch) iff both Exprs have types that
      // are type constants (in practice real or boolean), and the
      // types are not the same.  This is a crude check, but covers
      // the cases of usual interest.
      function typesMismatch(e1, e2) {
        var e1Type = e1.hasType();
        var e2Type = e2.hasType();
        return (e1Type instanceof TypeConstant &&
                e2Type instanceof TypeConstant &&
                // Perhaps compare the names of the type constants?
                e1Type != e2Type);
      }
      if (expr) {
        Toy.eachFact(function(info) {
            var goal = info.goal;
            if (!goal.isRewriter()) {
              return;
            }
            var lhs = goal.eqnLeft();
            if (typesMismatch(expr, lhs)) {
              return;
            }
            if (expr.matchSchema(lhs)) {
              if (self.showRuleType == 'algebra') {
                if (info.labels.algebra) {
                  facts.push(goal);
                }
                // Otherwise don't show the fact in algebra mode.
              } else {
                facts.push(goal);
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
 * step is selected.
 *
 * If something is selected, this accepts rules that can use that input
 * as an argument.
 */
function acceptsSelection(step, ruleName) {
  var info = Toy.rules[ruleName].info;
  var argInfo = info.inputs;
  if (!argInfo) {
    // If there is no information about arguments, fail.
    return false;
  }
  // Selected expression (within a step).
  var expr = step.selection;
  if (expr) {
    if (info.isRewriter && info.using) {
      // The rule has a "rewriting template", given as the name
      // of the fact to use in rewriting.
      assert(typeof argInfo.site === 'number',
             function() {
               return 'Rule ' + ruleName + ' must use exactly 1 site.';
             });
      // Check that the expression matches the LHS of the template.
      return !!expr.findSubst(info.using.unHyp().getLeft());
    } else {
      // Otherwise OK if it takes a site, or is a proper binding site
      // or a beta-reducible expression.
      // 
      // TODO: prevent selection of bound variables as terms.
      return (argInfo.site
              || argInfo.term
              || (argInfo.bindingSite && expr instanceof Toy.Lambda)
              || (argInfo.reducible
                  && expr instanceof Toy.Call
                  && expr.fn instanceof Toy.Lambda));
    }
  } else {
    // If the rule needs a site, do not accept just a step.
    return (!argInfo.site &&
            (argInfo.step
             || (argInfo.equation && step.unHyp().isCall2('='))
             || (argInfo.implication && step.unHyp().isCall2('=>'))));
  }
}


/**
 * Produces a rule menu entry from a ruleName, with "axiom"
 * potentially shortened to "xiom".  Called with a (rendered) step if
 * there is a selection, the selected term if a term is selected, and
 * the menu's ProofEditor.
 *
 * This returns either a falsy value (including the empty string),
 * indicating the rule will not be offered, or a string with the menu
 * HTML, or an array of strings, indicating multiple menu items for
 * this rule with the possibly selected step and term.  Returned
 * strings should be HTML text.
 *
 * If there is a selected term, it can be formatted using {term} in
 * the rule's "menu" format string, or {right} for the term's
 * right-hand neighbor when there is one.
 */
function ruleMenuInfo(ruleName, step, term, proofEditor) {
  ruleName = ruleName.replace(/^xiom/, 'axiom');
  var info = Toy.rules[ruleName].info;
  if (info.menuGen) {
    var gen = info.menuGen;
    return gen(ruleName, step, term, proofEditor);
  }
  if (Toy.isEmpty(info.inputs)) {
    // It is an axiom or theorem with no inputs.
    if (info.menu) {
      return info.menu;
    }
    var thm = Toy.getTheorem(ruleName);
    var thmText = Toy.trimParens(thm.unHyp().toHtml());
    if (ruleName.substring(0, 5) === 'axiom') {
      return 'axiom ' + thmText;
    } else {
      return 'theorem ' + thmText;
    }
  } else {
    // If there are inputs uses info.menu or some fallback.  This
    // defers the rendering work to the RuleMenu code where it is more
    // convenient and the HTML has been converted to DOM structure.
    var formatArgs = {term: '<span class=menuSelected></span>',
                      right: '<span class=menuRightNeighbor></span>'};
    if (info.menu) {
      return Toy.format(info.menu, formatArgs);
    } else {
      // TODO: Reconcile use of math markup here vs. non-use in menus.
      return Toy.mathMarkup(info.basicTooltip || 'menu?');
    }
  }
}


//// STEPSUGGESTER

/**
 * Widget that displays suggestions for possible next steps.  Has
 * public properties:
 *
 * stepEditor: StepEditor of which this is part.
 * display: ProofDisplay that holds the suggested steps.
 * $node: jQuery with DOM node of the widget presentation.
 */
function StepSuggester(stepEditor) {
  var self = this;
  self.stepEditor = stepEditor;
  var nexts = self.display = new Toy.ProofDisplay();
  $(nexts.node).addClass('nextSteps');
  var $node = self.$node = $('<div class="nextStepsContainer hidden">');
  $node.append('<b>Some next step options:</b></div>', nexts.node);
  // When activated, this will update the display when the event loop
  // next comes back to idle.
  self._refresher = new Toy.Refresher(self._update.bind(self));
  self._suggestions = [];

  // Event handling

  $node.on('click', '.stepSelector', function(event) {
      var dStep = Toy.getProofStep(event.target);
      var step = dStep.original;
      var rule = Toy.rules[step.ruleName];
      Toy.tryRuleAsync(stepEditor, rule, step.ruleArgs);
    });
}

var suggesterMethods = {

  /**
   * Use this to indicate that some state has changed which may affect
   * the desired list of step suggestions.
   */
  refresh: function() {
    this._refresher.activate();
  },

  /**
   * Returns true if there is data here to show.
   */
  showable: function() {
    return this.display.steps.length > 0;
  },

  /**
   * Internal to the StepSuggester; updates the display of suggested
   * next steps.
   *
   * The current policy is to offer all rules that are offerable and
   * have a "offerExample" property with truthy values, and to offer
   * all facts that are offerable.
   */
  _update: function() {
    var self = this;
    var display = self.display;
    var stepEditor = self.stepEditor;
    // Hide the nextSteps display temporarily; show it later if not empty.
    self.$node.addClass('hidden');
    display.setSteps([]);
    // If suggestions are disabled, stop here.
    if (!Toy.useStepSuggester) {
      return;
    }
    var mainDisplay = stepEditor.proofDisplay;
    var step = mainDisplay.selection;
    // Stop work on building suggestions.  This only affects ones
    // not yet displayed.
    self._suggestions.forEach(function(promise) {
        promise.cancel();
      });
    self._suggestions = [];
    var factsToOffer = [];
    if (step) {
      var term = step.selection;
      var path = term && step.prettyPathTo(term);
      var rules = Toy.rules;
      display.prevStep = step;
      // Given an RPC result wrapper, this adds its step if appropriate
      // and possible, and 
      function addStep(wrapper) {
        var result = wrapper.result;
        if (!self._suggestions.find(function(promise) {
              return promise.id === wrapper.id;
            })) {
          Toy.rpcLog('Not adding step for old RPC', wrapper.id);
        }
        if (self._suggestions.find(function(promise) {
              return promise.id === wrapper.id;
            }) && !result.step.matches(step)) {
          // A simplifer may return a step identical to its
          // input, which is intended to be ignored.
          display.addStep(result.step);
          if (self.showable()) {
            self.$node.removeClass('hidden');
            stepEditor.$advice.addClass('hidden');
          }
        }
      }
      stepEditor.offerableRuleNames().forEach(function(name) {
          var info = rules[name].info;
          if (info.offerExample) {
            // TODO: Report or handle error returns.
            sendRule(name, path ? [step.original, path] : [step.original])
              .addTo(self._suggestions)
              .then(addStep)
              .catch(function(wrapper) {
                  var msg = 'Rule suggestion error {1}: {2}';
                  console.warn(Toy.format(msg, wrapper.result.type,
                                          wrapper.result.message));
                });
          }
        });
      factsToOffer = stepEditor.offerableFacts();
      factsToOffer.forEach(function(statement) {
          self.length++;
          // TODO: Report or handle error returns.
          sendRule('rewrite',
                   [step.original,
                    step.prettyPathTo(step.selection),
                    statement])
            .addTo(self._suggestions)
            .then(addStep)
            .catch(function(wrapper) {
                var msg = 'Fact suggestion {1}:\n  {2}';
                console.warn(Toy.format(msg, wrapper.result.type,
                                        wrapper.result.message));
              });
        });
    }
  }
};
Object.assign(StepSuggester.prototype, suggesterMethods);


//// RULEMENU

/**
 * Widget that displays a list of rules for the user to try
 * if desired. Constructor argument is the StepEditor it
 * applies to when updating itself.
 *
 * Public properties:
 *
 * stepEditor: StepEditor as passed to the constructor.
 * length: current number of items in the menu.
 * changed: true iff its refresh has been activated, but
 *   the update has not yet run.
 *
 * onEnter, method: pass a function to call when the mouse enters.
 * onLeave, method: pass a function to call when the mouse leaves.
 *
 * Internal-ish properties:
 * hovering: DOM node under mouse or null.
 */
function RuleMenu(stepEditor) {
  var self = this;
  self.stepEditor = stepEditor;
  self._refresher = new Toy.Refresher(self._update.bind(self));
  self.length = 0;
  self.changed = false;
  // A rule menu item node or null.  If the mouse is hovering over an
  // item at any given time, this will be it.
  self.hovering = null;

  // Rule chooser:
  var $node = $('<div class=ruleMenu><b>Actions to try:</b></div>');
  self.$node = $node;
  self.$items = $('<div class=rulesItems/>');
  // An intermediate DIV.  This one is set to have vertical scrolling,
  // and the rulesItems div can be inline-block to shrink-wrap itself
  // around the individual items.
  var $scrollArea = $('<div class=scrollingMenu/>');
  $scrollArea.append(self.$items);
  $node.append($scrollArea);

  // Concise code to set up pseudo-events for "enter" and "leave".
  // Note that the methods are on the instance, not the prototype.
  // Invoke via onEnter and onLeave methods.  Note: leavers are also
  // called when the menu is hidden.
  var enters = $.Callbacks();
  self.onEnter = enters.add.bind(enters);
  $scrollArea.on('mouseenter', function() {
      enters.fire();
    });
  var leavers = $.Callbacks();
  self.onLeave = leavers.add.bind(leavers);
  $scrollArea.on('mouseleave', function() {
      leavers.fire();
    });
  // Make the leavers available from methods.
  self._leavers = leavers;

  $node.on('click', '.ruleItem', function(event) {
      // Run the step editor's ruleChosen method with
      // the ruleName of the menu item.
      self.stepEditor.ruleChosen($(this).data('ruleName'));
    });

  // Here are handlers for "enter" and "leave".  This code avoids
  // assuming that these events come in pairs.
  $node.on('mouseenter', '.ruleItem', function(event) {
      handleMouseEnterItem(self, this, event);
    });
  // When the mouse leaves an item, hide any suggested step.  If a
  // request has been issued for an appropriate suggestion, but is
  // still waiting in the queue, remove it from the queue and note
  // that no request is pending.
  $node.on('mouseleave', '.ruleItem', function(event) {
      self.hovering = null;
      var $this = $(this);
      stepEditor.proofDisplay.hideSuggestion();
      var promise = $this.data('promise');
      if (promise && promise.dequeue()) {
        $this.removeData('promise');
      }
    });
}

/**
 * Event handler for mouseenter events on RuleMenu items.
 */
function handleMouseEnterItem(ruleMenu, node, event) {
  var stepEditor = ruleMenu.stepEditor;
  var display = stepEditor.proofDisplay;
  // Note that this item is currently hovered.
  ruleMenu.hovering = node;
  var $node = $(node);
  // The "suggestion" data property indicates that a suggestion has
  // been computed for this menu item.  It is a DOM node that may
  // have a proofStep in it.
  var working = display.suggestionMessage('Working . . . ');
  display.suggest(working);
  var suggestion = $node.data('suggestion');
  if (suggestion) {
    // A suggestion is already computed; show it.
    display.suggest(suggestion);
  } else if (!$node.data('promise')) {
    // The "promise" data property indicates that a request for a
    // step has been issued.
    var ruleName = $node.data('ruleName');
    var promise;
    if (ruleName.slice(0, 5) === 'fact ') {
      // See StepEditor.ruleChosen for essentially the same code.
      // Values "fact etc" indicate use of rules.rewrite, and
      // the desired fact is indicated by the rest of the value.
      var siteStep = display.selection;
      if (!siteStep || !siteStep.selection) {
        stepEditor.error('No selected site');
      }
      promise = sendRule('rewrite', 
                         [siteStep.original,
                          siteStep.prettyPathTo(siteStep.selection),
                          ruleName.slice(5)]);
    } else if (Toy.rules[ruleName]) {
      // It is a rule other than a rewrite with fact.
      var rule = Toy.rules[ruleName];
      var args = stepEditor.argsFromSelection(ruleName);
      if (stepEditor.checkArgs(args, rule.info.minArgs, false)) {
        promise = sendRule(ruleName, args);
      } else {
        display.suggest(display.suggestionMessage('(needs user input)'));
      }
    } else {
      console.warn('No such rule:', ruleName);
    }
    if (promise) {
      $node.data('promise', promise);
      promise.then(function(info) {
          // The rule has successfully run.
          // First tidy up a little.
          $node.removeData('promise');
          var step = info.result.step;
          // Make note of the result, remembering its node.
          if (ruleMenu.hovering === $node[0]) {
            // At this (future) point in time, if this item is
            // hovered, show the result.
            var suggestionNode = display.stepSuggestion(step);
            $node.data('suggestion', suggestionNode);
            display.suggest(suggestionNode);

          }
        })
        .catch(function(info) {
            $node.removeData('promise');
            var messageNode = display.suggestionMessage('not applicable');
            $node.data('suggestion', messageNode);
            display.suggest(messageNode);
            console.error('Rule menu error', info.message);
          });
    }
  }
}

/**
 * Call this any time this object's display might need to be updated.
 * The display update will occur when the event loop becomes idle.
 */
RuleMenu.prototype.refresh = function() {
  this.changed = true;
  this._refresher.activate();
};

/**
 * Updates the step suggestions and rule menu to offer items
 * reflecting the currently-selected step or term, if any.
 */
RuleMenu.prototype._update = function() {
  var self = this;
  var stepEditor = self.stepEditor;
  // Clear any message displays whenever this changes, as when
  // the user selects an expression or step.
  stepEditor.$proofErrors.hide();



  var $items = self.$items;
  // Remove data and event handlers from suggestions.  They have
  // not been previously removed.
  $items.find('.ruleItem').each(function() {
      var suggestion = $(this).data('suggestion');
      suggestion && $(suggestion).remove();
    });
  $items.empty();
  var step = stepEditor.proofDisplay.selection;
  var term = step && step.selection;
  // Plain object describing each menu item.
  var itemInfos = [];
  stepEditor.offerableRuleNames().forEach(function(name) {
      var ruleName = name.replace(/^xiom/, 'axiom');
      if (!Toy.useStepSuggester || !Toy.rules[ruleName].info.offerExample) {
        // Info is a string or array of strings.
        var info = ruleMenuInfo(ruleName, step, term,
                                stepEditor._proofEditor);
        if (Array.isArray(info)) {
          // An array occurs when a rule may be used in multiple ways,
          // notably where there are multiple possible replacements of
          // a term by equal terms.
          info.forEach(function(msg) {
              itemInfos.push({ruleName: ruleName, html: msg});
            });
        } else if (info) {
          itemInfos.push({ruleName: ruleName, html: info});
        }
      }
    });
  
  if (!Toy.useStepSuggester) {
    self.stepEditor.offerableFacts().forEach(function(statement) {
        var text = statement.toString();
        var resultTerm = statement;
        if (statement.isEquation()) {
          if (statement.isCall2('=>')) {
            // Make the statement be the fact's equation.
            resultTerm = statement = statement.getRight();
          }
          // If as usual the LHS of the equation matches the selection,
          // set resultTerm to the result of substituting into the RHS.
          var step = self.stepEditor.proofDisplay.selection;
          var selection = step && step.selection;
          if (selection) {
            var subst = selection.matchSchema(statement.getLeft());
            if (subst) {
              resultTerm = statement.getRight().subFree(subst);
            }
          }
        }
        var display = '= <span class=menuResult></span>';
        if (subst) {
          display += (' <span class=description>using ' +
                      Toy.trimParens(statement.toHtml())
                      + '</span>');
        }
        // Value of the option; format of "fact <fact text>"
        // indicates that the text defines a fact to use in
        // rules.rewrite.
        var info = {ruleName: 'fact ' + text,
                    html: display,
                    result: resultTerm};
        itemInfos.push(info);
      });
  }
  itemInfos.sort(function(a, b) {
      return a.html.localeCompare(b.html);
    });
  var items = itemInfos.map(function(info) {
      var $item = $('<div class="ruleItem noselect"/>');
      $item.html(info.html);
      if (info.result) {
        $item.find('.menuResult').append(info.result.renderTerm());
      }
      $item.data('ruleName', info.ruleName);
      return $item
    });
  self.length = items.length
  self.changed = false;
  $items.append(items);
  if (term) {
    // If there is a selected term, render it and any right neighbor term,
    // and insert the renderings into their slots in menu items.
    var $term = $(term.copyForRendering().renderTerm());
    $items.find('.menuSelected').append($term);
    var rightTerm = Toy.getRightNeighbor(step, term);
    var $right = '?';
    if (rightTerm) {
      var $right = $(rightTerm.copyForRendering().renderTerm());
    }
    $items.find('.menuRightNeighbor').append($right);
  }
  self.$node.toggleClass('hidden', items.length === 0);
  if (items.length === 0) {
    // The menu can be hidden by clicks within it, and that does not
    // trigger a mouse leave event.
    self._leavers.fire();
  }

  // TODO: Consider updating the advice using Promises.
  var bothEmpty = (self.length == 0 &&
                   stepEditor.stepSuggester.$node.hasClass('hidden'));
  stepEditor.$advice.toggleClass('hidden', !bothEmpty);
};

/**
 * Take keyboard focus if the underlying widget can do so.
 * This is a harmless no-op on known touchscreen devices.
 */
RuleMenu.prototype.focus = function() {
  // var $node = this.$node;
  // window.setTimeout(function() { $node.focus(); }, 0);
};

/**
 * Ensures that the page's scrollTop (pageYOffset) remains at the
 * level given by its argument, recorded previously.  This helps work
 * around undesirable and weird scrolling induced by inserting or
 * deleting flexbox nodes in the DOM.  There is also one similar
 * workaround in rendering.js.
 */
function checkTop(oldTop) {
  function reset() {
    var top = $(window).scrollTop();
    if (top !== oldTop) {
      /*
      console.log(Toy.format('Resetting scrolltop from {1} to {2} at {3}.',
                             top, oldTop, new Date().toISOString()));
      */
      $(window).scrollTop(oldTop);
    }
  }
  reset();
  // Uncomment this to reset again a little bit later.
  // window.setTimeout(reset, 100);
}

/**
 * Enqueue an RPC message to an inference worker, returning a Promise
 * to receive the result.
 */
function sendRule(name, args) {
  return Toy.rpcQueue.enqueue({action: 'rule', name: name, args: args});
}


//// INITIALIZATION

/**
 * RPC setup for Mathtoys:
 */
$(function () {
    var receiver = {
      actions: {
        // The "rule" action returns a resulting step as its "step"
        // property, or standard error information in case of error.
        rule: function(message) {
          var step = Toy.rules[message.name].apply(null, message.args);
          return {step: step};
        }
      }
    };
    var fakeWorker = new Toy.FakeRpcWorker(receiver);
    var queue = new Toy.MessageQueue();
    queue.addWorker(fakeWorker);
    // This is the endpoint for accessing worker threads via RPC.
    Toy.rpcQueue = queue;
  });


// For testing:
Toy.autoSimplify = autoSimplify;

// Global variable to enable use of StepSuggester.
Toy.useStepSuggester = false;

// Global variable, name to use for CPU profiles, or falsy to disable:
Toy.profileName = '';

// Global setting controlling auto-simplification.
Toy.autoSimplifyWholeStep = true;

// Export public names.
Toy.stepTypes = stepTypes;
Toy.siteTypes = siteTypes;

Toy.StepEditor = StepEditor;

// Global variable set during execution of a rule from a step editor.
Toy.stepEditor = null;

Toy.tryRuleAsync = tryRuleAsync;

})();
