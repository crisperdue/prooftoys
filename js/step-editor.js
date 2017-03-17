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
 * $node: DIV with the step editor's HTML.
 * ruleName: name of rule selected from the RuleMenu; used with form
 *   information in tryExecuteRule.
 * form: jQuery SPAN to hold the argument input form.
 * proofDisplay: ProofDisplay to edit
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
  var div = $('<div class=stepEditor style="clear: both"></div>');

  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<input class=sted-clear type=button value=x title="Clear the input">');
  self.clearer.addClass('hidden');
  self.form = $('<span class=sted-form></span>');
  // Proof errors display.
  self.$proofErrors = $('<div class="proofErrors hidden"></div>');
  self.$node = div;

  // Attach the "ruleWorking" to the ProofDisplay node so
  // it doesn't move when steps are inserted.
  // TODO: Position the thing relative to the document each time it is
  //   displayed, removing a dependency on proofDisplay.
  $(self.proofDisplay.node)
    .append($('<div class=ruleWorking/>').text('Working . . . '));
  var menu = new RuleMenu(self);
  self.ruleMenu = menu;

  // This will contain suggestions for next steps.
  self.nextSteps = new Toy.ProofDisplay();

  div.append(self.clearer, self.form, self.$proofErrors,
             self.nextSteps.node, menu.$node);

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
    this.ruleMenu.$node.toggle(true);
    var offset = this.ruleMenu.$node.offset();
    this.ruleMenu.$node.toggle(false);
    // and similarly for $working to set its offset.
    $working.toggle(true);
    $working.offset({left: offset.left + 40, top: offset.top + 5});
    // Then  turn it off and fade it back in.
    $working.toggle(false).fadeIn(200, complete);
  } else {
    $working.fadeOut(200, complete);
  }
  this.ruleMenu.fadeToggle(!busy);
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
  this.ruleMenu.fadeToggle(true);
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
  this.ruleName = ruleName;
  var rule = Toy.rules[ruleName];
  if (rule) {
    var nargs = rule.length;
    // Initialize the args array length to be the number of its
    // named arguments.
    var args = new Array(nargs);
    this.fillFromSelection(args);
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
      this.ruleMenu.fadeToggle(false);
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
      this.form.find('input:text').each(function() {
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
 * TODO: Modify spec and implementation to just add step references
 * but not selected expressions to the form.  Selected expressions are
 * sites, which do not appear in forms.
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
  var nargs = rule.length;
  // Initialize the args array length to be the number of its
  // named arguments.
  var args = new Array(nargs);
  this.fillFromSelection(args);
  this.fillFromForm(args);
  if (this.checkArgs(args, rule.info.minArgs, true)) {
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
 * Fill in part of the args array with the step or step and path of
 * the UI's selection if there is one, using the input descriptor of
 * of the StepEditor's current rule.  Currently not picky about the
 * detailed requirements of the various kinds of site and step
 * arguments.  Relies on other components to do these checks.
 */
StepEditor.prototype.fillFromSelection = function(args) {
  var step = this.proofDisplay.selection;
  if (!step) {
    return;
  }
  var expr = step.selection;
  var rule = Toy.rules[this.ruleName];
  var inputs = rule.info.inputs;
  // Fill in args information from a selection.
  if (expr) {
    for (var type in siteTypes) {
      var input = inputs[type];
      if (input) {
        var position = Array.isArray(input) ? input[0] : input;
        args[position - 1] = step.original;
        args[position] = step.prettyPathTo(expr);
        // Only fill in one argument (pair) from the selection.
        break;
      }
    }
  } else {
    for (var type in stepTypes) {
      var input = inputs[type];
      if (input) {
        var position = Array.isArray(input) ? input[0] : input;
        args[position - 1] = step;
        // Only fill in one step.
        break;
      }
    }
  }
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
 * Policy-based rule offering policy function.  Returns a truthy value
 * iff current policy is to show the rule.
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
 * If the proof has a current selection, the rule is offerable if
 * acceptsSelection returns true given the selected step and rule
 * name.
 *
 * Otherwise only rules that take no step and no site are offerable.
 */
StepEditor.prototype.offerable = function(ruleName) {
  var info = Toy.rules[ruleName].info;
  if (!('form' in info)) {
    return false;
  }
  var step = this.proofDisplay.selection;
  if (step) {
    // Something is selected.  Check if the rule accepts the
    // selection.
    if (acceptsSelection(step, ruleName)) {
      // If the rule has a "toOffer" property, apply it as a further
      // test of offerability.
      var offerTest = info.toOffer;
      if (info.toOffer) {
        return offerTest(step, step.selection);
      }
      return true;
    }
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
   * currently all that are equational (equation, possibly with
   * conditions).
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
        Toy.eachFact(function(goal, synopsis) {
            if (goal.isEquation()) {
              var lhs = goal.eqnLeft();
              if (expr.matchSchema(lhs) &&
                  !(self.showRuleType == 'algebra' &&
                   // In simple algebra mode suppress facts with LHS
                   // of just a variable or constant.
                   lhs instanceof Toy.Atom)) {
                if (!typesMismatch(expr, lhs)) {
                  facts.push(goal);
                }
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
 * potentially shortened to "xiom".  Result is currently text, but may
 * become HTML in the future.  Called with a (rendered) step if there
 * is a selection, the selected term if a term is selected, and the
 * ProofEditor in which the menu is to exist.
 *
 * This is expected to return either a falsy value (including the
 * empty string), indicating the rule will not be offered, or a string
 * with the menu text, or an array of strings, indicating multiple
 * menu items for this rule with the possibly selected step and term.
 *
 * If there is a selected term, it can be formatted using {term} in
 * the rule's "menu" format string.
 */
function ruleMenuText(ruleName, step, term, proofEditor) {
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
    // If there are inputs uses info.menu or some fallback.
    var right = '?';
    if (term) {
      // Set up right neighbor info for rules.groupToRight.
      var pathToTerm = step.prettyPathTo(term);
      var parentPath = pathToTerm.upTo('/left') || pathToTerm.upTo('/left/right');
      if (parentPath) {
        var rightNeighbor = step.get(parentPath).getRight();
        right = rightNeighbor.toHtml();
      }
    }
    var formatArgs = {term: term && term.toHtml(), right: right};
    if (info.menu) {
      return Toy.format(info.menu, formatArgs);
    } else {
      return Toy.mathMarkup(info.basicTooltip || 'menu?');
    }
  }
}


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
 */
function RuleMenu(stepEditor) {
  var self = this;
  self.stepEditor = stepEditor;
  self._refresher = new Toy.Refresher(self.update.bind(self));
  self.length = 0;
  self.changed = false;

  // Rule chooser:
  self.$node = $('<div class=ruleMenu/>');

  self.$node.on('click', '.ruleItem', function(event) {
      // Run the step editor's ruleChosen method with
      // the ruleName of the menu item.
      self.stepEditor.ruleChosen($(this).data('ruleName'));
    });
}

/**
 * Call this any time this object's display might need to be updated.
 * The display update will occur when the event loop becomes idle.
 */
RuleMenu.prototype.refresh = function() {
  this.changed = true;
  this._refresher.activate();
}

/**
 * Fades the rule selector in (true) or out (false) based on the
 * argument.
 */
RuleMenu.prototype.fadeToggle = function(visible) {
  var $node = this.$node;
  if (visible) {
    $node.fadeIn(200);
  } else {
    // This fades out as the busy indicator fades in, so the duration
    // must be less than the fadeIn duration of the busy indicator;
    // otherwise completion of this will be delayed by running of the
    // actual rule.
    $node.fadeOut(0);
  }
};

/**
 * Return the RuleSelector to a "fresh" state, with no rule selected,
 * offered items reflecting the currently-selected step or term.
 */
RuleMenu.prototype.update = function() {
  var self = this;
  // Clear any message displays whenever this changes, as when
  // the user selects an expression or step.
  self.stepEditor.$proofErrors.hide();
  var $container = $('<div class=rulesContainer>');
  var $header = $('<div class=rulesHeader/>');
  $container.append($header);
  var step = this.stepEditor.proofDisplay.selection;
  var term = step && step.selection;
  // Map from rule display text to rule name.
  var byDisplay = {};
  var displayTexts = [];
  self.stepEditor.offerableRuleNames().forEach(function(name) {
      var ruleName = name.replace(/^xiom/, 'axiom');
      var text = ruleMenuText(ruleName, step, term,
                              self.stepEditor._proofEditor);
      if (Array.isArray(text)) {
        text.forEach(function(msg) {
            displayText.push(msg);
            byDisplay[msg] = ruleName;
          });
      } else if (text) {
        displayTexts.push(text);
        byDisplay[text] = ruleName;
      }
    });
  self.stepEditor.offerableFacts().forEach(function(statement) {
    var text = statement.toString();
    var toDisplay = statement;
    if (statement.isEquation()) {
      if (statement.isCall2('=>')) {
      // Make the statement be the fact's equation.
      toDisplay = statement = statement.getRight();
      }
      // If as usual the LHS of the equation matches the selection,
      // set toDisplay to the result of substituting into the RHS.
      var step = self.stepEditor.proofDisplay.selection;
      var selection = step && step.selection;
      if (selection) {
        var subst = selection.matchSchema(statement.getLeft());
        if (subst) {
          toDisplay = statement.getRight().subFree(subst);
        }
      }
    }
    var display = '= ' + toDisplay.toHtml();
    if (subst) {
      display += (' <span class=description>using ' +
                  Toy.trimParens(statement.toHtml())
                  + '</span>');
    }
    displayTexts.push(display);
    // Value of the option; format of "fact <fact text>"
    // indicates that the text defines a fact to use in
    // rules.rewrite.
    byDisplay[display] = 'fact ' + text;
  });
  displayTexts.sort(function(a, b) { return a.localeCompare(b); });
  var items = [];
  displayTexts.forEach(function(display) {
      var $item = $('<div class="ruleItem noselect"/>');
      $item.html(display);
      $item.data('ruleName', byDisplay[display]);
      items.push($item);
    });
  $container.append(items);
  self.length = items.length
  self.changed = false;
  // TODO: Generate smarter messages for rules that work without a UI
  //   selection (most theorems and theorem generators).
  $header.text(displayTexts.length
               ? 'Actions:'
               : (self.stepEditor.proofDisplay.selection
                  ? (self.stepEditor.showRuleType == 'algebra'
                     ? 'Try selecting the whole step or a numeric expression.'
                     : 'No actions available for the selection in this mode.')
                  : ('Select an expression with a click. ' +
                     'Checkbox selects the step.')));
  self.$node.fadeOut(0);
  self.$node.empty();
  self.$node.append($container);
  self.$node.fadeIn();
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

//// INITIALIZATION

// For testing:
Toy.autoSimplify = autoSimplify;

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
