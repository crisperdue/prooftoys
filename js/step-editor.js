// Copyright 2011, 2012, 2013, 2014, 2015 Crispin Perdue.
// All rights reserved.

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
 * solutions: If any of these expressions (or strings) is an alphaMatch
 *   with a step, announce the step as a solution.
 * standardSolution: If no explicit solutions given, but the result of
 *   a step solves for a variable (equal to a numeral or fraction),
 *   announce that the problem is solved.
 *
 * showRuleType: Selects type of rules to show, as determined by offerApproved.
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
  self.solutions = [];
  self.standardSolution = false;

  // Create a DIV with the step editor content.
  var div = $('<div class=stepEditor style="clear: both"></div>');
  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<input class=sted-clear type=button value=x title="Clear the input">');
  self.clearer.addClass('hidden');
  div.append(self.clearer);
  self.form = $('<span class=sted-form></span>');
  div.append(self.form);
  // Proof errors display.
  self.$proofErrors = $('<div class="proofErrors hidden"></div>');
  div.append(self.$proofErrors);
  self.$node = div;

  self.showRules = [];

  // Attach the "ruleWorking" to the ProofControl node so
  // it doesn't move when steps are inserted.
  $(self.proofControl.node)
    .append($('<div class=ruleWorking/>').text('Working . . . '));
  var widget = new BasicRuleSelector(self);
  self.ruleSelector = widget;
  div.append(widget.$node);
             
  self.showRuleType = 'general';
  // Let the constructor and initialization code all run before
  // triggering the change action.
  Toy.soonDo(function() { controller.setRulesMode(self.showRuleType); });

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
  var $working = $(this.proofControl.node).find('.ruleWorking');
  if (busy) {
    // Temporarily turn on display of ruleSelector to get its offset.
    this.ruleSelector.$node.toggle(true);
    var offset = this.ruleSelector.$node.offset();
    this.ruleSelector.$node.toggle(false);
    // and similarly for $working to set its offset.
    $working.toggle(true);
    $working.offset({left: offset.left + 40, top: offset.top + 5});
    // Then  turn it off and fade it back in.
    $working.toggle(false).fadeIn(200, complete);
  } else {
    $working.fadeOut(200, complete);
  }
  this.ruleSelector.fadeToggle(!busy);
  // Clear the form.
  // TODO: Make these actions into a function/method, see "reset".
  this.clearer.addClass('hidden');
  this.form.html('');
  this.proofControl.setSelectLock(false);
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
  this.proofControl.setSelectLock(false);
  this._setBusy(false);
  this.ruleSelector.fadeToggle(true);
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
StepEditor.prototype.ruleChosen = function() {
  var value = this.ruleSelector.ruleName;
  var rule = Toy.rules[value];
  if (rule) {
    // TODO: Only show the form if there are arguments that need to be
    //   filled from it.  Instead of calling tryExecuteRule(false),
    //   check here if all args can be filled from the selection
    //   and modify that to always report errors.
    var template = rule.info.form;
    if (template) {
      this.ruleSelector.fadeToggle(false);
      // Template is not empty.  (If there is no template at all, the
      // rule will not be "offerable" and thus not selected.)
      this.clearer.removeClass('hidden');
      this.form.html(template);
      this.proofControl.setSelectLock(true);
      this.form.append('<button>Go</button>');
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
    // the desired fact is indicated by the rest of the value.
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
 * Fill in arguments for the rule named by the ruleSelector from the
 * current selection and the rule's input form, and if successful set
 * up actual execution and redisplay to occur after the UI has
 * opportunity to repaint.  Throws in case of failure if reportFailure
 * is true.
 */
StepEditor.prototype.tryExecuteRule = function(reportFailure) {
  // TODO: Get it together on failure reporting here.
  var ruleName = this.ruleSelector.ruleName;
  var rule = Toy.rules[ruleName];
  var nargs = rule.length;
  // Initialize the args array length to be the number of its
  // named arguments.
  var args = new Array(nargs);
  this.prefillArgs(args);
  try {
    this.fillFromForm(args);
  } catch(error) {
    // The form is not ready, fail.
    if (reportFailure) {
      this.error(error.message);
    }
    return;
  }
  if (args.length != nargs) {
    Toy.logError('Rule received unnamed arguments: ' + ruleName);
  }
  // Check that the args are all filled in.
  var required = (rule.info.hasOwnProperty('minArgs')
                  ? rule.info.minArgs
                  : args.length);
  for (var i = 0; i < required; i++) {
    if (args[i] === undefined) {
      if (reportFailure) {
	this.error('Undefined argument ' + i);
      }
      return;
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
  tryRuleAsync(this, rule, args);
};

/**
 * Turns on the editor's busy indicator and sets the rule up to run
 * with the given aras as soon as the UI has opportunity to repaint.
 */
function tryRuleAsync(stepEditor, rule, args) {
  args.forEach(function(arg) {
      if (Toy.isStep(arg) && arg.isRendered()) {
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
    this.$proofErrors.hide();
    // After the browser repaints, try simplifying the step
    // and adding the result to the proof if simplification
    // has any effect.
    var self = this;
    function checkSolution(result) {
      var message = self.isSolution(result);
      if (message) {
        self.report(message);
      }
    }
    Toy.afterRepaint(function() {
        var trial = autoSimplify(result);
        // If autoSimplify is a no-op, do not display the result.
        var simplified = (trial.sameAs(result)
                          ? result
                          : trial);
        self._setBusy(false);
        var steps = Toy.unrenderedDeps(simplified);
        steps.forEach(function(step) {
            self.proofControl.addStep(step);
          });
        checkSolution(simplified);
      });
  }
  this.focus();
};

/**
 * If this.solutions is nonempty, returns a solution message iff the
 * step or its "main part" is an alphaMatch with some element of it.
 * 
 * If this.standardSolution is truthy, this returns a truthy value iff
 * the given step is an equation of the form <var> = <expr>, where
 * <expr> is a numeral or a fraction.
 */
StepEditor.prototype.isSolution = function(step) {
  if (this.solutions.length) {
    return Toy.each(this.solutions, function(solution) {
        if (Toy.termify(solution).alphaMatch(step) ||
            Toy.termify(solution).alphaMatch(step.getMain())) {
          return true;
        }
      }) && 'This is a valid solution';
  } else if (this.standardSolution &&
             step.isEquation() &&
             step.getMain().getLeft().isVariable()) {
    var rhs = step.getMain().getRight();
    return ((rhs.isNumeral() ||
             (rhs.isCall2('/') &&
              rhs.getLeft().isNumeral() &&
              rhs.getRight().isNumeral()))
            && 'You have solved for ' + step.getMain().getLeft().name);
  } else {
    return false;
  }
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
  return this.proofControl.steps.length + 1;
};

StepEditor.prototype.genAbbrevName = function() {
  return '$' + this.slotIndex();
};

/**
 * Fill in part of the array argument with the step and path of the
 * UI's selected site if there is one, based on the name of the rule
 * selected in the ruleSelector.  Reports an error to the user if
 * preconditions are not met.
 */
StepEditor.prototype.prefillArgs = function(args) {
  var rule = Toy.rules[this.ruleSelector.ruleName];
  var inputs = rule.info.inputs;

  // Fill in site information from a selected expression.
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
    if (!value.match(/^\d+$/)) {
      throw new Error('Not a step number: ' + value);
    }
    var index = Number(value) - 1;
    if (index < 0 || index >= this.proofControl.steps.length) {
      throw new Error('No such step: ' + value);
    }
    return this.proofControl.steps[Number(value) - 1].original;
  case 'bool':
    var expr = Toy.parse(value);
    var type = Toy.findType(expr);
    if (!(type === Toy.boolean || type instanceof Toy.TypeVariable)) {
      // Since variables do not have known types, some expressions may
      // have unknown types, and we allow that here.
      throw new Error('Not a true/false expression:' + value);
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
  var step = this.proofControl.selection;
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
    var step = this.proofControl.selection;
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
 * potentially shortened to "xiom".  Result is currently text,
 * but may become HTML in the future.
 *
 * If given, the term argument should be a term to format using
 * {term} in the rule's "menu" format string.
 */
function ruleMenuText(ruleName, term, step) {
  ruleName = ruleName.replace(/^xiom/, 'axiom');
  var info = Toy.rules[ruleName].info;
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
      return Toy.mathMarkup(info.comment || 'menu?');
    }
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

  self.$node.on('click', '.ruleItem', function(event) {
    var ruleName = $(this).data('ruleName');
    self.ruleName = ruleName;
    self.stepEditor.ruleChosen();
  });
}

BasicRuleSelector.prototype.refresh = function() {
  this._refresher.activate();
}

/**
 * Fades the rule selector in (true) or out (false) based on the
 * argument.  In all cases the selector continues to occupy space in
 * the document.  (This avoids jumping scrollbars or possibly even the
 * document itself jumping around.)
 */
BasicRuleSelector.prototype.fadeToggle = function(visible) {
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
 * offered items compatible the currently-selected step or term.
 */
BasicRuleSelector.prototype.update = function() {
  var self = this;
  self.$node.fadeOut(0);
  self.$node.empty();
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
      var text = ruleMenuText(ruleName, term, step);
      displayTexts.push(text);
      byDisplay[text] = ruleName;
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
      var step = self.stepEditor.proofControl.selection;
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
    // rewriteWithFact.
    byDisplay[display] = 'fact ' + text;
  });
  displayTexts.sort(function(a, b) { return a.localeCompare(b); });
  displayTexts.forEach(function(display) {
      var $item = $('<div class="ruleItem noselect"/>');
      self.$node.append($item);
      $item.html(display);
      $item.data('ruleName', byDisplay[display]);
    });
  self.ruleName = '';
  // TODO: Generate smarter messages for rules that work without a UI
  //   selection (most theorems and theorem generators).
  $header.text(displayTexts.length
               ? 'Actions:'
               : (self.stepEditor.proofControl.selection
                  ? (self.stepEditor.showRuleType == 'algebra'
                     ? 'Try selecting the whole step or a numeric expression.'
                     : 'No actions available for the selection in this mode.')
                  : ('Select an expression with a click. ' +
                     'Checkbox selects the step.')));
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
