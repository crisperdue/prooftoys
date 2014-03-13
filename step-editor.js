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
  self.$proofErrors.on('click', function() {
      // TODO: Don't hide on click in a step debugging display inside
      //   the error node.
      $(this).hide();
    });
}

/**
 * Marks this StepEditor as busy or not in the UI.
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
    $working.fadeOut(1000, complete);
  }
  this.ruleSelector.fadeToggle(!busy);
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
  $proofErrors.html('<button>X</button>');
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
 * not affect the rules offered.
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
  var ruleName = this.ruleSelector.ruleName;
  var action = Toy.rules[ruleName];
  // In some cases the action is generated from the test and
  // in these cases only the test has the correct number of
  // arguments in its argument list.
  var nargs = (action.info.test || action).length;
  // Initialize the args array length to be the number of its
  // named arguments.
  var args = new Array(nargs);
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
  if (args.length != nargs) {
    Toy.logError('Rule received unnamed arguments: ' + ruleName);
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
  tryRuleAsync(this, action, args);
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

    // Applies the rule here.
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
        var simplified = Toy.rules.simplifyStep(result);
        self._setBusy(false);
        if (simplified && !simplified.rendering) {
          self.proofControl.addStep(simplified);
          checkSolution(simplified);
        } else {
          checkSolution(result);
        }
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
 *
 * When parsing a term, simplifies the error message, but keeps
 * the original parsing error as the "cause" property of the
 * thrown error.
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
    if (Toy.findType(expr) != Toy.boolean) {
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
  // This test is really just for algebra mode.
  if (!this.selectionApprovedForMode()) {
    return false;
  }
  switch (this.showRuleType) {
  case 'all':
    return true;
  case 'algebra':
    return labels.algebra || labels.display;
  case 'general':
    return labels.basic || labels.display || labels.algebra;
  default:
    throw new Error('Bad rule policy value: ' + this.showRuleType);
  }
};

/**
 * In algebra mode, if there is a selected term, this only returns
 * true if the term is numeric (type real).  Otherwise true.
 */
StepEditor.prototype.selectionApprovedForMode = function() {
  if (this.showRuleType != 'algebra') {
    return true;
  }
  var step = this.proofControl.selection;
  if (step) {
    var expr = step.selection;
    if (expr) {
      // The step is rendered, so OK to annotate.
      step.annotateWithTypes();
      return expr.isReal();
    }
  }
  return true;
}

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
      // First check that the rule accepts this type of selection,
      // now if there is a test, check that the custom test passes.
      // This way the test can assume for example that there is a
      // selected term.
      var offerTest = info.toOffer;
      if (info.toOffer) {
        return info.toOffer(step, step.selection);
      }
      if (info.test) {
        return info.test(step, step.locate(step.selection));
      }
      return true;
    }
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
    if (!this.selectionApprovedForMode()) {
      return facts;
    }
    if (step) {
      var expr = step.selection;
      if (expr) {
        Toy.eachFact(function(fact) {
            var goal = fact.goal;
            if (goal.isEquation()) {
              var lhs = goal.eqnLeft();
              if (!(lhs instanceof Toy.Atom) && expr.matchSchema(lhs)) {
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
             || (argInfo.implication && step.unHyp().isCall2('==>'))));
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
    var right = '?';
    if (term) {
      // Set up right neighbor info for rules.groupToRight.
      var pathToTerm = step.prettyPathTo(term);
      var parentPath = pathToTerm.upTo('/left') || pathToTerm.upTo('/left/right');
      if (parentPath) {
        var rightNeighbor = step.locate(parentPath).getRight();
        right = rightNeighbor.toUnicode();
      }
    }
    var formatArgs = {term: term && term.toUnicode(), right: right};
    return Toy.unicodify((info.menu &&
                          Toy.format(info.menu, formatArgs)) ||
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
    $node.toggleClass('hidden', false);
    $node.fadeTo(100, 1);
  } else {
    // This fades out as the busy indicator fades in, so the duration
    // must be less than the fadeIn duration of the busy indicator;
    // otherwise completion of this will be delayed by running of the
    // actual rule.
    $node.fadeTo(0, 0, function() { $node.toggleClass('hidden', true); });
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
  self.stepEditor.offerableFacts().forEach(function(fact) {
    var statement = Toy.getStatement(fact);
    var text = statement.toString();
    var toDisplay = statement;
    if (statement.isEquation() && statement.isCall2('==>')) {
      // Make the statement be the fact's equation.
      toDisplay = statement = statement.getRight();
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
    var display = '= ' + toDisplay.toUnicode();
    if (subst) {
      display += (' <span class=description>using ' +
                  Toy.trimParens(statement.toUnicode())
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
      $item.html(display);
      $item.data('ruleName', byDisplay[display]);
      self.$node.append($item);
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

// Global variable, name to use for CPU profiles, or falsy to disable:
Toy.profileName = '';

Toy.stepTypes = stepTypes;
Toy.siteTypes = siteTypes;

Toy.StepEditor = StepEditor;

Toy.tryRuleAsync = tryRuleAsync;

})();
