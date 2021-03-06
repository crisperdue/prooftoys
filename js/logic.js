// Copyright Crispin Perdue.  All rights reserved.
//
// Definitions and theorems of pure logic

+function() {

'use strict';


//// Import names

const assert = Toy.assertTrue;
const abort = Toy.abort;
const assertEqn = Toy.assertEqn;
const newError = Toy.newError;

const varify = Toy.varify;
const constify = Toy.constify;
const termify = Toy.termify;
const mathParse = Toy.mathParse;
const call = Toy.call;
const equal = Toy.equal;
const implies = Toy.implies;
const lambda = Toy.lambda;

const Expr = Toy.Expr;
const Atom = Toy.Atom;
const Call = Toy.Call;
const Lambda = Toy.Lambda;

const definition = Toy.definition;

// The book definition of F is just fine, and can be presented either
// as a definition or as an ordinary fact.  But by taking [T != F] and
// [F != T] as axioms we could skip some technical development and
// omit the book definition entirely.  This constant could be turned
// into a flag to toggle between use of the definition and use of the
// two extra axioms.
const useFalseDefn = true;

const identity = Toy.parse('{x. x}');
const allT = Toy.parse('{x. T}');

const rules = Toy.rules;
const declare = Toy.declare;
const buildHypSchema = Toy.buildHypSchema;
const tryReduce = Toy.tryReduce;

const noSimplify = Toy.noSimplify;

const resolveToFactInfo = Toy.resolveToFactInfo;
const basicSimpFacts = Toy.basicSimpFacts;
const _tautologies = Toy._tautologies;

const T = constify('T');
const F = constify('F');

// Caches (details of) results of rules.fact that are given a string
// as input, for performance of functions such as findMatchingFact.
// Used in rules.fact to quickly get the proof of a fact given as a
// string.  Not to be confused with _factsMap, which contains
// information about facts as they are stated, not as they are looked
// up.  The values are Step objects.  Private to rules.fact.
//
// TODO: Consider removing this or upgrading it to a Map.
const _factMap = {};


//// Primitive constants

Toy.namedConstants.add('=');
Toy.namedConstants.add('==');
Toy.namedConstants.add('the1');
Toy.namedConstants.add('T');
// Toy.namedConstants.add('F');


//// Definitions

definition('forall = (=) {x. T}');
// Note that if the truth table for == is given as an axiom,
// F need not be defined.
definition('F == forall {x. x}');
definition('not = (=) F');
definition('(!=) = {x. {y. not (x = y)}}');
definition('exists = {p. p != {x. F}}');
definition('exists1 = {p. exists {x. p = {y. y = x}}}');

// Adding definitions before use enables type checking to use the
// known types of the constants.

// It would be desirable for the constants in this next group to
// all have generic types.
// definition('if = {p. {x. {y. the1 {z. p & z = x | not p & z = y}}}}');

declare(
  {statement: 'if T x y = x', axiom: true,
   simplifier: true},
  {statement: 'if F x y = y', axiom: true,
   simplifier: true}
);

// We will derive the T/F cases facts after defining some inference rules.
definition('(&) = {x. {y. if x y F}}');
definition('(|) = {x. {y. if x T y}}');
definition('(=>) = {x. {y. if x y T}}');

definition('empty = {x. F}');
definition('none = the1 empty');
definition('(?) = {p. {x. if p x none}}');

// The identity function
definition('ident = {x. x}');

// Collection has multiple elements:
definition('multi = {p. exists {x. exists {y. p x & p y & x != y}}}');

// Always either "none" or the member of the singleton set:
definition('the = {p. if (exists1 p) (the1 p) none}');

// This "negates" a predicate, returning a predicate whose value
// is the negation of the value of the given predicate.  (Just one
// argument!)
definition('negate = {p. {x. not (p x)}}');

// Strictness
definition('strict = {f. f none = none}');
definition('strict2 = {f. forall {x. f x none = none} & ' +
           'forall {x. f none x = none}}');


//// FACTS AND RULES

// Conventions for menu items (using "menu:")
// Step templates are in square brackets, such as [T = A].
// Rules (including axiom 4) that take a term as input use A, B to
//   show where the term goes, not enclosed in square brackets.

//// Logical axioms and rule of inference

declare(
  // TODO: LOGIC: Consider the possibility of instead saying that
  //     p T & p F => p x
  //   and defining forall:bool->bool as {p. p T & p F}.
  //   Most uses of axiom1 are immediately followed by instEqn, and
  //   use the definition of forall:bool->bool.
  //   We could prove that any two boolean functions with the same
  //   definition by cases are equal.  This still assumes that
  //   definition by cases is at least admissible.  (There exists
  //   a function as defined.)
  {name: 'axiom1',
    statement: 'g T & g F == forall {a. g a}', axiom: true,
    inputs: {},
    description: 'axiom of T & F',
    tooltip: ('T and F are all the booleans')
  },

  {name: 'axiom2',
    statement: 'x = y => h x = h y', axiom: true,
    inputs: {},
    description: 'axiom of function application',
    tooltip: ('functions take equal values to equal values')
  },

  /**
   * Axiom 2 specialized for predicates.  This is actually more like
   * Andrews' axiom 2.
   */
  {name: 'axiom2a',
    statement: 'x = y => (p x == p y)', axiom: true,
    proof: function() {
      var step1 = rules.instVar(rules.axiom2(), 'p', 'h');
      var step2 = rules.eqIsEquiv();
      var result = rules.r1(step1, '/right/binop', step2);
      return result;
    },
    inputs: {},
    description: 'axiom of predicate application',
    tooltip: ('predicates take equal values to the same truth value')
  },

  {name: 'axiom3',
    statement: '(f = g) == forall {x. f x = g x}', axiom: true,
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    inputs: {},
    tooltip: ('extensionality: functions are equal based on equal results'
              + ' on all inputs.'),
    description: 'axiom of equal functions'
  },

  {name: 'axiom3a',
    statement: '(p = q) == forall {x. p x == q x}', axiom: true,
    proof: function() {
      const map = {f: 'p', g: 'q'};
      const step1 = rules.instMultiVars(rules.axiom3(), map);
      const step2 = rules.eqIsEquiv();
      const result = rules.r1(step1, '/right/arg/body/binop', step2);
      return result.justify('axiom3a', []);
    },
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    inputs: {},
    tooltip: ('extensionality: predicates are equal ' +
              'based on equal membership.'),
    description: 'axiom of equal predicates'
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction,
   * in other words, a substitution.
   */
  {name: 'axiom4',
    action: function(call_arg) {
      const call1 = (typeof call_arg == 'string'
                     ? Toy.parse(call_arg)
                     : call_arg);
      assert(call1.isLambdaCall(),
             'Axiom 4 needs ({v. B} A), got: {1}', call_arg);
      // TODO: Consider requiring type info to be present.
      const call = (call1.hasType()
                    ? call1
                    : call1.copyForTyping().annotateWithTypes());
      var lambda = call.fn;
      const result =
            equal(call, lambda.body.subFree1(call.arg, lambda.bound.name));
      // Carefully install type information by hand.
      result.arg._type = result.fn.arg._type = call._type;
      result.fn._type = new Toy.FunctionType(call._type, Toy.boolean);
      result.fn.fn._type = Toy.equalityType(call._type);
      result._type = Toy.boolean;
      const badex = result.search(x => !x._type);
      assert(!badex,
             'Axiom4 result on {1} has untyped {2}', call_arg, badex);
      return result.justify('axiom4', [call]);
    },
    labels: 'primitive',
    inputs: {term: 1},  // Specifically a Call to a Lambda.
    form: 'Enter {v. body} expr <input name=term>',
    menu: 'apply a lambda to its argument',
    description: 'function call substitution axiom',
    tooltip: ('')
  },

  {name: 'axiom5',
    // Traditionally (upside-down) iota, as in Andrews' text.
    statement: 'the1 {x. x = y} = y', axiom: true,
    simplifier: true,
    inputs: {},
    tooltip: ('axiom of description'),
    description: 'axiom of description'
  },

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R.  The subexpression must match
   * the equation's LHS, meaning they are the same except possibly
   * in names of bound variables.
   *
   * If either the target or the equation are Error objects,
   * returns a LogicError.
   */
  {name: 'r',
    action: function(equation, target, path_arg) {
      if ((equation instanceof Error || target instanceof Error) &&
          !Toy.autoAssert) {
        return Toy.logicError('Not proved');
      }
      const path = target.asPath(path_arg);
      assert(equation.isCall2('='), 'Rule R requires equation: {1}', equation);
      // Logs the location of the test where autoAssert is used.
      function logWhere(term) {
        var e = new Error();
        var lines = e.stack.split('\n');
        // Note that the following regex may be Chrome-specific.
        function test(line) { return line.match(/Object.test/); }
        var where = lines.find(test) || 'at unknown location';
        console.warn('Asserting', term.$$, where);
      }
      // Auto-justify input steps if requested by the current configuration.
      if (!equation.isProved()) {
        if (Toy.autoAssert) {
          logWhere(equation);
          equation = rules.assert(equation);
        } else {
          assert(false, 'Rule R unproven equation: {1}', equation);
        }
      }
      if (!target.isProved()) {
        if (Toy.autoAssert) {
          logWhere(target);
          target = rules.assert(target);
        } else {
          assert(false, 'Rule R unproven target: {1}', target);
        }
      }
      if (!target._type) {
        console.warn(Toy.format('Target lacks type: {1}', target));
        debugger;
      }
      if (!equation._type) {
        console.warn(Toy.format('Equation lacks type: {1}', equation));
        debugger;
      }
      let result;
      const targex = target.get(path);
      const badTarg = target.wff.search(x => !x._type);
      const badEqn = equation.wff.search(x => !x._type);
      if (badTarg || badEqn) {
        debugger;
      }

      // TODO: Instead, check that they have identical term types,
      //   with no type variables in them.
      const targHas = target.wff.search(x => x._type.hasVariable());
      const eqnHas = equation.wff.search(x => {
          return x._type.hasVariable();
        });
      if (!targHas && !eqnHas) {
        // Make a copy with the eqn RHS replacing the target term.
        // Carry over (constant) types of all terms being copied.
        const replace = (x, pth) => {
          if (pth && pth.isMatch()) {
            // Include the equation RHS as-is.
            return equation.getRight();
          }
          const c = x.constructor;
          const seg = pth && pth.segment;
          const rest = pth && pth.rest;
          if (c === Atom) {
            const v = new Atom(x.pname);
            v._type = x._type;
            return v;
          } else if (c === Call) {
            const v = new Call(replace(x.fn, seg === 'fn' && rest),
                               replace(x.arg, seg === 'arg' && rest));
            v._type = x._type;
            return v;
          } else if (c === Lambda) {
            const rest = pth.rest;
            const v = new Lambda(replace(x.bound, null),
                                 replace(x.body, seg === 'body' && rest));
            v._type = x._type;
            return v;
          }
        }
        const ugPath = path.uglify(true);
        result = replace(target.wff, ugPath);
        const failure = result.typeCheck();
        if (failure) {
          console.warn('typeCheck failure');
          debugger;
          result.typeCheck();
        }
        assert(!failure, 'Typecheck failure in {1} at {2}', result, failure);
      } else {
        const eq2 = equation.distinctify(target);
        const unifier = eq2.getLeft().typesUnifier(targex);
        assert(unifier,
               'Rule R: subexpression {1}\n of {2}\n must match {3}',
               targex, target, equation.getLeft());
        const eq2r = eq2.getRight().subsType(unifier);
        const target2 = target.subsType(unifier);
        // The unifier makes the targex and the LHS exactly the same,
        // but we may need to unify types of free variables in the LHS
        // that are "captured" in a way by like-named target variables
        // that are in scope at the replacement site.
        // We can find those with boundNames and I guess freeVarSet
        // ("freeVarTypes"?).
        // We extend the unification pairs with their types
        // before doing any type substitutions.
        //
        // Can we check the assignments with a Hindley-Milner
        // "dry run" over the formulas?
        const result1 = target2.replaceAt(path, expr => eq2r);
        // Does this always exist?
        //
        // This is guaranteed most general, but it ignores
        // the type assignments done before!  We could check
        // that the "real" computed result is a substitution
        // instance of this.
        result = result1.copyForTyping().annotateWithTypes();
      }
      var justified = result.justify('r', [equation, target, path],
                                     [target, equation], true);
      justified.details = null;
      return justified;
    },
    inputs: {equation: 1, site: 2},
    // Currently not offered in forms; use "replace".
    // form: ('Replace with right side of step <input name=equation>'),
    tooltip: ('Replace an occurrence of a term with an equal term.'),
    menu: 'replace {term} with something equal',
    description: 'replace term;; {in step siteStep} {using step equation}',
    labels: 'uncommon'
  },

  /* Rule R with arguments in the standard order; currently inline. */
  {name: 'r1',
    action: function(target, path, equation) {
      return rules.r(equation, target, path);
    }
  }

);


//// Preliminaries to logic

declare(
  /**
   * The name "assertion" is used in displays to indicate that the
   * result of the inference is asserted without proof.  If given a
   * string, parses it and uses the result as its input.
   */
  {name: 'assert',
    action: function(assertion_arg) {
      const assertion = termify(assertion_arg).copyForTyping();
      assertion.annotateWithTypes();
      const newConsts = assertion.newConstants();
      if (newConsts.size > 0) {
        console.warn('In', assertion.toString(), 'introducing constants:',
                     Array.from(newConsts).join(', '));
        Toy.addConstants(newConsts);
      }
      return assertion.justify('assert', [assertion]);
    },
    inputs: {bool: 1},
    form: ('Assert <input name=bool>'),
    menu: 'assert without proof',
    labels: 'advanced',
    description: 'assert',
    tooltip: 'WFF to assert (possibly to prove later)'
  },

  {name: 'define',
    action: function(definition) {
      const name = Toy.definition(definition);
      const defn = rules.definition(name);
      return defn.justify('define', [definition]);
    },
    inputs: {term: 1},
    form: ('Enter definition <input name=term> (persists until page reload)'),
    menu: 'define a name',
    // TODO: Consider offering to define a name for the selected term
    //   if circumstances are appropriate.
    // Currently does not offer to define a name if there is any
    // selection.
    toOffer: 'return step == null',
    description: 'definition',
    tooltip: 'define a name'
  },

  {name: 'copy',
   action: function(step) {
     // Always make a new step, that is the point.
     return step.justify('copy', arguments, [step], true);
   },
   inputs: {step: 1},
   menu: 'copy step',
   description: 'copy;; {of step step}'
  },

  /**
   * A no-op step that breaks the cycle of displaying with elision.
   */
  {name: 'display',
    action: function(step) {
      // Force "justify" to not ignore this step.
      return step.justify('display', arguments, [step], true);
    },
    autoSimplify: noSimplify,
    inputs: {step: 1},
    form: ('Does nothing, but result will display in full. '
           + '<input name=step>'),
    menu: 'display in full',
    tooltip: 'display fully',
    description: 'display fully;; {step step}',
    labels: 'display basic'
  },
      
  // TODO: Consider making this a command rather than a rule,
  //   available through the rule menu when a step is selected.
  // TODO: Modify this to encode the steps to be inlined before
  //   committing to the inlining, and if encoding fails, abort the
  //   inlining.
  {name: 'inline',
    // Caution: this rule can ONLY be used on a step that has a rendering.
    action: function(step) {
      const inlined = step;
      const rendered = step.rendering;
      assert(rendered, 'For interactive use only');
      const display = Toy.getProofDisplay(rendered);

      Toy.fillDetails(rendered);
      const insertions = Toy.unrenderedDeps(step.details);
      // Steps with an array (list of facts) where some entry is
      // neither a term nor a string cannot currently be inlined.
      const noEncode = insertions.some(function(step) {
          return step.ruleArgs.some(function(arg) {
              return (Array.isArray(arg) &&
                      arg.some(function(fact) {
                          return (!(typeof fact === 'string') &&
                                  !(fact instanceof Expr));
                        }));
            });
        });
      if (noEncode) {
        throw new Error('Inlining not supported for ' + step.toString());
      }

      const steps = display.steps;
      const index = steps.indexOf(rendered);
      // These steps will be replaced with near-duplicates.
      const replaced = (steps.slice(index)
                        .map(function(step) { return step.original; }));
      display.removeStepAndFollowing(rendered);
      insertions.forEach(function(step) { display.addStep(step); });

      // Re-create the replaced steps except the first from their rule
      // info, replacing occurrences of replaced steps in their
      // arguments with the conclusion of the inline proof.
      const fixups = new Map();
      fixups.set(step, insertions[insertions.length - 1]);
      function rerun(step, index) {
        // The inlined (first) step is already replaced by the last insertion
        if (index > 0) {
          const args2 = step.ruleArgs.map(function(arg) {
              return fixups.get(arg) || arg;
            });
          const replacement = rules[step.ruleName].apply(rules, args2);
          display.addStep(replacement);
          fixups.set(step, replacement);
        }
      }
      replaced.forEach(rerun);
      // Do not return a step, but make the step editor accept the
      // result as a success.
      return true;
    },
    autoSimplify: noSimplify,
    inputs: {step: 1},
    menu: 'make inline',
    tooltip: 'make inline',
    // Rare property, indicates that this has side effects, so do
    // not run the rule to find a suggested step.
    noSuggest: true,
    labels: 'display'
  },

  // This is another high-level function that edits a proof.  This
  // supports replacing the derivation of a step in the proof with a
  // different derivation.  Selecting a step that is the same as (a
  // new) one at the end of the proof display enables this command,
  // which replaces all steps in the proof derived from the selected
  // one with identical steps derived from its twin.  No proof steps
  // are modified; they are only replaced with counterparts.
  //
  // This inserts the replacement steps at the end of the proof.
  {name: 'replaceStep',
    precheck: function(step) {
      const rendered = step.rendering;
      const last = Toy.getProofDisplay(rendered).getLastStep();
      if (last == rendered || !last.matches(rendered)) {
        // The last step must match the selected one, but must
        // be a different step.
        return false;
      }
      const derived = rendered.descendants();
      // The last step cannot be derived from the selected one.
      return derived.has(last) ? null : derived;
    },
    action: function(step) {
      const derived = Toy._actionInfo;
      const rendered = step.rendering;
      const display = Toy.getProofDisplay(rendered);
      // This is the step to use as a replacement.
      const alt = display.getLastStep().original;
      const dSteps = display.steps; 
      const index = dSteps.indexOf(rendered);
      assert(index >= 0, 'Step {1} not found', step);
      const fixups = new Map();
      fixups.set(step, alt);
      // This will have originals of the steps to be retained in the proof.
      const oldSteps = [];
      // This will have the real steps to replace ones derived from
      // the replaced step.
      const newSteps = [];
      for (let i = index; i < dSteps.length; i++) {
        const d = dSteps[i];
        if (derived.has(d)) {
          // Step d is derived from the replaced step, so re-run the
          // rule that made it, replacing input step(s) as needed
          // using the fixups Map.
          const s = d.original;
          const args2 = s.ruleArgs.map(function(arg) {
              return fixups.get(arg) || arg;
            });
          const replacement = rules[s.ruleName].apply(rules, args2);
          newSteps.push(replacement);
          fixups.set(s, replacement);
        } else {
          oldSteps.push(d.original);
        }
      }
      display.removeStepAndFollowing(rendered);
      oldSteps.concat(newSteps).forEach(function(s) { display.addStep(s); });
      return true;
    },
    noSuggest: true,
    autoSimplify: noSimplify,
    inputs: {step: 1},
    menu: 'derive consequences from alternate step',
    tooltip: 'derive consequences from alternate step',
    // Rare property, indicates that this has side effects, so do
    // not run the rule to find a suggested step.
    noSuggest: true,
    labels: 'display'
  },

  // Removes the selected step and any following steps from the proof.
  // Prompts before actually removing.
  {name: 'removeFromHere',
    precheck: function(step) {
      const rendered = step.rendering;
      const last = Toy.getProofDisplay(rendered).getLastStep();
      return rendered != last;
    },
    action: function(step) {
      if (window.confirm('Remove selected step and all following?')) {
        const rendered = step.rendering;
        const display = Toy.getProofDisplay(rendered);
        display.removeStepAndFollowing(rendered);
      }
      return true;
    },
    noSuggest: true,
    autoSimplify: noSimplify,
    inputs: {step: 1},
    menu: 'remove step and all following',
    // Rare property, indicates that this has side effects, so do
    // not run the rule to find a suggested step.
    noSuggest: true,
    labels: 'display'
  },

  /**
   * Refer to a theorem by name, for the UI.  Inline.
   *
   * TODO: Consider adding a rule that takes a ruleName as an
   *   argument, also for the UI.
   */
  {name: 'theorem',
    action: function(name) {
      if (!rules[name]) {
        return newError('No theorem named {1}', name);
      }
      if (!(rules[name].length == 0)) {
        return newError('Rule needs argument(s): {1}', name);
      }
      return rules[name]();
    },
    inputs: {string: 1},
    form: ('Look up theorem named <input name=string>'),
    menu: 'look up a theorem by name',
    tooltip: (''),
    description: 'theorem',
    labels: 'basic'
  },

  // Add a new named theorem to the rules.
  //
  // TODO: This and a few other commands change system state, and
  //   similarly changes to the set of supporing "theory" files.  So
  //   in some cases a page reload may be needed to refresh the state.
  //   We may want to annotate commands that change state, and track
  //   changes that can desynchronize the state.
  {name: 'addTheorem',
   action: function(step, name) {
     if (rules[name]) {
       return newError('Theorem {1} already exists', name);
     }
     const info = {
       name: name,
       statement: '@' + step.wff.toString(),
       proof: function() {
         return step;
       },
       description: 'theorem ' + name
     };
     Toy.addRule(info);
     return step.justify('addTheorem', arguments, [step], true);
   },
   inputs: {step: 1, string: 2},
   form: ('Add theorem named <input name=string>'),
   menu: 'as a named theorem (experimental)',
   description: 'proved "{string}";; {in step step}',
   labels: 'advanced'
  },

  /**
   * Refer to a definition in the definitions database.  Returns null
   * if no definition is found.
   *
   * Like rules.assert, this creates a proved step that has no
   * details.
   *
   * Note: Going forward we should probably expect at least
   * interactive users to use the "consider" rule followed by use of
   * the core definition fact.  That approach would also give access
   * to the traditional "forall" form as well as substitution
   * instances of definitions.
   */
  {name: 'definition',
    action: function(name) {
      // The derivations are computed in advance, and have the name as
      // the argument.
      const defn = Toy.findDefinition(name);
      return defn && defn.justify('definition', [name]);
    },
    inputs: {string: 1},
    labels: 'advanced',
    form: ('Definition of <input name=string>'),
    menu: 'look up a definition',
    tooltip: 'look up a definition',
    description: '=definition'
  },

  /**
   * Converts an equality of two functions / predicates into equality
   * of the result of applying each to a variable, as for converting
   * a function definition to the traditional form [f x = ... ].
   *
   * TODO: Consider obsoleting this rule when Axiom 3 becomes
   *   available to use as a rewrite in the UI.  Further consider
   *   obsoleting this if unForall or similar rule removes forall from
   *   deeper subexpressions (that do not involve ==).
   */
  {name: 'reduceEqn',
    action: function(equation) {
      assertEqn(equation);
      const inputs = [equation];
      if (equation.isCall2('=>')) {
        return (equation.andThen('rewriteOnly', '/right', rules.axiom3())
                .andThen('unForall', '/right')
                .justify('reduceEqn', inputs, inputs));
      } else {
        return (equation.andThen('rewriteOnly', '', rules.axiom3())
                .andThen('unForall', '')
                .justify('reduceEqn', inputs, inputs));
      }
    },
    inputs: {step: 1},
    labels: 'basic',
    menu: '[f = {x. p x}] to [f x = p x]',
    description: 'reduce equation'
  },

  // Use the definition of the name at the given location in the given
  // step.  If the definition is by cases the location should be a
  // call to the named function, with T or F as the argument.
  // For the benefit of the UI, if the path is to a call, uses
  // the definition of the named function of the call, even if there
  // is more than one argument, by descending into fn parts.
  //
  // TODO: Fix bug here that A != B does not become not (A = B).
  {name: 'useDefinition',
    precheck: function(step, path) {
      var term = step.get(path);
      var fn = term.funPart();
      // The fn could be a Lambda, which is not defined.
      // This returns falsy if the function is an "unused" constant.
      return (fn instanceof Atom && Toy.isDefined(fn.name));
    },
    action: function(step, path) {
      var args = [step, path];
      path = step.asPath(path);
      var result;
      var target = step.get(path);
      // Undefined if the path refers to an Atom.
      var parent;
      var parentPath;
      // Descend to the named function, even if multiple arguments.
      while (target instanceof Call) {
        parentPath = parentPath ? parentPath.concat('/fn') : path;
        parent = target;
        target = target.fn;
      }
      // At this point the parent (if defined) is a Call.
      // The parentPath is path to the parent if any.
      assert(target instanceof Atom, 'Not a symbol: {1}', target);
      result = rules.r1(step,
                        parentPath ? parentPath.concat('/fn') : path,
                        rules.definition(target.name));
      return result.justify('useDefinition', args, [step]);
    },
    inputs: {site: 1},
    menu: 'replace name with its definition',
    tooltip: (''),
    description: 'definition of {site}'
  }

);


// Some trivial rules not needing definitions

// These just(?) use axiom4 and Rule R.

// Definition rules need reduce and applyBoth to be available
// at the occurrence of Toy.definition.

declare(
  // Takes an arbitrary expression A, concluding that it is equal
  // to itself. (5200)
  {name: 'eqSelf',
    action: function(a) {
      a = termify(a);
      var step1 = rules.axiom4(call(Toy.parse('{x. x}'), a));
      var result = rules.r(step1, step1, '/left');
      return result.justify('eqSelf', arguments);
    },
    inputs: {term: 1},
    form: 'Term to prove equal to itself: <input name=term>',
    menu: 'A = A',
    tooltip: 'Derives A = A.',
    description: 'A = A',
    labels: 'primitive'
  },

  // The two forms of "=" are interchangeable (other than precedence).
  {name: 'eqIsEquiv',
    statement: '(=) = (==)',
    proof: function() {
      var step1 = rules.eqSelf(Toy.constify('='));
      var step2 = rules.eqSelf(Toy.constify('=='));
      return rules.r(step2, step1, '/right');
    },
    tooltip: '= and \u21d4 are the same',
    labels: 'uncommon'
  },

  // Given A, proves A == A.  This is intended for use only when
  // A is boolean.
  {name: 'equivSelf',
    action: function(a) {
      var step1 = rules.eqSelf(a);
      var eqn = rules.theorem('eqIsEquiv');
      var result = rules.r(eqn, step1, '/binop');
      return result.justify('equivSelf', arguments);
    },
    inputs: {bool: 1},
    form: 'Statement to prove equal to itself: <input name=bool>',
    menu: 'A \u21d4 A',
    tooltip: 'Derives A \u21d4 A.',
    description: 'A \u21d4 A',
    labels: 'primitive'
  },

  // Consider a term that we may wish to rewrite.  Functionally
  // the same as eqSelf, but display is handled specially.
  {name: 'consider',
    action: function(term_arg) {
      const term = termify(term_arg);
      const copy = term.deepCopy();
      copy.annotateWithTypes();
      if (copy.isBoolean()) {
        var step = rules.equivSelf(term);
      } else {
        var step = rules.eqSelf(term);
      }
      return step.justify('consider', arguments);
    },
    inputs: {term: 1},
    form: 'Term to consider: <input name=term>',
    menu: 'consider a term to transform',
    toOffer: 'return step == null',
    tooltip: ('consider a term to transform'),
    description: 'consider',
    labels: 'basic'
  },

  // Like "consider", but for formulas (boolean-valued terms)
  // Special case: this is only offerable if there are no steps
  // already in a proof.
  {name: 'given',
    action: function(term) {
      term = termify(term);
      var step = rules.equivSelf(term);
      return step.justify('given', arguments);
    },
    inputs: {term: 1},
    form: 'Formula to take as given: <input name=term>',
    menuGen: function(ruleName, step, term, proofEditor) {
      // This rule is only available if the proof is currently empty.
      return (proofEditor.proofDisplay.steps.length == 0
              ? ['problem to solve (givens)']
              : null);
    },
    tooltip: ('statement to take as given'),
    description: 'given',
    labels: 'algebra basic'
  },

  // Similar to "consider", but uses a selected term.
  {name: 'considerPart',
    action: function(step, path) {
      return (rules.consider(step.get(path))
              .justify('considerPart', arguments, [step]));
    },
    inputs: {site: 1},
    menu: 'consider {term} in isolation',
    tooltip: ('prepare to transform term'),
    description: 'term equal to itself',
    labels: 'display'
  },

  // r5201a is not implemented.  It would be ambiguous in case the
  // "whole" is a conditional.  Use rules.replaceT0 instead.

  // r5201b, works with a conditional equation.
  {name: 'eqnSwap',
    action: function(h_ab) {
      var ab = h_ab.getMain();
      var op = ab.getBinOp().pname;
      var aa = (op === '=='
                ? rules.equivSelf(ab.getLeft())
                : op === '='
                ? rules.eqSelf(ab.getLeft())
                : assert(false, 'Must be an equiv/equation: {1}', ab));
      // Plain replace is suitable here.  If h_ab is a pure equation
      // it is the same as r1.
      var ba = rules.replace(aa, '/main/left', h_ab);
      return ba.justify('eqnSwap', arguments, arguments);
    },
    inputs: {equation: 1},
    form: 'Swap sides in step <input name=equation>',
    menu: '[a = b] to [b = a]',
    tooltip: 'from a = b deduce b = a',
    description: '[a = b] to [b = a]',
    labels: 'basic algebra'
  },

  // r5201c is unused.
  // r5201d is not used.
  // r5201e, with eqn potentially conditional.
  //
  {name: 'applyBoth',
    action: function(eqn, a) {
      const step1 = (eqn.isCall2('==')
                     ? rules.equivSelf(call(eqn.eqnLeft(), a))
                     : rules.eqSelf(call(eqn.eqnLeft(), a)));
      // Plain replace is OK here, and becomes r1 if eqn is pure.
      const step2 = rules.replace(step1, '/right/fn', eqn);
      return step2.justify('applyBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    toOffer: ((step, term) =>
              step.wff.getLeft().hasType() instanceof Toy.FunctionType),
    form: ('Apply both sides of step <input name=equation>'
           + ' to term <input name=term>'),
    menu: '[f = g] to [f val = g val]',
    tooltip: 'given f = g, deduce (f term) = (g term)',
    description: '[f = g] to [f val = g val]',
    labels: 'primitive'
  },

  // r5201f.  Works with a conditional equation "ab".
  // If f is a lambda expression, also applies it to both sides.
  {name: 'applyToBoth',
    action: function(f_arg, ab) {
      var f = termify(f_arg);
      var fafa = rules.eqSelf(call(f, ab.eqnLeft()));
      // Plain replace is OK here, and becomes r1 if ab is pure.
      var fafb = rules.replace(fafa, '/right/arg', ab);
      var result = fafb;
      if (f instanceof Toy.Lambda) {
        var step2 = rules.apply(fafb, '/main/left');
        var result = rules.apply(step2, '/main/right');
      }
      return result.justify('applyToBoth', arguments, [ab]);
    },
    inputs: {term: 1, equation: 2},
    form: ('Apply function <input name=term>'
           + ' to both sides of step <input name=equation>'),
    menu: '[a = b] to [f a = f b]',
    tooltip: 'given a = b deduce (f a) = (f b)',
    description: 'from a = b to (f a) = (f b)',
    labels: 'primitive'
  },

  // Apply a function of 2 args to each side of the given equation,
  // with the side of the equation as first argument and the given
  // term as second argument, resulting in a call to the function
  // with the equation side as first argument and the given
  // second argument.
  // 
  // Works with a conditional equation.
  {name: 'applyToBothWith',
    action: function(a_b, f_arg, c_arg) {
      var f = Toy.constify(f_arg);
      var c = termify(c_arg);
      var fn = call(call(termify('{f. {y. {x. f x y}}}'), f), c);
      return (rules.applyToBoth(fn, a_b)
              .andThen('reduce', '/main/right/fn/fn')
              .andThen('reduce', '/main/right/fn')
              .andThen('reduce', '/main/right')
              .andThen('reduce', '/main/left/fn/fn')
              .andThen('reduce', '/main/left/fn')
              .andThen('reduce', '/main/left')
              .justify('applyToBothWith', arguments, [a_b]));
    },
  },

  // Just applies an anonymous lambda to an argument at the specified
  // location in a step.  (This is beta reduction.)
  {name: 'reduce',
    action: function(step, path) {
      // Note that axiom 4 checks validity of its argument.
      var equation = rules.axiom4(step.get(path));
      var result = rules.r(equation, step, path);
      return result.justify('reduce', arguments, [step]);
    },
    // TODO: Check that we do want to offer this interactively.
    inputs: {reducible: 1},
    isRewriter: true,
    menuGen: function(ruleName, step, term) {
      return Toy.format('apply function of {1}', term.fn.bound);
    },
    tooltip: ('Applies a lambda to its argument'),
    description: '=reduce',
    labels: 'uncommon'
  }

);


declare(
  // "Reduces" a call identified by a path within a theorem. If the
  // call is an application of a lambda expression to an argument,
  // beta-reduces it.  If the target expression is a call to a named
  // function supplying one or two arguments, expands the definition
  // and applies the expansions to the argument(s).
  //
  // TODO: Consider making this functionality part of useDefinition.
  {name: 'apply',
    precheck: function(step, path) {
      var term = step.get(path);
      var fn = term.funPart();
      var n = term.argsPassed();
      // The fn could be a Lambda, which is not defined.
      // This returns falsy if the function is an "unused" constant.
      return ((n === 1 || n === 2) &&
              (fn instanceof Lambda ||
               (fn instanceof Atom && Toy.isFunDef(fn.name))));
    },
    action: function(step, path) {
      // Returns an identity with arg as LHS.
      function applier(expr) {
        assert(expr instanceof Toy.Call, 'Not a call: {1}', expr, step);
        var fn = expr.fn;
        if (fn instanceof Toy.Lambda) {
          return rules.axiom4(expr);
        }
        // Call that looks like (<constant> <expr>).
        if (fn.isConst()) {
          var defn = Toy.findDefinition(fn.name);
          if (defn) {
            return (rules.eqSelf(expr)
                    .andThen('useDefinition', '/right/fn')
                    .andThen('reduce', '/right'));
          }
        }
        // Call that looks like (<left> <constant> <right>) or
        // equivalently ((<constant> <arg1>) <arg2>).
        if (expr.isCall2()) {
          var call = expr.fn;
          var fn2 = call.fn;
          if (fn2.isConst()) {
            var defn = Toy.findDefinition(fn2.name);
            if (defn) {
              var step1 = rules.eqSelf(call);
              var step2 = rules.useDefinition(step1, '/right/fn');
              var step3 = rules.reduce(step2, '/right');
              var step4 = rules.eqSelf(expr);
              var step5 = rules.r1(step4, '/right/fn', step3);
              return rules.reduce(step5, '/right');
            }
          }
        }
        abort('Cannot apply at {1} in {2}', step.get(path), step);
      }

      return Toy.convert(step, path, applier)
        .justify('apply', [step, path], [step]);
    },
    isRewriter: true,
    inputs: {site: 1},
    menuGen: function(ruleName, step, term) {
      var format = Toy.format;
      if (!(term instanceof Call)) {
        return null;
      }
      if (term.fn.isConst()) {
        return format('apply definition of {1}', term.fn);
      } else {
        return format('apply function of {1}', term.fn.bound);
      }
    },
    tooltip: ('Applies a function, named or not, to one or two arguments'),
    description: '=apply'
  },

  /**
   * Change the name of a bound variable.  Replaces the lambda
   * subexpression in expr at path with one that binds newName, which
   * may be a string or Atom, and uses it in place of any references to
   * the old bound variable.
   *
   * In case the body of the lambda has any free occurrence of the
   * given new name, this uses a name with the same initial letter as
   * the given name, but distinct from all of its free variables.
   *
   * TODO: Make this work also with the bound variable as the site.
   * In that case check the parent path (Path.parent).  Keep current
   * behavior for compatibility.  Possibly classify as "advanced"
   * again.
   */
  {name: 'renameBound',
   action: function(step, path, name_arg) {
      const newName = typeof name_arg === 'string' ? name_arg : name_arg.name;
      var target = step.get(path);
      // Report the step, but not in the message.
      assert(target instanceof Toy.Lambda,
             'Not a function: {1}', target, step);
      if (target.bound.name === newName) {
        // No need to do anything in this case, so do not rename anything.
        return step;
      }
      const newVar = target.body.freshVar(newName);
      var changed = lambda(newVar,
                           target.body.subFree1(newVar, target.bound));
      var step1 = rules.eqSelf(changed);
      var step2 = rules.r(step1, step, path);
      return step2.justify('renameBound', arguments, [step]);
    },
   labels: 'basic',
   inputs: {bindingSite: 1, varName: 3},
   form: ('Rename to <input name=varName>'),
   menu: 'rename bound variable',
   tooltip: ('Change the name of a bound variable.  The new name '
             + 'must not occur free in the target expression.  '
             + 'Uses the fact that the original expression matches '
             + 'the one with changed bound variable.'),
   description: '=renameBound'
  },

  /**
   * From an equation, infers a similar equation with each
   * side wrapped in a binding of the given variable or variable name.
   */
  {name: 'bindEqn',
    action: function(h_eqn, v) {
      if (h_eqn.isCall2('=>')) {
        debugger;
      }
      // TODO: Simplify the rest of the code based on it just being
      //   an equation.
      v = varify(v);
      var eqn = h_eqn.getMain();
      eqn.assertCall2('=');
      const step1 = (eqn.isCall2('==')
                     ? rules.equivSelf(lambda(v, eqn.getLeft()))
                     : rules.eqSelf(lambda(v, eqn.getLeft())));
      const step2 = rules.r1(step1, '/right/body', h_eqn);
      return step2.justify('bindEqn', arguments, [h_eqn]);
    },
    inputs: {equation: 1, varName: 2},
    form: ('Bind variable <input name=varName> in step <input name=equation>'),
    menu: '[a = b] to [{v. a} = {v. b}]',
    tooltip: ('Makes each side of an equation into a function'
              + ' of the variable you choose.'),
    description: '[a = b] to [{v. a} = {v. b}]',
    labels: 'primitive'
  },

  /**
   * Substitutes term "a" for variable or name "v" in equation b_c,
   * with the result a consequence of b_c.  (5209)
   */
  {name: 'instEqn',
    action: function(b_c_arg, a_arg, v) {
      var b_c = termify(b_c_arg);
      var a = termify(a_arg);
      var bound = rules.bindEqn(b_c, v);
      var step2 = rules.applyBoth(bound, a);
      var step3 = rules.reduce(step2, '/left');
      var step4 = rules.reduce(step3, '/right');
      return step4.justify('instEqn', arguments, [b_c]);
    },
    inputs: {equation: 1, term: 2, varName: 3},
    form: ('Instantiate <input name=varName> with <input name=term> '
           + 'in step <input name=equation>'),
    menu: 'substitute for a variable in equation',
    tooltip: ('Instantiates a free variable in an equation.'),
    description: 'substitute for {var}',
    labels: 'primitive'
  },

  /**
   * forall {x. x = x}
   * Helper lemma for eqT.
   */
  {name: 'xAlwaysX',
    statement: 'forall {x. x = x}',
    proof: function() {
      var a3 = rules.axiom3();
      var step1 = rules.instEqn(a3, 'f', 'g');
      var step2 = rules.instEqn(step1, '{y. y}', 'f');
      var step3 = rules.reduce(step2, '/right/arg/body/right');
      var step4 = rules.reduce(step3, '/right/arg/body/left');
      var step5 = rules.eqSelf(Toy.parse('{y. y}'));
      return rules.r(step4, step5, '');
    }
  },

  // T == [B = B] (5210)
  {name: 'eqT',
    action: function(b) {
      var lemma = rules.theorem('xAlwaysX');
      var step0 = rules.useDefinition(lemma, '/fn')
      var step1 = rules.applyBoth(step0, b);
      var step2 = rules.reduce(step1, '/right');
      var step3 = rules.reduce(step2, '/left');
      return step3.justify('eqT', arguments, []);
    },
    inputs: {term: 1},
    form: ('Term to prove equal to itself: <input name=term>'),
    menu: '(T = (A = A))',
    tooltip: ('Proves T = [A = A].'),
    description: 'T = (A = A)',
    labels: 'primitive'
  },

  /**
   * "T" is a theorem.  In the book, T is defined as an instance of
   * eqSelf.
   */
  {name: 't',
    statement: 'T',
    proof: function() {
      const step1 = rules.eqSelf(T);
      const step2 = rules.eqT(T);
      const step3 = rules.eqnSwap(step2);
      return rules.r1(step1, '', step3);
    }
  },

  /**
   * Extract the body term from a select use of forall, renaming the
   * bound variable if necessary to keep it distinct from all (other)
   * free variables.  This is a useful special case of instForall that
   * does not need the user to enter data through a form.
   *
   * TODO: Consider obsoleting this in favor of unForall0.
   */
  {name: 'unForall',
    precheck: function(step, path) {
      const target = step.get(path);
      const pathStr = path.toString();
      const conditional = step.wff.isCall2('=>');
      const ok = (target &&
                  target.isCall1('forall') &&
                  target.arg instanceof Toy.Lambda &&
                  // TODO: Handle cases where the target is unconditional.
                  (conditional
                   ? (pathStr === '/right' ||
                      pathStr === '/main' ||
                      pathStr === '/arg')
                   : (pathStr === '' ||
                      pathStr === '/main')));
      return ok;
    },
    action: function(step, path) {
      const bound = step.get(path).arg.bound;
      const name = step.wff.freshVar(bound.name);
      return (rules.instForall(step, path, name)
              .justify('unForall', arguments, [step]));
    },
    toOffer: function(step, term) {
      var path = step.prettyPathTo(term);
      return rules.instForall.precheck(step, path);
    },
    inputs: {site: 1},
    labels: 'basic',
    menu: '[&forall; {v. p v}] to [p v]',
    tooltip: ('In &forall;, instantiates the bound variable.'),
    description: '[&forall; {v. p v}] to [p v]'
  },

  // Like unforall, but takes just the step as input.
  {name: 'unForall0',
    precheck: function(step) {
      const target = step.wff;
      return target.isCall1('forall') && target.arg instanceof Toy.Lambda;
    },
    action: function(step) {
      const wff = step.wff;
      const bound = wff.arg.bound;
      return (rules.instForall(step, '', bound.name)
              .justify('unForall0', arguments, [step]));
    },
    toOffer: function(step) {
      return rules.instForall.precheck(step, '');
    },
    inputs: {step: 1},
    labels: 'basic',
    menu: '[&forall; {v. p v}] to [p v]',
    description: '[&forall; {v. p v}] to [p v]'
  },

  // Target is a step of the form forall {x. B}, expr is A, which will
  // replace all occurrences of x.  Uses no book-specific definitions,
  // and relies only on theorem "T", 5200, and reduce. (5215)
  //
  // Accepts a string for the expr, and supports a target that is the
  // RHS of a conditional.
  //
  // TODO: Consider cleaning up the conditions on the path.
  //
  // Careful: The conditional form has more dependencies because
  // it uses rules.replace with a conditional equation.
  {name: 'instForall',
    precheck: function(step, path, expr_arg) {
      const target = step.get(path);
      const pathStr = path.toString();
      const conditional = step.wff.isCall2('=>');
      const ok = (target &&
                  target.isCall1('forall') &&
                  target.arg instanceof Toy.Lambda &&
                  // TODO: Handle cases where the target is unconditional.
                  (conditional
                   ? (pathStr === '/right' ||
                      pathStr === '/main' ||
                      pathStr === '/arg')
                   : (pathStr === '' ||
                      pathStr === '/main')));
      return ok;
    },
    action: function(step, path, expr_arg) {
      const expr = termify(expr_arg);
      const eqn1 = rules.useDefinition(step, path);
      var step2 = rules.applyBoth(eqn1, expr);
      var step3 = rules.reduce(step2, '/main/left');
      var step4 = rules.reduce(step3, '/main/right');
      // The conditional form of this rule uses the conditional
      // form of rules.replace.
      var step5 = (step.isCall2('=>')
                   ? rules.rewriteOnly(step4, '/main', '(T == a) == a')
                   : rules.fromTIsA(step4));
      return step5.justify('instForall', arguments, [step]);
    },
    toOffer: function(step, term) {
      var path = step.prettyPathTo(term);
      return rules.instForall.precheck(step, path, term);
    },
    // "Unforall" followed by plain substitution serve well for this.
    labels: 'obsolete',
    inputs: {site: 1, term: 3},
    form: ('Instantiate &forall; with term <input name=term>'),
    menu: 'instantiate &forall;',
    tooltip: ('In &forall;, instantiates the bound variable.'),
    description: 'instantiate &forall;'
  },

  // From [A = B] deduce T = [A = B].
  {name: 'toTIsEquation',
    action: function(a_b) {
      assertEqn(a_b);
      var step1 = rules.eqT(a_b.get('/left'));
      var step2 = rules.r1(step1, '/right/right', a_b);
      return step2.justify('toTIsEquation', arguments, [a_b]);
    },
    inputs: {equation: 1},
    form: 'Introduce "T = " into step <input name=equation>',
    menu: '[a = b] to [T = (a = b)]',
    tooltip: ('From [a = b] deduce T = [a = b].'),
    description: 'from a = b to T = (a = b)',
    labels: 'primitive'
  },

  // Deduces the conjunction of two proved unconditional equations.
  // Helper for equationCases.
  {name: 'andEqns',
    action: function(step1, step2) {
      var step3 = rules.toTIsEquation(step1);
      var step4 = rules.toTIsEquation(step2);
      var step5 = rules.r1(rules.theorem('r5212'), '/left', step3);
      var step6 = rules.r1(step5, '/right', step4);
      return (step6.justify('andEqns', arguments, arguments));
    },
    inputs: {step: [1, 2]},
    form: ('Prove conjunction of equation <input name=step1> ' +
           'and equation <input name=step2>'),
    menu: '[a = b] and [c = d] to [a = b & c = d]',
    tooltip: ('Given [a = b] and [c = d], derive [a = b & c = d]'),
    description: 'a = b & c = d;; from steps {step1}, {step2}',
    labels: 'internal'
  },

  // Given two WFFs each of the form A = B that are the result of
  // substituting T and F respectively for a variable, proves the WFF
  // with the variable.
  {name: 'equationCases',
    action: function(caseT, caseF, v) {
      v = varify(v);
      var step1 = rules.andEqns(caseT, caseF);
      // Note: If a variable is not in caseT it is also not in caseF.
      var newVar = Toy.genVar('w', caseT.allNames());
      var gen = caseT.generalizeTF(caseF, newVar);
      var lexpr = lambda(newVar, gen);
      var step4 = rules.instEqn(rules.axiom1(), lexpr, 'g');
      var step5 = rules.reduce(step4, '/right/arg/body');
      var step6 = rules.reduce(step5, '/left/right');
      var step7 = rules.reduce(step6, '/left/left');
      var step8 = rules.r(step7, step1, '');
      var step9 = rules.instForall(step8, '', v);
      return step9.justify('equationCases', arguments, [caseT, caseF]);
    },
    inputs: {equation: [1, 2], varName: 3},
    form: ('Cases: true case step <input name=equation1>'
           + ' false case step <input name=equation2>,'
           + ' use variable <input name=varName>'),
    menu: 'proof by cases, for equations',
    tooltip: ('Given two proved equations C and D obtainable by substitution' +
              ' for a free variable of an equation A = B; C by substituting' +
              ' T, and D by substituting F, proves A = B.'),
    labels: 'primitive'
  },

  {name: 'r5211',
    statement: 'T & T == T',
    proof: function() {
      var step1 = rules.instEqn(rules.axiom1(), '{y. T}', 'g');
      var step2a = rules.apply(step1, '/right/arg/body');
      var step2b = rules.apply(step2a, '/left/right');
      var step2c = rules.apply(step2b, '/left/left');
      var step3a = rules.eqT(Toy.parse('{x. T}'));
      var step3b = rules.rRight(step3a, '/right/fn',
                                rules.definition('forall'));
      return rules.rRight(step2c, '/right', step3b);
    }
  },

  // T & T.
  // Used to prove equationCases.  The "cases" rule
  // and makeConjunction could treat this as a tautology.
  {name: 'r5212',
    statement: 'T & T',
    proof: function() {
      return rules.rRight(rules.theorem('t'), '', rules.theorem('r5211'));
    }
  }

);

// Now onward to proving a few of the usual truth table facts.

if (useFalseDefn) {
declare(
  {name: 'defFFromBook',
    statement: 'F = forall {x. x}',
    proof: function() {
      return rules.definition('F');
    }
  },

  // Bookish: [T & F] = F
  // Uses defFFromBook.
  {name: 'r5214',
    statement: 'T & F == F',
    proof: function() {
      var step1 = rules.axiom1();
      var step2 = rules.instEqn(step1, Toy.parse('{x. x}'), 'g');
      var step3 = rules.reduce(step2, '/right/arg/body');
      var step4 = rules.reduce(step3, '/left/right');
      var step5 = rules.reduce(step4, '/left/left');
      var step6 = rules.defFFromBook();
      return rules.rRight(step5, '/right', step6);
    }
  },

  // 5216: [T & A] = A
  // TODO: A theorem T & x == x would be adequate since it is an
  //   equation.  Then apply instEqn as needed.  It would be a
  //   simplifier.  (Just change step10.)
  {name: 'andTBook',
    action: function(a) {
      var step1 = rules.axiom1();
      var step2 = rules.instEqn(step1, '{x. T & x == x}', 'g');
      var step3 = rules.reduce(step2, '/left/left');
      var step4 = rules.reduce(step3, '/left/right');
      var step5 = rules.reduce(step4, '/right/arg/body');
      var step7 = rules.r5214();
      var step8 = rules.r5213(rules.theorem('r5211'), step7);
      var step9 = rules.r(step5, step8, '');
      var step10 = rules.instForall(step9, '', a);
      return step10.justify('andTBook', arguments);
    }
  },

  // r5217 is the same as r5230TF.
  // [T = F] = F
  // Relies on F == forall {x. x} (defn of F).
  {name: 'r5217Book',
    statement: '(T == F) == F',
    proof: function() {
      var step1 = rules.instEqn(rules.axiom1(), '{x. T = x}', 'g');
      var step2a = rules.reduce(step1, '/left/left');
      var step2b = rules.reduce(step2a, '/left/right');
      var step2c = rules.reduce(step2b, '/right/arg/body');
      var step3 = rules.rRight(step2c, '/left/left', rules.eqT(T));
      var step4a = rules.andTBook(equal(T, F));
      var step4b = rules.r(step4a, step3, '/left');
      var step5a = rules.instEqn(rules.axiom3(), '{x. T}', 'f');
      var step5b = rules.instEqn(step5a, '{x. x}', 'g');
      var step6a = rules.reduce(step5b, '/right/arg/body/left');
      var step6b = rules.reduce(step6a, '/right/arg/body/right');
      var step6c = rules.useDefinition(rules.defFFromBook(),
                                       '/right/fn');
      var step6d = rules.rRight(step6b, '/left', step6c);
      return rules.rRight(step4b, '/right', step6d);
    }
  },

  // F => x; bookish
  {name: 'r5227',
    statement: 'F => x',
    proof: function() {
      var step1 = rules.theorem('r5225');
      var step2 = rules.instVar(step1, Toy.parse('{x. x}'), 'p');
      var step3 = rules.defFFromBook();
      var step4 = rules.rRight(step2, '/left', step3);
      return rules.reduce(step4, '/right');
    }
  },

  // Proves [F = T] = F (r5230FT) from r5217Book (r5230TF).
  // Relies also on facts about "=>", which are not currently
  // proven from "book" definitions.
  //
  // With r5217Book and this, and the book definition of false,
  // and some sort of truth table definition of =>, 
  //
  // TODO: Is there a more elegant proof of this?
  {name: 'r5230FT_alternate',
    statement: '(F == T) == F',
    proof: function() {
	const map1 = {x: 'F', y: 'T', h: '{x. x = F}'};
	const step1c = rules.instMultiVars(rules.axiom2(), map1);
	const step2b = rules.reduceAll(step1c, '/right');
	const step3a1 = rules.eqT(F);
	const step3a2 = rules.eqnSwap(step3a1);
	const step3a = rules.r1(step2b, '/right/left', step3a2);
	const step3bb = rules.r5218(F);
	const step3b = rules.r1(step3a, '/right/right', step3bb);
	const step3c = rules.r1(step3b, '/right', step3bb);
	// From this point most of the work is basically a proof
	// that [A => F] => not A, a tautology.
	const step4 = rules.rewriteOnly(step3c, '', 'p == (T == p)');
	// We are going to prove the cases of: (x => F) = (x = F)
	// First with x = F.
	const step11 = rules.fact('(a => b) = if a b T');
	const step12 = rules.instMultiVars(step11, {a: 'F', b: 'F'});
	const step13 = rules.rewriteOnly(step12, '/right', 'if F x y = y');
	const step14 = rules.r1(step13, '/right', step3a1);
	// Then with x = T.
	const step21 = rules.fact('(a => b) = if a b T');
	const step22 = rules.instMultiVars(step21, {a: 'T', b: 'F'});
	const step23 = rules.rewriteOnly(step22, '/right', 'if T x y = x');
	const step24 = rules.r5217Book();
	const step25 = rules.rRight(step23, '/right', step24);
	// Now use the cases rule:
	const step5 = rules.equationCases(step25, step14, 'x');
	// Then instantiate [F = T] for x.
	const step6 = rules.instEqn(step5, equal(F, T), 'x');
	// And use the fact that [F = T] => F
	const step7 = rules.rRight(step6, '/left', step4);
	return rules.rewriteOnly(step7, '', '(T == p) == p');
    },
    tooltip: ('[F = T] = F')
  }

)};



// These are not specific to book definitions, but currently may
// use (non-book) definitions by cases.

declare(
  // From theorems A = B and C = D, derives theorem
  // [A = B] & [C = D].  Used in andTBook.
  {name: 'r5213',
    action: function(a_b, c_d) {
      assertEqn(a_b);
      var a = a_b.get('/left');
      var b = a_b.get('/right');
      assertEqn(c_d);
      var c = c_d.get('/left');
      var d = c_d.get('/right');
      var step1 = rules.eqT(a);
      var step2 = rules.r(a_b, step1, '/right/right');
      var step3 = rules.eqT(c);
      var step4 = rules.r(c_d, step3, '/right/right');
      var step5 = rules.r(step2, rules.theorem('r5212'), '/left');
      var step6 = rules.r(step4, step5, '/right');
      return step6.justify('r5213', arguments, arguments);
    }
  }

);

// This might be treated as the end of the subcore.
// Managing numeric type assumptions

declare(
  // Simplifies repeatedly using basicSimpFacts.  If the visible part
  // of the step is an equation, simplify each side, otherwise the
  // entire expression.
  {name: 'simplifyFocalPart',
    action: function(step) {
      var visPath = step.pathToFocalPart();
      var result = rules._simplifySite(step, visPath);
      return result.justify('simplifyFocalPart', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Simplify step <input name=step>'),
    menu: 'algebra: simplify',
    description: 'simplify;; {step step}',
    labels: 'algebra'
  },

  // Applies simplification repeatedly within the part of the given
  // step at the given path using the given facts until no more
  // simplifications are found.  The simplifiers can be conditional
  // and thus generate assumptions.  By default uses basicSimpFacts if
  // facts are not supplied.
  //
  // Ultimately uses rules.rewrite and rules.replace, so resulting
  // assumptions will be simplified and arranged.
  {name: 'simplifySite',
    action: function(step, path, opt_facts) {
      var result = rules._simplifySite(step, path, opt_facts);
      return result.justify('simplifySite', arguments, [step]);
    },
    inputs: {site: 1},
    minArgs: 2,
    menu: 'algebra: simplify {term}',
    description: 'simplify;; {in step siteStep}',
    labels: 'algebra'
  },

  // Repeatedly apply the one fact as in simplifySite, to
  // simplify the target site.
  // 
  // TODO: Consider supporting a conjunction as equivalent to a list
  //   of its conjuncts.  Maybe merge with simplifySite.
  {name: 'simplifySiteWith',
    action: function(step, path, fact_arg) {
      var result = rules._simplifySite(step, path, [fact_arg]);
      return result.justify('simplifySiteWith', arguments, [step]);
    },
    inputs: {site: 1, term: 3},
    menu: 'algebra: simplify {term} with fact',
    form: 'Simplify using term <input name=term>',
    description: 'simplify using {term};; {in step siteStep}',
    labels: 'algebra'
  },

  // TODO: Create a "rules.simplifier" that takes a term argument
  //   and proves it equal to some (hopefully) simpler term.

  // Inline version of simplifySite.  Uses full rewriting and replace,
  // so resulting assumptions are simplified.  If the simplification
  // has no effect, return the input step.  This also enables "justify"
  // to pretend this (or its caller!) was never invoked.
  {name: '_simplifySite',
    action: function(step, path, opt_facts) {
      var eqn = rules.consider(step.get(path));
      var simpler = Toy.repeatedly(eqn, function(eqn) {
          // This usage of /main is kind of cool in that it automatically
          // adapts in case some versions of eqn have assumptions.
          return rules._simplifyOnce(eqn, eqn.asPath('/main/right'), opt_facts);
        });
      if (eqn.sameAs(simpler)) {
        return step;
      } else {
        return rules.replace(step, path, simpler);
      }
    }
  },

  // Applies up to one simplification (using rewriting on facts)
  // within the part of the given step at _path using the given facts,
  // or basicSimpFacts if facts are not given.  Returns its result
  // inline, just the input step if there is nothing to do.  This
  // common support code uses rules.rewrite, which is generally
  // appropriate, but not always.
  //
  // Uses rules.rewrite, so simplifies resulting assumptions.
  //
  // From the UI use a rule that calls this one.
  {name: '_simplifyOnce',
    action: function(step, _path, opt_facts) {
      var facts = opt_facts || basicSimpFacts;
      var info = Toy.searchForMatchingFact(step.get(_path), facts);
      return (info
              ? rules.rewrite(step, _path.concat(info.path), info.stmt)
              : step);
    }
  },

  // Uses the given facts to simplify the assumptions of the given
  // step, by default using asmSimplifiers, for example to manage type
  // assumptions, e.g. "is real", "is integer", etc..  This also
  // differs from other simplifiers in that it also simplifies any
  // assumptions introduced by conditional facts in the facts list.
  // Ensures the result has its assumptions arranged, and if the
  // assumptions reduce to T, removes the assumptions entirely.
  {name: 'simplifyAsms',
    action: function(step, facts_arg) {
      const facts = facts_arg || Toy.asmSimplifiers;
      if (!step.wff.isCall2('=>')) {
        return step;
      }
      let simpler = step;
      // Uses rewriteOnly, avoiding recursive calls to simplifyAsms
      // which could be problematic or simply result in unintuitive
      // displays of the process.
      const rw = rules.rewriteOnly;
      // Repeatedly apply simplifying facts, each time removing T from
      // the assumptions.  Note that rewriteOnly adds any new
      // assumptions, making them available on the next iteration.
      const search = Toy.searchForMatchingFact;
      const left = Toy.asPath('/left');
      while (true) {
        const info = search(simpler.get('/left'), facts);
        if (info) {
          simpler = (rw(simpler, left.concat(info.path),
                        info.stmt));
          // Immediately remove T if possible, partly for clean displays.
          const info2 = search(simpler.get('/left'),
                              ['a & T == a', 'T & a == a']);
          if (info2) {
            simpler = rw(simpler, left.concat(info2.path), info2.stmt);
          }
        } else {
          // No applicable fact found.
          // Dedupe and normalize order of asms.
          simpler = rules.arrangeAsms(simpler);
          // If only T remains, remove it.
          simpler = (Toy.applyMatchingFact(simpler, '', ['T => a == a'],
                                           'rewriteOnly') ||
                     simpler);
          // And we are done.
          return simpler.justify('simplifyAsms', arguments, [step]);
        }
      }
    },
    inputs: {step: 1},
    minArgs: 1,
    menu: 'simplify assumptions',
    description: 'simplify assumptions;; {in step step}',
    labels: 'general'
  }
);

/**
 * Function callable to simplify an entire step.  Useful
 * as an autoSimplify function.
 */
function simplifyStep(step) {
  return rules.simplifySite(step, '');
}

declare(
  // [T = x] = x
  // Note that this or 5230TF or symmetry of equality of booleans
  // might be taken as an axiom given r5230FT_alternate.
  {name: 'tIsXIsX',
    statement: '(T == x) == x',
    proof: function() {
      var step1 = rules.theorem('r5217Book');
      var step2 = rules.eqT(T);
      var step3 = rules.eqnSwap(step2);
      return rules.equationCases(step3, step1, 'x');
    }
  },

  // 5218: [T == A] == A
  // Stepping stone to universal generalization.
  // TODO: Replace all uses of this with rewrites.
  {name: 'r5218',
    action: function(a) {
      var step1 = rules.theorem('tIsXIsX');
      var step2 = rules.instEqn(step1, a, 'x');
      return step2.justify('r5218', arguments);
    },
    inputs: {bool: 1},
    form: ('Term to use in ((T = A) = A): <input name=bool>'),
    menu: '(T = A) = A',
    labels: 'uncommon',
    tooltip: ('For any expression derives (T = A) = A.'),
    description: '(T = A) = A'
  },

  // 5219: [A] to [T == A].
  // TODO: Consider replacing all uses of this with rewrites.
  {name: 'toTIsA',
    action: function(step) {
      const step1 = rules.r5218(step);
      const step2 = rules.rRight(step, '', step1);
      return step2.justify('toTIsA', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Introduce "T = " into step <input name=step>',
    menu: '[a] to [T = a]',
    tooltip: ('From A derives T = A'),
    description: '[a] to [T = a];; {in step step}',
    labels: 'primitive'
  },

  // also 5219: [T == A] to [A].
  // Nice to have for proving instForall.  Using low-level
  // primitives here prevents dependency problems there.
  {name: 'fromTIsA',
    precheck: function(step) {
      return step.matchSchema('T = p');
    },
    action: function(step) {
      const step1 = rules.theorem('t');
      const result = rules.r1(step1, '', step);
      return result.justify('fromTIsA', arguments, [step]);
    },
    inputs: {equation: 1},
    form: 'Eliminate "T = " from step <input name=equation>',
    description: '[T = a] to [a]',
    menu: '[T = a] to [a]',
    tooltip: ('From T = A derives A'),
    labels: 'primitive'
  },

  // Replaces an occurrence of T at the given path of the given step
  // with the entirety of another step.
  //
  // TODO: With the usual boolean connectives, the only case that
  //   does not immediately simplify is conjunction, so perhaps this
  //   should be replaced by a rule that inserts a conjunction with
  //   a theorem instead of replacing T.
  {name: 'replaceT0',
    precheck: function(step, path, step2) {
      return step.get(path).isConst('T');
    },
    action: function(step, path, step2) {
      assert(step.get(path).isConst('T'),
             'Site should be T, not {1}', step.get(path));
      var tIsA = rules.toTIsA(step2);
      return (rules.r(tIsA, step, path)
              .justify('replaceT0', arguments, [step, step2]));
    },
    inputs: {site: 1, step: 3},
    toOffer: 'return term instanceof Toy.Atom && term.name == "T"',
    form: ('Replace T with step <input name=step>'),
    menu: 'replace T with a whole true statement',
    tooltip: ('Replaces an occurrence of T with a true statement'),
    description: 'replace T;; {in step siteStep} {with step step}',
    labels: 'basic'
  },

  // Replaces an occurrence of T at the given path of the given step
  // with the consequent of another step, which must be conditional.
  //
  // TODO: See the TODO for replaceT0.
  {name: 'replaceT',
    precheck: function(step, path, step2) {
      return step.get(path).isConst('T') && step2.isCall2('=>');
    },
    action: function(step, path, step2) {
      assert(step.get(path).isConst('T'),
             'Site should be T, not {1}', step.get(path));
      const eqn = rules.rewrite(step2, '/main', 'x == (T == x)');
      return (rules.rewriteFrom(step, path, eqn)
              .justify('replaceT', arguments, [step, step2]));
    },
    inputs: {site: 1, step: 3},
    toOffer: 'return term instanceof Toy.Atom && term.name == "T"',
    form: ('Replace T with step <input name=step>'),
    menu: 'replace T with a true conclusion',
    tooltip: ('Replaces T with the conclusion of a true statement'),
    description: 'replace T;; {in step siteStep} {with step step}',
    labels: 'basic'
  },



// These trueBy rules are similar to rewriteOnlyFrom, but that one
// creates an equation or conditional equation based on its policy.

  // Replace part of a target step with T if it matches a proved step
  // (trueby0) or the consequent of a proved conditional (trueBy1),
  // taking the proved step as a schema.  These do not simplify
  // assumptions.
  //
  // Unlike the somewhat similar "rewrite" rules, this rule applies
  // the substitution to the target term, not to the "step" argument.
  {name: 'trueBy0',
    action: function(target, path, step) {
      const term = target.get(path);
      // Note that the keys of the map are precisely the names of the
      // free variables of the term.
      const map = step.wff.matchSchema(term);
      // Returns a possibly empty object/map substitution to rename
      // variables in the step to match target term variable names,
      // or null if it cannot match the term to the step.
      function precheck() {
        if (map == null) {
          return null;
        }
        const bound = target.wff.boundNames(path);
        // The following code seeks renamings of variables in the step
        // that match them with free variables of the target term that
        // are bound in context.
        //
        // This object will map from names in the step to names in the
        // target term that are bound in the term's context.  If the
        // search her is successful, it defines a substitution that
        // completes the matching done by matchSchema.
        const renamings = {};
        for (const name in bound) {
          if (name in map) {
            // This bound name is in the map, so it occurs free in the
            // target term.  Check if a free variable in the step can
            // be renamed to match it.
            const stepTerm = map[name];
            if (stepTerm.isVariable()) {
              const n = stepTerm.name;
              const renamed = renamings[n];
              if (renamed) {
                if (renamed !== name) {
                  return null;
                } else {
                  continue;
                }
              } else {
                // This can be an identity renaming, still needed
                // as indication that the name must remain the same.
                renamings[n] = name;
              }
            } else {
              // stepTerm is not a variable, so fail.
              return null;
            }
          }
        }
        const subst = {};
        // We have found suitable renamings.
        for (const name in renamings) {
          const renamed = renamings[name];
          if (renamed !== name) {
            subst[name] = varify(renamed);
          }
        }
        return subst;
      }
      const renames = precheck();
      if (renames) {
        // Now do the rest of the substitution.
        const step2 = rules.rewriteOnly(step, '', 'p == (p == T)');
        // console.log('Subst:', Toy.debugString(map));
        // console.log('Renaming:', Toy.debugString(renames));
        // TODO: Change this use of r1 to a new form of rewrite
        //   that substitutes into "step", using something like
        //   matchToRule / matchRuleTo in the process.
        let result = rules.r1(target, path, step2);
        return result.justify('trueBy0', arguments, [target, step]);
      }
      assert(false, 'Term {1} does not match {2}',
             target.get(path), step);
    },
    inputs: {site: 1, step: 3},
    autoSimplify: simplifyStep,
    toOffer: 'return term.isBoolean()',
    form: ('Match {term} with step <input name=step>'),
    menu: 'replace with T, proved unconditionally',
    description: ('term known true;; {in step siteStep} {by step step}'),
    labels: 'basic'
  },

  // Requires a conditional step, matching its consequent with
  // the target site and adding assumptions to the target step.
  //
  // The target term is the schema!
  {name: 'trueBy1',
    action: function(target, path, step) {
      if (step.isCall2('=>')) {
        const term = target.get(path);
        const map = step.getRight().matchSchema(term);
        if (map) {
          const step2 = rules.rewriteOnly(step, '/right', 'p == (p == T)');
          // TODO: Change this "replace" basically as described for
          //   trueBy0, with the additional possibility that variable
          //   bindings may prevent the substitution.
          const result = rules.replace(target, path, step2);
          return result.justify('trueBy1', arguments, [target, step]);
        }
      }
      assert(false, 'Term {1} does not match {2}',
             target.get(path), step);
    },
    inputs: {site: 1, step: 3},
    autoSimplify: simplifyStep,
    toOffer: 'return term.isBoolean()',
    form: ('Match {term} with consequent of step <input name=step>'),
    menu: 'replace with T, proved under assumptions',
    description: ('term known true;; {in step siteStep} {by step step}'),
    labels: 'basic'
  },

  // This finds a substitution into the schema to make it match the
  // part of the target at the given path. The substitution may need
  // to be followed by beta reduction(s) and/or renaming of bound
  // variables.  Names of variables bound within the match may differ
  // between the two terms, but names free relative to that context
  // must match exactly.
  //
  // The schema and target 
  //
  // TODO: Caution, this is poorly tested at present.  Test it better.
  //
  // TODO: Consider replacing with matchToRule and friends.
  {name: 'matchTerm',
    action: function(target, path, term) {
      const schema = target.get(path);
     const map = term.matchSchema(schema);
      if (map) {
        let funSites = new Map();
        for (const key in map) {
          if (map[key] instanceof Lambda) {
            funSites.set(key, target.locateFree(key));
          }
        }
        let simpler = rules.instMultiVars(target, map);
        funSites.forEach(function(rPaths) {
            rPaths.forEach(function (rPath) {
                for (let r = rPath; r.segment === 'fn'; r = r.rest) {
                  // First time r refers to the lambda, then successive
                  // parents as this does more reductions.  Could be
                  // done more efficiently.
                  const path = r.rest.reverse();
                  const s = rules.backReduce(simpler, path);
                  if (!s) {
                    break;
                  }
                  simpler = s;
                }
              });
          });

        // Uncomment these lines to restore afterMatch functionality:
        // const info = resolveToFactInfo(eqn_arg);
        // const after = (info && info.afterMatch) || function(x) { return x; };
        // simpler = after(simpler);
        return (simpler.justify('matchTerm', arguments, [target]));
      } else {
        return null;
      }
    },
    inputs: {site: 1, term: 3},
    form: ('Match with term <input name=term>'),
    menu: 'make {term} match term',
    description: ('substitute to match {term};; {in step siteStep}'),
    labels: 'basic'
  },

  // Lemma helper for toForall; a pure theorem.
  {name: 'forallXT',
    statement: 'forall {x. T}',
    proof: function() {
      var step1 = rules.eqSelf(Toy.parse('{x. T}'));
      var fa = rules.definition('forall');
      return rules.rRight(step1, '/fn', fa);
    }
  },

  {name: 'existsXT',
    statement: 'exists {x. T}',
    proof: function() {
      return (rules.fact('p x => exists p')
              .andThen('instVar', '{x. T}', 'p')
              .andThen('reduce', '/left')
              .andThen('simplifySite', ''));
    }
  },

  // This actually says NOT (forall {x. F}).
  {name: 'forallXF',
    statement: 'not (forall {x. F})',
    proof: function() {
      var fact = rules.fact('exists p == not (forall {x. not (p x)})');
      return (fact.andThen('instVar', '{x. T}', 'p')
              .andThen('apply', fact.find('p x'))
              .andThen('simplifySite', fact.find('not (p x)'))
              .andThen('trueBy0', '/left', rules.existsXT())
              .andThen('rewriteOnly', '', 'T == a == a'));
    }
  },

  // 5220 variant that from A deduces forall {v. A}.  The variable v
  // may be given as a string, which it converts internally to a
  // variable.
  //
  // TODO: Rename to just toForall.
  {name: 'toForall0',
    action: function(step, v_arg) {
      const v = varify(v_arg);
      var step1 = rules.rewriteOnly(step, '', 'a == (T == a)');
      var step2 = rules.theorem('forallXT');
      var step3 = rules.renameBound(step2, '/arg', v);
      var step4 = rules.r(step1, step3, '/arg/body');
      return step4.justify('toForall0', arguments, [step]);
    },
    inputs: {step: 1, varName: 2},
    form: ('In step <input name=step> generalize on variable '
           + '<input name=varName>'),
    menu: '[A] to [&forall; {v. A}]',
    tooltip: ('UGen for  a whole step'),
    description: '[A] to [&forall; {v. A}];; {in step step}'
  },

  // 5220 variant, from [A => B] deduces [A => forall {v. B}].
  // The variable v may be given as a string, which it converts
  // internally to a variable.  The step must be a conditional,
  // and v cannot be free in A.
  //
  // TODO: Consider whether all uses of this might be replaced
  //   by rewrites using implyForall.
  {name: 'toForall1',
    precheck: function(step, v_arg) {
      var v = varify(v_arg);
      var format = Toy.format;
      return (step.isCall2('=>') && !(step.getLeft().hasFreeName(v.name)));
    },
    action: function(step, v_arg) {
      const v = varify(v_arg);
      const step1 = rules.toForall0(step, v);
      // This will never need simplification of assumptions,
      // because in the end it leaves the assumptions unchanged.
      const step2 = rules.rewriteOnly(step1, '', rules.implyForall());
      return step2.justify('toForall1', arguments, [step]);
    },
    inputs: {step: 1, varName: 2},
    form: ('In step <input name=step> generalize on variable '
           + '<input name=varName>'),
    menu: '[A => B] to [A => &forall; {v. B}]',
    tooltip: ('UGen for [A => B]'),
    description: '[A => B] to [A => &forall; {v. B}];; {in step step}',
  },

  // 5221 (one variable), in the given step substitute term A for free
  // variable v, which may also be given as a string.
  {name: 'instVar',
    action: function(step, a, v) {
      a = termify(a);
      v = varify(v);
      var map = {};
      map[v.name] = a;
      var result = rules.instMultiVars(step, map);
      return result.justify('instVar', arguments, [step]);
    },
    inputs: {step: 1, term: 2, varName: 3},
    form: ('In step <input name=step>, for variable <input name=varName> '
           + 'substitute <input name=term>'),
    menu: 'substitute for a free variable',
    tooltip: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.'),
    description: 'substitute for {var};; {in step step}',
    labels: 'advanced'
  },

  // Same functionality as instVar, but with a site (step+path) and a
  // term as the arguments.  Inline, variant of instVar.
  {name: 'instantiateVar',
    toOffer: 'return term.isVariable()',
    action: function(step, path, term) {
      const v = step.get(path);
      assert(v.isVariable(), 'Not a variable: {1}', v);
      return rules.instVar(step, term, v);
    },
    inputs: {site: 1, term: 3},
    form: ('Substitute <input name=term> for {term}'),
    menu: 'substitute for {term}',
    tooltip: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.'),
   // This rule is inline, so has no description.
    labels: 'basic'
  },

  // More like the book's 5221.  For each name in the map (a string),
  // substitutes the expression associated with it in the map, using
  // simultaneous substitution.  Parses string values in the map.
  //
  // Optimized to avoid substitutions that have no effect, returning
  // its input, justified as "instMultiVars".
  {name: 'instMultiVars',
    action: function(b, map) {
      assert(map && map.constructor && map.constructor === Object,
             'Non-map argument to instMultiVars: {1}', map);
      var isEqn = b.isCall2('=');
      // Ensure that the step is a (pure) equation.
      var step = isEqn ? b : rules.rewriteOnly(b, '', 'a == (T == a)');
      var namesReversed = [];
      for (var name in map) {
        if (name === '%expansions') {
          continue;
        }
        var value = termify(map[name]);
        if (value.isVariable() && value.name === name) {
          // If the variable maps to itself, do nothing.
          continue;
        }
        step = rules.bindEqn(step, name);
        namesReversed.unshift(name);
      }
      if (namesReversed.length === 0) {
        return b.justify('instMultiVars', arguments, [b]);
      }
      // Then substitute for the variables, outermost binding first.
      namesReversed.forEach(function(name) {
        // The step is now an equation between two functions,
        // apply both to sides to the appropriate term
        // and reduce the result in both sides, substituting.
        var step2 = rules.applyBoth(step, map[name]);
        var step3 = rules.reduce(step2, '/right');
        step = rules.reduce(step3, '/left');
      });
      if (!isEqn) {
        step = rules.fromTIsA(step);
      }
      return step.justify('instMultiVars', arguments, [b]);
    },
    inputs: {step: 1},
    menu: 'substitute for multiple variables',
    tooltip: ('For each variable in the map substitute its value in the map'),
    description: '=instMultiVars'
  },

  // Given two theorems a1 => a and a2 => b, proves a1 & a2 => a & b.
  // If either theorem is unconditional, omits a1 or a2 or both
  // accordingly.
  // TODO: Replace usage with trueBy1, and remove this.
  {name: 'makeConjunction',
    action: function(a, b) {
      var stepa = rules.rewriteOnly(a, '/main', 'a == (T == a)');
      var stepb = rules.rewriteOnly(b, '/main', 'a == (T == a)');
      var step1 = rules.theorem('r5212');
      var step2 = rules.rewriteFrom(step1, '/left', stepa);
      var step3 = rules.rewriteFrom(step2, '/main/right', stepb);
      // TODO: Consider whether this really needs to arrangeAsms
      //   explicitly.
      return (step3.andThen('arrangeAsms')
              .justify('makeConjunction', arguments, [a, b]));
    },
    inputs: {step: [1, 2]},
    // An approximation, good enough until we can remove this whole rule.
    toOffer: 'return step.isCall2("=>");',
    form: ('Conjoin steps <input name=step1> and <input name=step2>'),
    menu: '[h => p] and [h => q] to [h => p & q]',
    tooltip: ('Given a and b, derive a & b'),
    description: 'p & q;; using steps {step1}, {step2}'
  },

  // (5222) Given two theorems that are substitutions of T and
  // F respectively into a WFF, and a variable or variable name,
  // proves the WFF.
  //
  // TODO: Consider deriving this from equationCases.
  {name: 'casesTF',
    action: function(caseT, caseF, v) {
      v = varify(v);
      // Note: caseF has no variables not in caseT, so no need to
      // calculate all of its names.
      var newVar = Toy.genVar('v', caseT.allNames());
      var gen = caseT.generalizeTF(caseF, newVar);
      var step1a = rules.axiom4(call(lambda(newVar, gen), T));
      var step1b = rules.rRight(caseT, '', step1a);
      var step2a = rules.axiom4(call(lambda(newVar, gen), F));
      var step2b = rules.rRight(caseF, '', step2a);
      var step4 = rules.and(step1b, step2b);
      var step5 = rules.instVar(rules.axiom1(), lambda(newVar, gen), 'g');
      var step6 = rules.r1(step4, '', step5);
      var step7a = rules.instForall(step6, '', v);
      var step7b = rules.apply(step7a, '');
      return step7b.justify('casesTF', arguments, [caseT, caseF]);
    },
    inputs: {step: [1, 2], varName: 3},
    form: ('CasesTF: true case step <input name=step1>,'
           + ' false case <input name=step2>,'
           + ' use variable name <input name=varName>'),
    menu: 'proof by true/false cases',
    tooltip: ('Prove a theorem by cases given two theorems that'
              + ' show it with T and F.'),
    description: 'cases: {var} true in step {step1}, false in step {step2}'
  },

  // Given P and P => Q, derive Q. (5224)
  // TODO: Consider replacing all uses of this with trueBy0
  //   followed by removal of the "T".
  {name: 'modusPonens',
    action: function(a, b) {
      var step1 = rules.eqnSwap(rules.toTIsA(a));
      // Replace the "a" in "b" with T.
      var step2 = rules.r(step1, b, '/left');
      // Use a property of =>; carefully because this is used
      // before tautologies are available.
      var step3 = rules.rewriteOnly(step2, '/fn', '(=>) T = {y. y}');
      // From T => x derive x.
      var step4 = rules.reduce(step3, '');
      return step4.justify('modusPonens', arguments, arguments);
    },
    inputs: {step: 1, implication: 2},
    form: ('Modus ponens: premise step <input name=step>,'
           + ' implication in step <input name=implication>'),
    menu: 'modus ponens',
    tooltip: ('Modus Ponens.  Given A and A => B derives B.'),
    description: '[p] and [p &rArr; q] to q',
    labels: 'primitive'
  },

  // Note: Combined with substitution for x (and potentially p), this
  // can take the place of 5215 (universal instantiation) and
  // unForall.  To apply, match "forall p" with an existing
  // statement. Then "apply" p to user's choice of term.
  //
  // TODO: Move this proof near to its one use.  (It's hard to see
  //   how this fact is useful standing on its own given the way
  //   matching is done.)
  {name: 'r5225',
    statement: 'forall p => p x',
    proof: function() {
      var step1 = rules.axiom2();
      var map = {h: Toy.parse('{g. g x}'),
                 x: Toy.parse('{x. T}'),
                 y: Toy.parse('p')};
      var step2 = rules.instMultiVars(step1, map);
      var step2a = rules.eqnSwap(rules.definition('forall'));
      var step3 = rules.r(step2a, step2, '/left/fn');
      var step4 = rules.reduce(step3, '/right/left');
      var step5 = rules.reduce(step4, '/right/left');
      var step6 = rules.reduce(step5, '/right/right');
      // This could be changed into a rewrite.
      return rules.r(rules.r5218(Toy.parse('p x')), step6, '/right');
    }
  },

  // r5226 is r5225 with "p" and "x" instantiated, then beta conversion.

  // [not T] = F
  {name: 'r5231T',
    statement: 'not T == F',
    proof: function() {
      var step1 = rules.eqSelf(call('not', T));
      var step2 = rules.r(rules.definition('not'), step1, '/right/fn');
      return rules.r(rules.theorem('r5230FT_alternate'), step2, '/right');
    },
    tooltip: ('[not T] = F')
  },

  // [not F] = T
  {name: 'r5231F',
    statement: 'not F == T',
    proof: function() {
      var step1 = rules.eqSelf(call('not', F));
      var step2 = rules.r(rules.definition('not'), step1, '/right/fn');
      var step3 = rules.eqT(F);
      return rules.rRight(step2, '/right', step3);
    }
  },

  // Helper for evalBool, not in book.
  // [[F =] = not].
  {name: 'falseEquals',
    statement: '((==) F) == (not)',
    proof: function() {
      return rules.eqnSwap(rules.definition('not'));
    }
  },

  // Another helper for evalBool, not in book.
  // [[T =] = {x. x}].
  {name: 'trueEquals',
    statement: '((==) T) == {x. x}',
    proof: function() {
      var x = varify('x');
      var step1 = rules.r5218(x);
      var step2 = rules.eqSelf(Toy.parse('{x. x} x'));
      var step3 = rules.apply(step2, '/left');
      var step4 = rules.r(step3, step1, '/right');
      var step5 = rules.toForall0(step4, x);
      var step6 = rules.instVar(rules.axiom3(), equal(T), 'f');
      var step7 = rules.instVar(step6, '{x. x}', 'g');
      return rules.rRight(step5, '', step7);
    }
  },

  // Equates the given expression to a similar one where boolean terms
  // are reduced.  (These are calls to =, &, |, =>, or "not", and
  // lambda expressions, with an argument of T or F.)  Reduces
  // repeatedly until no subexpression can be reduced.
  //
  // TODO: Prove all the truth table facts and use them here.
  //
  // TODO: Implement this recursively for cleaner presentation of
  // results and greater efficiency.
  {name: 'boolSimp',
    action: function(data, expr) {
      const eqn = rules.equivSelf(expr);
      return (rules._simplifySite(eqn, '/right', data.simpFacts)
              .justify('boolSimp', [expr]));
    }.bind(null,
           {simpFacts: [
             'if T x y = x',
             'if F x y = y',
             'not F == T',
             'not T == F',
             // Fast simp facts for &, |, => perhaps right here.
             {apply: tryReduce},
             // It might be possible to get some speedup
             // by precomputing ground terms with these ops.
             '(==) = {x. {y. if x y (not y)}}',
             '(&) = {x. {y. if x y F}}',
             '(|) = {x. {y. if x T y}}',
             '(=>) = {x. {y. if x y T}}'
           ]}),
    // TODO: should be bool:.
    inputs: {term: 1},
    menu: 'simplify booleans',  
    form: 'Boolean term to simplify: <input name=term>',
    labels: 'uncommon',
    tooltip: ('simplify boolean'),
    description: 'simplify boolean value'
  },

  {name: 'evalBool',
    action: function(expr) {
      var boolOps = {'&': true, '|': true, '=>': true, '=': true, not: true};
      function isReducible(expr) {
        return (expr instanceof Toy.Call
                && ((expr.fn.isConst()
                     && boolOps[expr.fn.name]
                     && expr.arg.isConst()
                     && (expr.arg.name == 'T' || expr.arg.name == 'F'))
                    || expr.fn instanceof Toy.Lambda));
      }
      var result = rules.eqSelf(expr);
      while (true) {
        var right = result.getRight();
        var _path = right.pathTo(isReducible);
        if (_path == null) {
          return result.justify('evalBool', arguments);
        }
        var target = right.get(_path);
        var fn = target.fn;
        if (fn.isConst()) {
          var defn;
          const op = fn.name;
          const argName = target.arg.name;
          if (op == 'not') {
            defn = rules.theorem(argName == 'T'
                                 ? 'r5231T'
                                 : 'r5231F');
            result = rules.r(defn, result, '/right' + _path);
          } else if (op == '=') {
            // TODO: To avoid dependencies on trueEquals and
            //   falseEquals, we could break this down into
            //   all 4 cases.
            defn = rules.theorem(argName == 'T'
                                 ? 'trueEquals'
                                 : 'falseEquals');
            result = rules.r(defn, result, '/right' + _path);
          } else {
            // The op is "&", "|", or "=>".
            const fact = factForCase(op, argName);
            // No simplification can be needed here. These facts are
            // unconditional and applied on the RHS, so they don't
            // affect any assumptions.
            result = rules.rewriteOnly(result, '/right' + _path, fact);
          }
        } else if (fn instanceof Toy.Lambda) {
          result = rules.reduce(result, '/right' + _path);
        } else {
          assert(false, 'Unexpected expression: {1}', target);
        }
      }
    },
    inputs: {bool: 1},
    form: 'Boolean term to evaluate: <input name=bool>',
    labels: 'uncommon',
    tooltip: ('evaluate a boolean term'),
    description: 'calculate boolean value'
  },

  // Proves that the wff is a tautology and returns the proved
  // statement, else returns a LogicError.
  // (5233)
  //
  // Accepts a parseable string as the wff.
  {name: 'tautology',
    action: function(wff_arg) {
      const wff = termify(wff_arg);
      const key = '' + wff.dump();
      const details = _tautologies.get(key);
      let result;
      if (details) {
        result = details.justify('tautology', [wff]);
      } else {
        result = Toy.withExit(exit => {
          return Toy.rebind('tautExit', exit,
                            () => rules.tautology0(wff));
        });
      }
      if (Toy.isError(result)) {
        return new Error('Not a tautology: ' + wff_arg +
                         ' -- ' + result.message);
      } else {
        _tautologies.set(key, result.details);
        const str = wff.toString();
        const count = tautologyCounts.get(str);
        tautologyCounts.set(str, (count || 0) + 1);
      }
      return result;
    },
    inputs: {bool: 1},
    menu: 'prove a tautology',
    form: 'Enter tautology: <input name=bool size=40>',
    autoSimplify: noSimplify,
  },

  {name: 'tautology0',
    // This justifies its result as "tautology" rather than
    // tautology0, so this should be more like a helper function
    // than a rule on its own.  Also it builds a recursive tree
    // of justified proofs, so the proof display is a bit artificial.
    action: function(wff) {
      // TODO: Right here check for patterns such as -
      //   p | T == T, p & F == F, p => T == T, and negations such as
      //   p | not F = T and so on.
      //   Where these occur, this is an instance of a simpler tautology
      //   and need not be analyzed further.  In addition, forms such as
      //   p | F == T is equivalent to p == T along with similar examples,
      //   so this can be broken down into a smaller wff.
      // NOTE that saving proved tautologies as we already do has
      //   potential for accomplishing similar improvements, though it
      //   would work better if saved variable names were standardized.
      var taut = null;
      if (taut) {
        // Re-justify to create a new step.
        // Saved steps in _tautologies only keep details, for
        // nice displays.
        return taut.justify('tautology', arguments);
      } else {
        var names = wff.freeVars();
        // Not really a loop, just works with the first free (variable!)
        // name returned.
        for (var name in names) {
          if (wff instanceof Toy.Call && wff.fn instanceof Toy.Call
              && wff.fn.fn.isConst('=')) {
            // WFF is already an equation.
            var step1 = rules.tautology0(wff.subFree1(T, name));
            var step2 = rules.tautology0(wff.subFree1(F, name));
            var step3 = rules.equationCases(step1, step2, name);
            // Record before the final justification, so all occurrences
            // look the same when displayed.
            var result = step3.justify('tautology', arguments);
            return result;
          } else {
            var step1 = rules.tautology0(call('==', T, wff.subFree1(T, name)));
            var step2 = rules.tautology0(call('==', T, wff.subFree1(F, name)));
            var step3 = rules.equationCases(step1, step2, name);
            var step4 = rules.fromTIsA(step3);
            var result = step4.justify('tautology', arguments);
            return result;
          }
        }
        // There are no free variables, evaluate the expression.
        var step11 = rules.evalBool(wff);
        const success = step11.isCall2('=') && step11.getRight().isConst('T');
        if (!success) {
          const message = Toy.format('Not true: {1}',
                                     step11.getLeft(), step11);
          if (Toy.tautExit) {
            Toy.tautExit(Toy.logicError(message));
          } else {
            abort(message);
          }
        }
        var step12 = rules.rRight(rules.theorem('t'), '', step11);
        var result = step12.justify('tautology', arguments);
        return result;
      }
    },
    tooltip: ('Tautology decider.'),
    description: 'tautology'
  },

  /**
   * The boolean input should be an instance of a tautology.
   *
   * TODO: Complete with at least a precheck.  Consider what to do
   *   in case the argument is not an instance of a tautology.  Something
   *   like this could be useful as a test.
   */
  {name: 'tautologous',
    action: function(wff_arg) {
      const wff = termify(wff_arg);
      const info = Toy.boolSchemaInfo(wff);
      const tautWff = info.schema;
      const tautology = rules.tautology(tautWff);
      if (Toy.isError(tautology)) {
        return tautology;
      } else {
        const proved = rules.instMultiVars(tautology, info.subst);
        return proved.justify('tautologous', [wff_arg]);
      }
    },  
    inputs: {bool: 1},
    form: 'Enter statement: <input name=bool size=40>',
    menu: 'prove a tautology instance',
    tooltip: ('Tautology instantiator'),
    autoSimplify: noSimplify,
    description: 'tautology instance'
  },

  // Any instance of a tautology is a theorem.  This is part
  // of the book's Rule P.
  //
  // Given an expression that is a tautology and a substitution,
  // derives an instantiation of the tautology using the substitution.
  // The tautology can be given as a parseable string.
  //
  // TODO: Automatically detect the relevant tautology. 
  {name: 'tautInst',
    action: function(h_tautology_arg, map) {
      var tautology = termify(h_tautology_arg);
      var step1 = rules.tautology(tautology);
      return rules.instMultiVars(step1, map).justify('tautInst', arguments);
    },
    tooltip: ('substitute into tautology'),
    description: '=tautInst'
  },

  // TODO: Complete this.
  {name: 'simplifyBool',
    action: function(term) {
      if (term.findSubst('not x')) {
        if (term.arg.isBoolConst()) {
          var name = term.arg.name;
          if (name == 'T') {
            return rules.tautology('not T = F');
          } else {
            return rules.tautology('not F = F');
          }
        }
      }
      var simplifiers = {
        '&': {
          T: {
            T: 'T & T == T',
            F: 'T & F == F'
          },
          F: {
            T: 'F & T == F',
            F: 'F & F == F'
          }
        },
        '|': {
            T: 'T | T == T',
            F: 'T | F == T'
          },
          F: {
            T: 'F | T == T',
            F: 'F | F == F'
          },
        '=>': {
            T: 'T => T == T',
            F: 'T => F == F'
          },
          F: {
            T: 'F => T == T',
            F: 'F => F == T'
          },
        '=': {
            T: 'T = T == T',
            F: 'T = F == F'
          },
          F: {
            T: 'F = T == F',
            F: 'F = F == T'
          }
      };
      var boolOps = {'=': true, '&': true, '|': true, '=>': true};
      var op = term.getBinOp().name;
      if (term.isInfixCall() && boolOps.hasOwnProperty(op)) {
        var left = term.getLeft();
        var right = term.getRight();
        if (left.isBoolConst() && right.isBoolConst()) {
          return rules.tautology(simplifiers[op][left.name][right.name]);
        } else if (left.isBoolConst()) {
          return rules.tautology(leftSimplifiers[op][left.name]);
        } else {
          return rules.tautology(rightSimplifiers[op][right.name]);
        }
      }
    }
  }
);

/**
 * Supporting function for evalBool.  Given the name of a defined
 * boolean operator "&", "|", or "=>" and a string T or F, returns the
 * relevant fact for simplifying a call with that first argument by
 * simplifying an "if".
 */
function factForCase0(trueCases, falseCases, op, tf) {

  /**
   * This derives two facts for "&", "|", or "=>",
   * one for the true case and one for the false case, reducing the
   * outer lambda and simplifying any conditional within it.
   */
  function deriveCases(op) {
    const eqn = rules.definition(op);

    const t1 = rules.applyBoth(eqn, T);
    const t2 = rules.reduce(t1, '/right');
    const t3 = rules.rewriteOnly(t2, '/right/body', 'if T y z = y');
    Toy.addFact({goal: t3, desimplifier: true});
    trueCases.set(op, rules.fact(t3));

    const f1 = rules.applyBoth(eqn, F);
    const f2 = rules.reduce(f1, '/right');
    const f3 = rules.rewriteOnly(f2, '/right/body', 'if F y z = z');
    Toy.addFact({goal: f3, desimplifier: true});
    falseCases.set(op, rules.fact(f3));
  }

  if (trueCases.size == 0) {
    deriveCases('&');
    deriveCases('|');
    deriveCases('=>');
  }

  return tf == 'T' ? trueCases.get(op) : falseCases.get(op);
}
const factForCase = factForCase0.bind(null, new Map(), new Map());

declare(
  /**
   * Suppose the given statement to be true.  This is the standard way
   * to introduce an assumption into a proof.  If given a string,
   * parses it and uses the result.
   */
  {name: 'assume',
    action: function(assumption) {
      assumption = termify(assumption);
      const result = (rules.tautInst('a => a', {a: assumption})
                      .justify('assume', arguments));
      return result;
    },
    inputs: {bool: 1},
    form: ('Assume <input name=bool>'),
    menu: 'assume',
    tooltip: 'Statement to assume',
    description: 'assumption',
    labels: 'basic'
  },

  // Assume the target boolean term, like considerPart, but making it
  // an assumption.
  {name: 'assumePart',
    toOffer: 'return term.isBoolean()',
    action: function(step, path) {
      return rules.assume(step.get(path)).justify('assumePart', arguments);
    },
    inputs: {site: 1},
    menu: 'assume {term}',
    tooltip: ('assume term'),
    description: 'assume',
    labels: 'display'
  },

  /**
   * Suppose the given statement to be true.  The UI will display the
   * statement in each step where it occurs, even though it is among
   * the assumptions.
   */
  {name: 'assumeExplicitly',
    action: function(asm_arg) {
      var assumption = termify(asm_arg);
      var step = rules.tautInst('a => a', {a: assumption});
      return step.justify('assumeExplicitly', arguments);
    },
    inputs: {bool: 1},
    form: ('Assume <input name=bool>'),
    menu: 'assume temporarily',
    tooltip: 'Statement to assume (show occurrences)',
    description: 'temporary assumption',
    labels: 'basic'
  }

);

declare(
  // Deduces the conjunction of two proved steps.
  //
  // Introducing a T wherever desired, then substituting a theorem,
  // with or without assumptions, may be a more effective approach.
  // That appears to be to introduce T then use trueBy0.
  {name: 'and',
    action: function(step1, step2) {
      return (rules.replaceT0(rules.tautology('T & T'), '/right', step2)
              .andThen('replaceT0', '/left', step1)
              .justify('and', arguments, arguments));
    },
    inputs: {step: [1, 2]},
    form: ('Prove conjunction of step <input name=step1> ' +
           'and step <input name=step2>'),
    menu: '[p] and [q] to [p & q]',
    tooltip: ('Given [p] and [q], derive p & q'),
    description: 'p & q;; from steps {step1}, {step2}',
    labels: 'basic'
  },

  // Andrews' Rule P with two conjuncts.
  {name: 'p2',
    action: function(step1, step2, schema_arg) {
      var schema = rules.fact(schema_arg);
      var conj = rules.and(step1, step2);
      var result = rules.forwardChain(conj, schema);
      return result.justify('p2', arguments, [step1, step2]);
    },
    inputs: {step: [1, 2], bool: 3},
    labels: 'basic',
    menu: '[p] and [q] and [p & q => r] to [r]',
    form: ('Match step <input name=step1> and ' +
           'step <input name=step2> with left side of ' +
           'fact [p & q => r] <input name=bool>'),
    tooltip: ('[p] and [q] and [p & q => r] to [r]'),
    description: 'consequence;; of step {step1} and step {step2} using {bool}'
  },

  // Adds an assumption to the given step and deduplicates it.
  {name: 'andAssume',
    action: function(step, expr_arg) {
      var expr = termify(expr_arg);
      if (step.isCall2('=>')) {
        var taut = rules.tautology('(p => q) => (p & a => q)');
        var map = {p: step.getLeft(), q: step.getRight(), a: expr};
        var step1 = rules.tautInst(taut, map);
        var step2 = rules.modusPonens(step, step1);
      } else {
        var taut = rules.tautology('p => (a => p)');
        var map = {p: step, a: expr};
        var step1 = rules.tautInst(taut, map);
        var step2 = rules.modusPonens(step, step1);
      }
      var step3 = rules.arrangeAsms(step2);
      return step3.justify('andAssume', arguments, [step]);
    },
    inputs: {step: 1, bool: 2},
    form: ('Add assumption <input name=bool> in step <input name=step>'),
    menu: 'add assumption',
    labels: 'basic',
    description: 'add assumption {bool};; {in step step}'
  },

  // Given a RHS site that is the same as an assumption of the step,
  // converts the expression to T and simplifies out the T if it can.
  //
  // TODO: Consider whether we may want to detect and offer opportunities
  //   to use this rule in situations where an occurrence of the assumption
  //   is not explicitly selected.
  {name: 'assumed',
    precheck: function(step, path_arg) {
      const path = step.asPath(path_arg);
      if (!(step.isCall2('=>') && path.isRight())) {
        return false;
      } else {
        return step.asmSet().has(step.get(path));
      }
    },
    action: function(step, path_arg) {
      const path = step.asPath(path_arg);
      if (step.isCall2('=>') && path.isRight()) {
        const term = step.get(path);
        if (step.asmSet().has(term)) {
          const step1 = rules.assume(term);
          return (rules.trueBy1(step, path, step1)
                  // Crudely bludgeon out certain kinds of occurrences of T.
                  // Improve this with smart simplification.
                  .andThen('simplifySite', '/right', ['T & a == a', 'a & T == a'])
                  .justify('assumed', arguments, [step]));
        }
      }
    },
    inputs: {site: 1},
    menu: 'true by assumption',
    description: 'true by assumption'
  },

  // Given a variable v that is not free in the given wff A, and a wff B, derive
  // ((forall {v. A | B}) => A | (forall {v. B})).  Could run even if
  // the variable is free, but would not give desired result.
  // This is Axiom Schema 5 of Andrews' first-order logic F.
  //
  // NOTE: This is by the book; use implyForall or perhaps
  // toImplyForall in proofs!
  //
  // TODO: Prove a theorem schema for removing quantification over terms
  // that do not depend on the bound variable.  Something like:
  // {v. f A B} c = f A ({v. B} c) where v is not free in f or a.
  {name: 'r5235',
    action: function(v, a, b) {
      v = varify(v);
      var aFree = a.freeVars();
      assert(!aFree.hasOwnProperty(v.name),
             'r5235: variable {1} cannot occur free in {2}', v, a);
      var map1 = {
        p: call('forall', lambda(v, call('|', T, b))),
        q: call('forall', lambda(v, b))
      };
      var step1 = rules.tautInst('p => T | q', map1);
      var step2 = rules.tautInst('p => F | p',
                                 ({p: call('forall', lambda(v, b))}));
      var step3 = rules.tautInst('p == F | p',
                                 ({p: b}));
      var step4 = rules.r(step3, step2, '/left/arg/body');

      var freeNames = $.extend({}, aFree, b.freeVars());
      // Treat v as a free variable also.
      freeNames[v.name] = true;
      var p0 = Toy.genVar('p', freeNames);
      var step5 = rules.casesTF(step1, step4, p0);
      var step6 = rules.instVar(step5, a, p0);
      return step6.justify('r5235', arguments);
    },
    inputs: {varName: 1, bool: [2, 3]},
    /* Do not show, hard to use and seldom helpful.
    form: ('Variable: <input name=varName> '
           + 'wff without it free: <input name=bool1> '
           + 'other wff: <input name=bool2>'),
    */
    labels: 'uncommon',
    tooltip: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".'),
    description: 'move forall'
  },

  // Given a variable v that is not free in the given wff A, and a wff
  // B, derives ((forall {v. A => B}) == (A => forall {v. B})).  Could
  // run even if the variable is free, but would not give desired
  // result.
  //
  // When rewriting with implyForall does the beta reductions that are
  // here, this can probably go away.
  {name: 'implyForallGen',
    action: function(v, a_arg, b_arg) {
      var p = termify(a_arg);
      var q = lambda(v, termify(b_arg));
      var step1 = rules.implyForall();
      var step2 = (rules.instMultiVars(step1, {p: p, q: q})
                   .andThen('reduce', '/left/arg/body/right')
                   .andThen('reduce', '/right/right/arg/body'));
      return step2.justify('implyForallGen', arguments);
    },
    inputs: {varName: 1, bool: [2, 3]},
    form: ('Variable: <input name=varName> '
           + 'wff without it free: <input name=bool1> '
           + 'other wff: <input name=bool2>'),
    menu: 'forall {v. A => B} => (A => forall {v. B}',
    tooltip: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".'),
    description: 'move forall',
    labels: 'uncommon'
  },

  // 2104
  {name: 'r2104',
    statement: 'forall {x. p x => q x} => (forall p => forall q)',
    proof: function() {
      const fact1 = rules.fact('forall p => p x');
      const step1 = (fact1.andThen('instMultiVars', {p: '{x. p x => q x}'})
                     .andThen('reduce', '/right'));
      const step2 = (rules.p2(step1, fact1,
                              '(a => (b => c)) ∧ (d => b) => (a ∧ d => c)')
                     .andThen('toForall1', 'x')
                     .andThen('extractHyp', 'forall p'));
      return step2;
    }
  },

  {name: 'r2104a',
    statement: 'forall {x. p x => q x} => (exists p => exists q)',
    proof: function() {
      const contra = 'a => b == not b => not a';
      return (rules.r2104()
              .andThen('instMultiVars', {p: 'negate q', q: 'negate p'})
              // This is an interesting case of a rewrite in the
              // assumption, within a quantifier.
              .andThen('rewrite', '/left/arg/body', contra)
              .andThen('rewrite', '/right', contra)
              // TODO: Simplify with specific facts.
              .andThen('simplifySite', ''));
    }
  },

  // 2121
  //
  // NOTE: This and its converse both introduce specific bound variables.
  //
  // TODO: Consider extension of matching to associate actual ones
  //   with matched ones, including renaming of bound variables as
  //   potential parts of resulting substitutions.
  {name: 'forallXY',
    statement: 'forall {x. forall {y. p x y}} == forall {y. forall {x. p x y}}',
    proof: function() {
      const step1 = (rules.assume('forall {x. forall {y. p x y}}')
                     .andThen('instForall', '/right', 'x')
                     .andThen('instForall', '/right', 'y')
                     .andThen('toForall1', 'x')
                     .andThen('toForall1', 'y'));
      const step2 = (step1
                     .andThen('instVar', '{x. {y. p y x}}', 'p')
                     .andThen('reduceAll', ''));
      return rules.p2(step1, step2, '(a => b) & (b => a) => (a == b)');
    }
  },

  // 2122
  {name: 'existsXY',
    statement: 'exists {x. exists {y. p x y}} == exists {y. exists {x. p x y}}',
    proof: function() {
      const exAll = 'exists p == not (forall {x. not (p x)})';
      return (rules.consider('exists {x. exists {y. p x y}}')
              .andThen('simplifySite', '/right', [exAll])
              .andThen('rewrite', '/right/arg/arg/body',
                       'not (not p) == p')
              .andThen('rewrite', '/right/arg', rules.forallXY())
              .andThen('rewrite', '/right',
                       'not (forall p) == exists {x. not (p x)}')
              .andThen('simplifySite', '/right'));
    }
  },

  // Subsumes 2133
  {name: 'forallOrEquiv',
    statement: 'forall {x. p | q x} == (p | forall q)',
    proof: function() {
      var or = rules.tautology('T | a');
      var all = or.andThen('instVar', 'q x', 'a').andThen('toForall0', 'x');
      var and = rules.and(all, or.andThen('instVar', 'forall q', 'a'));
      var trueCase = rules.forwardChain(and, 'a & b => (a == b)');
      var falseCase = (rules.eqSelf('forall {x. q x}')
                       .andThen('rewrite', '/right/arg', rules.eta())
                       .andThen('rewriteOnly', '/right', 'p == F | p')
                       .andThen('rewriteOnly', '/left/arg/body', 'p == F | p'));
      return rules.casesTF(trueCase, falseCase, 'p');
    }
  },

  {name: 'existsEquivAnd',
    statement: 'exists {x. a & q x} == a & exists q',
    proof: function() {
      const facts = ['not (a | b) == not a & not b'];
      return (rules.fact('forallOrEquiv')
              .andThen('instMultiVars', {p: 'not a', q: 'negate q'})
              .andThen('rewrite', '', '(a == b) == (not a == not b)')
              .andThen('rewrite', '/left',
                       'not (forall p) == exists {x. not (p x)}')
              .andThen('simplifySite', '', facts.concat(basicSimpFacts)));
    }
  },

  // This is probably the most useful form of quantifier remover that
  // requires a variable to be not free.  It does not appear in the
  // book, but the numbered ones are corollaries of it.
  {name: 'implyForall',
    // Could this fact be used to help build Rule R'?
    statement: 'forall {x. p => q x} == (p => forall q)',
    proof: function() {
      var taut = 'not a | b == a => b';
      return (rules.forallOrEquiv()
              .andThen('instVar', 'not p', 'p')
              .andThen('rewriteOnly', '/right', taut)
              .andThen('rewriteOnly', '/left/arg/body', taut));
    }
  },

  // 2127
  {name: 'equivForall',
    statement: 'forall {x. p} == p',
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    proof: function() {
      var term = '{x. F} x';
      var falsity = (rules.forallXF()
                     .andThen('rewriteOnly', '', 'not a == (a == F)'));
      var step1 = rules.forallOrEquiv().andThen('instVar', '{x. F}', 'q');
      var step2 = rules.reduce(step1, step1.find(term));
      var step4 = rules.rewriteOnly(step2, '/right/right', falsity);
      var step5 = (step4.andThen('simplifySite', '/right')
                   .andThen('simplifySite', '/left/arg/body'));
      return step5;
    }
  },

  // 2128
  {name: 'equivExists',
    statement: 'exists {x. a} == a',
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    proof: function() {
      var step1 = (rules.equivForall().andThen('instVar', 'not a', 'p'));
      return (rules.applyToBoth('not', step1).andThen('simplifySite', ''));
    }
  },

  // 2129
  {name: 'forallAnd',
    statement: 'forall {x. p x & q x} == forall p & forall q',
    proof: function() {
      const andAB = (rules.fact('forall p => p x')
                     .andThen('instMultiVars', {p: '{x. p x & q x}'})
                     .andThen('reduce', '/right'));
      const a = rules.forwardChain(andAB, 'a => b & c => (a => b)');
      const b = rules.forwardChain(andAB, 'a => b & c => (a => c)');
      const fa = rules.toForall1(a, 'x');
      const fb = rules.toForall1(b, 'x');
      const fafb = rules.makeConjunction(fa, fb);

      const px = (rules.fact('a & b => a')
                  .andThen('instMultiVars', {a: 'forall p', b: 'forall q'})
                  .andThen('p2', rules.fact('forall p => p x'),
                           '(a => b) & (b => c) => (a => c)'));
      const qx = (rules.fact('a & b => b')
                  .andThen('instMultiVars', {a: 'forall p', b: 'forall q'})
                  .andThen('p2', rules.fact('forall q => q x'),
                           '(a => b) & (b => c) => (a => c)'));
      const fab = (rules.makeConjunction(px, qx)
                   .andThen('toForall1', 'x'));
      return rules.p2(fafb, fab, '(a => b) & (b => a) => (a == b)');
    }
  },

  // 2130
  {name: 'existsOr',
    statement: 'exists {x. p x | q x} == exists p | exists q',
    proof: function() {
      return (rules.forallAnd()
              .andThen('rewrite', '', 'a == b == (not a == not b)')
              .andThen('rewrite', '(p x & q x)', 'a & b == not (not a | not b)')
              .andThen('rewrite', '/left',
                       'not (forall {x. not (p x)}) == exists p')
              .andThen('rewrite', '/right', 'not (a & b) == not a | not b')
              .andThen('instMultiVars', {p: 'negate p', q: 'negate q'})
              .andThen('simplifySite', ''));
    }
  },

  // 2131 is by 2130 and 2128

  // 2132
  {name: 'forallOr',
    // TODO: Modernize statement and probably also proof, removing
    //   some {x. p x} and similar.
    statement: 'forall p | forall q => forall {x. p x | q x}',
    proof: function() {
      var step1 = rules.fact('forall p => p x');
      var step2 = rules.fact('forall q => q x');
      var step3 = rules.p2(step1, step2,
                           '(a => b) & (c => d) => (a | c => b | d)');
      var step4 = rules.toForall0(step3, 'x');
      var step5 = rules.rewriteOnly(step4, '', 'implyForall');
      return step5;
    }
  },

  // 2138
  {name: 'existsAnd',
    statement: 'exists {x. p x & q x} => exists p & exists q',
    proof: function() {
      const facts = [
       'not (a | b) == not a & not b'
       ];
      return (rules.forallOr()
              .andThen('instMultiVars', {p: 'negate p', q: 'negate q'})
              .andThen('rewriteOnly', '', 'a => b == not b => not a')
              // Note that this rewrites the assumption.
              .andThen('rewriteOnly', '/left',
                       'not (forall p) == exists {x. not (p x)}')
              // TODO: Simplify with a more specific set of facts,
              .andThen('simplifySite', '', facts.concat(basicSimpFacts)));
    }
  },

  // General TODOs:
  //
  // TODO: Consider asserting theorems until proof is requested.
  //

  // 2134.  This does almost all the work for the
  // "Exists rule" (2135, 5244).
  //
  // The LHS quantifier limits the "E rule" to usage where x is not
  // free in any assumptions, and since "q" appears with x bound,
  // substituting for it does not result in any new occurrences of x
  // within the "forall".
  //
  // TODO: Rename to something like forallIsExists.
  //
  // NOTE: The converse of this introduces a specific bound variable.
  //
  // TODO: For situations like the converse of this identity, when p
  //   is a lambda, use the name of its bound variable rather than
  //   the one in the statement here.
  {name: 'existImplies',
    statement: 'forall {x. p x => q} == (exists p => q)',
    proof: function() {
      var fact = 'not (forall {x. not (p x)}) == exists p';
      return (rules.implyForall()
              .andThen('instMultiVars', {p: 'not q', q: '{x. not (p x)}'})
              .andThen('apply', '/left/arg/body/right')
              .andThen('rewrite', '/right', 'not a => b == not b => a')
              .andThen('rewrite', '/left/arg/body',
                       'not a => not b == b => a')
              .andThen('rewrite', '/right/left', fact));
    }
  },

  // This removes an irrelevant assumption of the form <vbl> = <term>,
  // where the variable does not occur in the term nor elsewhere in
  // the step.  The arguments are a step and path to the assumption.
  //
  // TODO: Require an instance of the asm rather than a path.
  //
  // TODO: Generalize this into a rule for removal of irrelevant
  //   assumptions, based on a collection of predicates that "exist"
  //   and patterns for such predicates, e.g. {x. x = <term>} being
  //   such a predicate and x = <term> serving as the patten.
  //   Subsume removeLet and removeTypeAsm with that rule.
  {name: 'removeLet',
    precheck: function(step, path_arg) {
      var path = Toy.asPath(path_arg);
      const term = step.get(path);
      // This check is a little loose because it does not compare
      // the paths.  To do that, use prettyPathTo and compare strings.
      // But it is not clear just how useful that extra check is.
      if (!Array.from(step.asmMap().values()).includes(term)) {
        return false;
      }
      if (!term.isCall2('=')) {
        return false;
      }
      var vbl = term.getLeft();
      if (!vbl.isVariable()) {
        return false;
      }
      var val = term.getRight();
      if (vName in val.freeVars()) {
        return false;
      }
      var vName = vbl.name;
      var step1 = rules.extractHypAt(step, path);
      var map = step1.matchSchema('a => (b => c)');
      if (map) {
        var aFree = map.a.freeVars();
        var cFree = map.c.freeVars();
        if (!(vName in aFree || vName in cFree)) {
          return {extracted: step1, vName: vName, rewrite: true};
        }
      } else {
        var cFree = step.wff.getRight().freeVars();
        if (!(vName in cFree)) {
          return {extracted: step1, vName: vName, rewrite: false};
        }
      }
      return false;
    },
    action: function(step, path_arg) {
      var info = Toy._actionInfo;
      var path = Toy.asPath(path_arg);
      var step1 = info.extracted;
      var vName = info.vName;
      var asm = step.get(path);
      var step2 = (info.rewrite
                   ? rules.rewrite(step1, '', 'a => (b => c) == b => (a => c)')
                   : step1);
      var step3 = rules.toForall0(step2, vName);
      var equiv = rules.fact('forall {x. p x => q} == exists p => q');
      var step4 = rules.rewriteOnly(step3, '', equiv);
      var exists = (rules.fact('exists {y. y = x}')
                    .andThen('instVar', asm.getRight(), 'x'));
      var step5 = rules.trueBy0(step4, '/left', exists);
      var step6 = rules.arrangeAsms(step5);
      return step6.justify('removeLet', arguments, [step]);
    },
    inputs: {site: 1},
    labels: 'basic',
    form: (''),
    menu: 'remove irrelevant assumption',
    tooltip: 'Remove irrelevant assumption',
    description: 'remove irrelevant assumption {site};; {in step siteStep}'
  },

  // Removes an irrelevant type assumption of the form (R v) at the
  // target site, where v is a variable.  Currently only for predicate
  // R, but should be extended as needed.
  {name: 'removeTypeAsm',
    precheck: function(step, path_arg) {
      var path = Toy.asPath(path_arg);
      if (!(step.isCall2('=>') && path.isLeft())) {
        return false;
      }
      var term = step.get(path);
      var termMap = term.matchSchema('R v');
      if (!termMap || !termMap.v.isVariable()) {
        return false;
      }
      var step1 = rules.extractHypAt(step, path);
      var map = step1.matchSchema('a => (b => c)');
      var vName = termMap.v.name;
      if (map) {
        var aFree = map.a.freeVars();
        var cFree = map.c.freeVars();
        if (!(vName in aFree || vName in cFree)) {
          return {extracted: step1, vName: vName, rewrite: true};
        }
      } else {
        // The step had no other assumptions.
        var cFree = step.wff.getRight().freeVars();
        if (!(vName in cFree)) {
          return {extracted: step1, vName: vName, rewrite: false};
        }
      }
      return false;
    },
    action: function(step, path_arg) {
      var path = Toy.asPath(path_arg);
      var info = Toy._actionInfo;
      var step1 = info.extracted;
      var vName = info.vName;
      var asm = step.get(path);
      var step2 = (info.rewrite
                   ? rules.rewrite(step1, '', 'a => (b => c) == b => (a => c)')
                   : step1);
      var step3 = rules.toForall0(step2, vName);
      var equiv = rules.fact('forall {x. p x => q} == exists p => q');
      var step4 = rules.rewriteOnly(step3, '', equiv);
      var exists = rules.fact('exists R');
      var step5 = rules.trueBy0(step4, '/left', exists);
      var step6 = rules.rewrite(step5, '', 'T => x == x');
      return step6.justify('removeTypeAsm', arguments, [step]);
    },
    inputs: {site: 1},
    labels: 'basic',
    form: (''),
    menu: 'remove irrelevant type assumption',
    tooltip: 'Remove irrelevant type assumption',
    description: 'remove irrelevant type assumption {site};; {in step siteStep}'
  },

  // Rule P/Q for a single antecedent (5234).  The schema step must
  // have the form (A => B), where A matches the given input step.
  // This matches the step against A in the schema, and deduces the
  // appropriate instance of B.
  //
  // This version extends Andrews' version in that it universally
  // quantifies any (free) variables of B not also (free) in A, with
  // the quantified variables in lexicographic order by name, so the
  // instantiation always affects exactly the sites in the schema
  // where the variable originally occurred, and any renaming can be
  // recovered from the order of the quantifiers.
  //
  // Unlike Andrews' rule, there is no special handling here for
  // hypotheses.  Include them as antecedent of a conditional
  // in the schema.
  // 
  // For tautologies with a conjunction on the LHS as shown in the
  // book, use rule P2.  If there are more than two conjuncts, combine
  // combine them with rules.and before applying this rule to get
  // the full generality of Rule P.
  //
  // TODO: Apply a similar quantification strategy to rewriting, since
  // the same issues apply to rewrites.
  //
  // TODO: Remove support here for equivalences, and replace the
  // relevant occurrences of this rule with uses of rewriting.
  //
  // TODO: Consider merging this functionality with rules.trueBy.
  //
  // TODO: This rule is a specific useful case of "matchToRule",
  // because the substitution goes into the form A => B rather than
  // the theorem that A is to match.  Reimplement it when matchToRule
  // is available.
  {name: 'forwardChain',
    action: function(step, schema_arg) {
      var schema = rules.fact(schema_arg);
      var mainOp = schema.getBinOp().pname;
      var substitution = step.matchSchema(schema.getLeft());
      if (!substitution && (mainOp === '==' || mainOp === '=')) {
        // Allow RHS match in case schema is an equivalence.
        substitution = step.matchSchema(schema.getRight());
      }
      assert(substitution, 
             '{1} does not match LHS of schema\n{2}',
             step, schema);
      var unmapped = schema.unmappedVars(substitution);
      var schema2 = schema;
      // Variables first in unmapped are quantified first/outermost.
      while (unmapped.length) {
        // Currently only applied in the facts that the add/mul
        // identity elements are unique.
        schema2 = rules.toForall1(schema2, unmapped.pop());
      }
      // Schema2 may have some newly-quantified variables in its RHS.
      var step2 = rules.instMultiVars(schema2, substitution);
      var step3 = (mainOp === '=>'
                   ? rules.modusPonens(step, step2)
                   : assert(false, 'Schema must be like A => B or A == B'));
      // Schema is listed as a dependency here so it can be recognized
      // as a dependency, e.g. when rendering a proof.
      return step3.justify('forwardChain', [step, schema], [step]);
    },
    inputs: {step: 1, bool: 2},
    labels: 'basic',
    menu: 'forward chain',
    form: ('Match step <input name=step> with left side of ' +
           'fact [left => right] <input name=bool>'),
    tooltip: ('[p] and [p => q] to q'),
    description: 'consequence;; of step {step} using {bool}'
  },

  // TODO: Consider generalizing rule p2 and probably others to unify
  //   their arguments, not just compare or match a schema.  If p2 did
  //   unification, it could replace uses of this rule.  See for example
  //   addDefnFacts.

  // The step and fact arguments must both be conditional.  This
  // applies transitivity of the conditional operator, treating the
  // fact LHS as a schema to be matched with the step consequent.
  {name: 'forwardChain2',
    action: function(step, fact_arg) {
      var fact = rules.fact(fact_arg);
      var map1 = step.matchSchema('p => q0');
      assert(map1, 'Not a conditional: {1}', step);
      var map2 = fact.matchSchema('q1 => r');
      assert(map2, 'Not a conditional: {1}', fact);
      var map3 = map1.q0.matchSchema(map2.q1);
      assert(map3, '{1} does not match {2}', map1.q0, map2.q1);
      var step1 = rules.instMultiVars(fact, map3);
      var step2 = rules.p2(step, step1,
                           '(a => b) & (b => c) => (a => c)');
      // Caution: These are unusual justification args.
      return step2.justify('forwardChain2', [step, fact], [step]);
    },
    inputs: {step: 1, bool: 2},
    labels: 'basic',
    menu: "[p => q'] and fact [q => r] to [p => r']",
    form: ('Match conclusion of step <input name=step> with left side of ' +
           'fact [left => right] <input name=bool>'),
    tooltip: ('[p => q] and [q => r] to [p => r]'),
    description: 'consequence;; of step {step} using {bool}'
  },

  // Instantiates the schema theorem so that the part at the given
  // path is identical to the given term.
  //
  // TODO: Change "subgoal" to "expandRight"; create similar "expandLeft".
  {name: 'instantiate',
    action: function(schema, path, term) {
      var expr = schema.get(path);
      var subst = term.matchSchema(expr);
      assert(subst, 'Schema {1} should match {2}', expr, term);
      var result = rules.instMultiVars(schema, subst);
      return result.justify('instantiate', arguments, [schema]);
    }
  },

  // Finds a "subgoal" statement that implies the goal via the given
  // theorem, which must be a schema of the form a => b.
  // Instantiates the theorem by matching the goal against the theorem
  // RHS, returning the instantiated theorem.  Returns null if the
  // theorem does not match the goal.
  {name: 'subgoal',
    action: function(goal, theorem) {
      theorem.assertCall2('=>');
      var subst = goal.matchSchema(theorem.getRight());
      if (subst) {
        var result = rules.instMultiVars(theorem, subst);
        return result.justify('subgoal', arguments);
      } else {
        return null;
      }
    }
  },

  // Relates equal functions to equality at all input data points.
  {name: 'r5238',
    action: function(vars, a, b) {
      assert(Array.isArray(vars), 'Variables must be an array: {1}', vars);
      var result;
      if (vars.length == 0) {
        result = rules.eqSelf(equal(a, b));
      } else if (vars.length == 1) {
        result = rules.r5238a(vars[0], a, b);
      } else {
        var v = varify(vars[vars.length - 1]);
        var step1 = rules.r5238(vars.slice(0, -1),
                                lambda(v, a),
                                lambda(v, b));
        var step2 = rules.r5238a(v, a, b);
        var step3 = rules.r(step2, step1, '/right/arg/body');
        result = step3;
      }
      return result.justify('r5238', arguments);
    },
    // TODO: inputs: ... ?
    tooltip: ('Equal functions equate to equal expression values.')
  },

  // "Base case" of 5238, with just a single variable.
  // TODO: Consider whether it may make sense to replace usage of
  //   this with uses of r5238b.
  {name: 'r5238a',
    action: function(v, a, b) {
      v = varify(v);
      var step2 = rules.axiom3();
      var step3 = rules.instMultiVars(step2,
                               ({f: lambda(v, a),
                                 g: lambda(v, b)}));
      var step4 = rules.apply(step3, '/right/arg/body/left');
      var step5 = rules.apply(step4, '/right/arg/body/right');
      var step6 = rules.renameBound(step5, '/right/arg', v);
      // Do not "derive", leave this inline.
      return step6;
    },
    tooltip: ('')
  },

  // Base case of 5238 as a theorem.
  {name: 'r5238b',
    statement: '{x. f x} = {x. g x} == forall {x. f x = g x}',
    proof: function() {
      const eta2 = rules.eta().andThen('eqnSwap');
      return (rules.fact('f = g == forall {x. f x = g x}')
              .andThen('rewriteOnly', '/left/left', eta2)
              .andThen('rewriteOnly', '/left/right', eta2));
      //.andThen('instMultiVars', {f: '{x. f x}', g: '{x. g x}'})
      // .andThen('reduceAll', '/right'));
    }
  },

  // 5239, closely following the description and names in the book.
  // Analog to Rule R, expressed as an implication.  Theorem schema.
  //
  // Given a target wff C, a path relative to C, and an equation A = B,
  // proves a wff of the form "(forall ... A = B) => (C == D), where D
  // is obtained similarly to an application of Rule R to A = B and C.
  // The "forall" binds free variables of A = B that are bound at the
  // replacement location in C.
  //
  // Note that the target and the equation are merely formulas.  They
  // need not be proved or true statements.
  {name: 'r5239',
    action: function(target, path, equation) {
      path = target.asPath(path);
      assert(equation.isCall2('='),
             'Expecting an equation, got: {1}',
             equation);
      var step1 = rules.axiom2a();
      var a = equation.getLeft();
      var b = equation.getRight();
      var boundNames = target.boundNames(path);
      Toy.removeExcept(boundNames, equation.freeVars());
      // Is this the full set of names?
      var t = Toy.genVar('t', Object.assign({},
                                            target.allNames(),
                                            equation.allNames()));
      var texpr = t;
      for (var name in boundNames) {
        texpr = call(texpr, varify(name));
      }
      var aBound = a;
      var bBound = b;
      var boundNameList = [];
      for (var name in boundNames) {
        var v = varify(name);
        aBound = lambda(v, aBound);
        bBound = lambda(v, bBound);
        boundNameList.push(name);
      }
      var g = target.replaceAt(path, function(expr) { return texpr; });
      var step2 =
        rules.instMultiVars(step1,
                            ({x: aBound, y: bBound, p: lambda(t, g)}));
      var step3 = rules.apply(step2, '/right/left');
      var step4 = step3;
      for (var i = 0; i < boundNameList.length; i++) {
        step4 = rules.apply(step4, Toy.asPath('/right/left').concat(path));
      }
      var step5 = rules.apply(step4, '/right/right');
      var step6 = step5;
      for (var i = 0; i < boundNameList.length; i++) {
        step6 = rules.apply(step6, Toy.asPath('/right/right').concat(path));
      }
      if (boundNameList.length == 0) {
        return step6.justify('r5239', arguments);
      }
      var step7 = rules.r5238(boundNameList, a, b);
      var step8 = rules.r(step7, step6, '/left');
      return step8.justify('r5239', arguments);
    },
    // First arg is any equation, need not be proved.
    inputs: {bool: [1, 3], path: 2},
    form: ('Apply equation <input name=bool2> to <input name=bool1> at ' +
           '<input name=path>'),
    menu: 'prove A = B => (C == D) where D is C with an A replaced by B',
    labels: 'advanced',
    tooltip: ('Analog to Rule R, expressed as an implication.')
  },

  // Uses r5239 to prove C & (forall)(a = b) == D & (forall)(a = b)
  // where D is like C, but with an occurrence of "a" replaced, and
  // "(forall)" here indicates potential universal quantification of
  // some variables of (a = b).
  {name: 'r5239a',
    action: function r5239a(base, path, equation) {
      var step = rules.r5239(base, path, equation);
      var taut = rules.tautology('a => (b == c) == (b & a == c & a)');
      var subst = step.wff.matchSchema(taut.getLeft());
      var inst = rules.instMultiVars(taut, subst);
      var result = rules.r1(step, '', inst);
      return result.justify('r5239a', arguments);
    },
    // First arg is any equation, need not be proved.
    inputs: {bool: [1, 3], path: 2},
    form: ('Apply equation <input name=bool2> to <input name=bool1> at ' +
           '<input name=path>'),
    menu: 'prove (A = B) & C == (A = B) & D where D is C with an A replaced by B',
    labels: 'advanced',
    tooltip: ('Theorem generator used with simultaneous equations.')
  },

  // Not in Andrews' textbook
  //
  // This is the core rule for replacing terms in simultaneous equations.
  //
  // The target term must be part of a tree of conjuncts in the step
  // and the tree must also contain an equation with one side equal to
  // the target.  This replaces the target with the other side of that
  // equation.
  {name: 'replaceConjunct',
    // The basic idea of this rule is to apply the equivalence:
    // (t1 = t2 & A == t1 = t2 & A[t1 :1= t2]),
    // where t1 and t2 are terms, and t1 occurs in A with all of its
    // free variables also free there.  The :1= operator is like
    // substitution with :=, but replacing just one occurrence (not
    // specifying which occurrence).
    //
    // This function searches the ancestor nodes of the target
    // expression, seeking a conjunction that also has a suitable
    // equation ("eqn") as a descendant.  If none is found, the rule
    // fails.
    //
    // If the conjunction has the form (expr & eqn), this immediately
    // replaces the conjunction using r5239a and rule R, and we are
    // done.
    //
    // Otherwise it searches along the path from the conjunction to
    // the target for the nearest node that is not itself a conjunction.
    // (We will call this node the base.)
    //
    // Now it proves that the original conjunction is equivalent
    // to a version with the base replaced by (base & eqn).  Next it
    // shows this form of the conjunction is equivalent to a version
    // with (base' & eqn), where base' has the target replaced.  Then
    // it shows that form to be equivalent to a form with (base' & eqn)
    // replaced by just base'.  Finally it replaces the conjunction
    // using the last of these equivalences.
    //
    // TODO: Currently the equation's LHS must match the target.
    // Extend this rule to handle an equation with RHS matching the target.
    action: function replaceConjunct(step, path_arg) {
      var infixCall = Toy.infixCall;
      var wff = step.wff;
      var path = wff.asPath(path_arg);
      var prettyPath = wff.prettifyPath(path);
      // This will become the nearest ancestor of the target that is a
      // conjunction and has a suitable equation among its direct or
      // indirect conjuncts (which form a tree).
      var conjunction;
      // Ancestors of the target node, always non-empty, outermost
      // (i.e. wff) first.
      var ancestors = wff.ancestors(prettyPath);
      // The actual term to be replaced.
      var target = ancestors[ancestors.length - 1];
      // True iff the term is a "suitable equation" whose LHS matches
      // the target.
      function suitableEqn(term) {
        return term.isCall2('=') && term.getLeft().matches(target);
      }
      // This will become a "pretty" path from the conjunction to the
      // suitable equation below it.
      var eqnPath;
      var i;
      // Find the conjunction and eqnPath.
      for (i = ancestors.length - 1; i >= 0; --i) {
        var term = ancestors[i];
        if (term.isCall2('&')) {
          eqnPath =
            Toy.pathToConjunct(term, suitableEqn);
          if (eqnPath) {
            // Suitable conjunct is found.
            conjunction = term;
            break;
          }
        }
      }
      // ancestors[i] is now the conjunction.
      // Do a sanity check.
      assert(conjunction, 'No suitable conjunction found');
      // This is the equation that will be applied.
      var eqn = conjunction.get(eqnPath);
      // Path to the conjunction is a prefix of the target path.
      var toConjunction = path.firstN(i);

      if (eqnPath.toString() === '/right') {
        // This will equate the conjunction (base & eqn) with
        // another conjunction where the target is replaced.
        var equiv = rules.r5239a(conjunction.getLeft(),
                                 path.nth(i + 1), eqn);
        // Replaces the conjunction with a new conjunction.
        var result = rules.r1(step, toConjunction, equiv);
        // Done.
        return result.justify('replaceConjunct', arguments, [step]);
      }

      // Now find the base.
      var j;
      for (j = i + 1; j < ancestors.length; j++) {
        var term = ancestors[j];
        if (!term.isCall2('&')) {
          break;
        }
      }
      // This is the path from the conjunction to the base.
      var toBase = path.nth(i).firstN(j - i);
      var base = conjunction.get(toBase);
      var schema = Toy._conjunctionSchema(conjunction);
      var eqnVar = schema.get(eqnPath);
      var baseVar = schema.get(toBase);
      var rhs = schema.replaceAt(toBase, function(x) {
          return infixCall(baseVar, '&', eqnVar);
        });
      var schema1 = rules.tautology(infixCall(schema, '==', rhs));
      // Path from the base to the target.
      var fromBase = path.nth(j);
      var map1 = conjunction.matchSchema(schema);
      // Prove the conjunction is equivalent to its transform.
      var equiv1 = rules.tautInst(schema1, map1);
      // Prepare to replace the base part of the right side.
      var replacer1 = rules.r5239a(base, fromBase, eqn);
      // Conjunction is equivalent to its transform with target replaced.
      var equiv2 = rules.r1(equiv1, Toy.asPath('/right').concat(toBase),
                                 replacer1);
      // Reverse the transform on the RHS.
      var equiv3 = rules.rewriteOnly(equiv2, '/right',
                                     infixCall(rhs, '==', schema));
      var result = rules.r1(step, toConjunction, equiv3);
      return result.justify('replaceConjunct', arguments, [step]);
    },
    inputs: {site: 1},
    menuGen: function(ruleName, step, term) {
      if (step && term && term.isVariable()) {
        var wff = step.wff;
        var path = wff.prettyPathTo(term);
        var ancestors = wff.ancestors(path);
        var conjunction;
        var i;
        // Find the innermost conjunction containing the term, then
        // the innermost non-conjunction containing that.
        for (i = ancestors.length - 1; i >= 0; --i) {
          var node = ancestors[i];
          if (node.isCall2('&')) {
            conjunction = node;
          } else if (conjunction) {
            break;
          }
        }
        if (!conjunction) {
          return null;
        }
        var vname = term.name;
        var results = [];
        var terms = new Toy.TermSet();
        function add(term) {
          terms.add(term);
        }
        var format = Toy.format;
        // TODO: Use makeConjunctionSet there.
        var conjuncts = conjunction.scanConjuncts(add);
        if (terms.size() > 1) {
          // There are multiple conjunctions, so check for possible
          // replacements.
          function check(eqn) {
            if (eqn.isCall2('=') && eqn.getLeft().isVariable() &&
                eqn.getLeft().name === vname) {
              results.push(format('replace {1} with {2}',
                                  term.pname, eqn.getRight().toUnicode()));
            }
          }
          terms.each(check);
        }
        return results;
      }
    },
    tooltip: ('Replaces an occurrence of a term with an equal term'),
    description: 'replace {site};; {in step siteStep}',
    labels: 'algebra basic'
  },

  // Version of Andrews Rule R' that uses a conditional rather than
  // hypotheses.  Uses a potentially conditional equation to replace a
  // term in a target step.  Replaces the target as done by r1, and
  // describing the inputs as A => B = C, and D, produces a result
  // that is schematically A => D', where D' is like D, with an
  // occurrence of B replaced by C.
  //
  // The "replace" rule (below) also merges any assumptions of D with
  // the new assumptions A using arrangeAsms.
  {name: 'r2',
    action: function(target, path, equation) {
      assert(equation.isEquation(), 'Not an equation: {1}', equation);
      if (equation.isCall2('=')) {
        return rules.r(equation, target, path);
      }
      // The result of this has the form [h => (forall ... eq)],
      // same as LHS of step3; see below for h, eq and step3.
      function quantEquation() {
        var boundNames = target.boundNames(path);
        Toy.removeExcept(boundNames, equation.freeVars());
        var hypFreeNames = h.freeVars();
        const eqFreeNames = eq.freeVars();
        // Quantify over just the variables free in the equation and
        // bound at the target site.
        var quantEqn = equation;
        for (var name in boundNames) {
          // Check the variable is not free in assumptions and equation.
          // TODO: Do appropriate checking in 5235 and impliesForall as well.
          assert(!(name in hypFreeNames && name in eqFreeNames),
                 'Conflicting binding of {1} in {2}', name, target);
          quantEqn = rules.toForall1(quantEqn, name);
        }
        return quantEqn;
      }

      // Main body of the rule is here.
      // The equation is a conditional, eq is its pure equation part.
      var eq = equation.getRight();
      var h = equation.getLeft();
      var step1 = rules.r5239(target, path, eq);
      var step2a = rules.trueBy0(step1, '/right/left', target);
      var step2b = rules.rewriteOnly(step2a, '/right', '(T == p) == p');
      // quantEqn will be [(forall ... eq) => D], where D is the target
      // after replacement, and the quantifier binds no free vars of eq.
      const quantEqn = quantEquation();
      // Use the equation's assumptions as assumptions in place of
      // the equation itself.
      var step3 = rules.p2(quantEqn, step2b,
                           '(a => b) & (b => c) => (a => c)');
      return step3.justify('r2', arguments, [target, equation]);
    },
    inputs: {site: 1, equation: 3}, // plus further constraints
    form: ('Replace using equation <input name=equation>'),
    menu: 'replace minimally using a step like {term} = . . .',
    description: 'replace term;; {in step siteStep} {using step equation}',
    labels: 'primitive'
  },

  /**
   * Replaces the target term using the given equation.  If both
   * inputs are conditionals and this does not replace the entire
   * step, merges the resulting assumptions with arrangeAsms.
   */
  {name: 'replace',
    action: function(target, path, equation) {
      const step1 = rules.r2(target, path, equation);
      const step2 = (target.implies() && equation.implies() &&
                     !target.wff.asPath(path).isEnd()
                     ? (rules.rewriteOnly(step1, '',
                                          'a => (b => c) == a & b => c')
                        .andThen('arrangeAsms'))
                     : step1);
      return step2.justify('replace', arguments, [target, equation]);
    },
    inputs: {site: 1, equation: 3}, // plus further constraints
    form: ('Replace site with right side of equation <input name=equation>'),
    menu: 'replace using a step like {term} = . . .',
    description: 'replace term;; {in step siteStep} {using step equation}',
    labels: 'basic'
  },

  /**
   * Same as r1, but replaces an occurrence in target of the right
   * side of the equation with its left side.
   */
  {name: 'rRight',
    action: function(target, path, equation) {
      path = Toy.asPath(path);
      var rev = rules.eqnSwap(equation);
      var result = rules.r1(target, path, rev);
      return result.justify('rRight', arguments, [target, equation]);
    },
    inputs: {site: 1, equation: 3},
    form: ('Replace with left side of step <input name=equation>'),
    menu: 'replace using term like A = {term}',
    tooltip: ('Replaces an occurrence of a term with an equal term,'
              + ' replacing right side with left side.'),
    description: 'replace term;; {in step siteStep} {using step equation}',
    labels: 'uncommon'
  },

  // Given a step A, a path to its selected subexpression b, and an
  // equation step containing an equation of the form (b = c), this
  // proves (b = c => (B = B')), where B is either A, or if A is a
  // call to "==" or "=>", the appropriate top-level subexpression of
  // A, and B' is B with the referenced occurrence of b replaced by c.
  // If step B has the form C => D or C == D and the subexpression is
  // part of C or D, uses C or D as appropriate in place of B.  If the
  // equation step is an equivalence (or conditional), this uses its
  // RHS as the equation.
  //
  // Extracts subexpressions from the input steps, but does not need
  // either one to be proved; they just provide convenient access to
  // terms and parts of terms for application of r5239.
  //
  // This offers one approach to solving simultaneous equations,
  // in which the equations are in separate steps rather than
  // being conjoined.  Generally preferred now for practical
  // reasons is replaceConjunct.
  {name: 'replaceIsEquiv',
    action: function(step, path_arg, eqnStep) {
      var path = Toy.asPath(path_arg);
      var wff = step.wff;

      // A boolean part of the step:
      var targetWff = wff;
      // Path to the target, relative to targetWff:
      var targetPath = path;
      // TODO: "==" would be preferable to "=", but we can't ensure it
      // will be that here.
      if (wff.isCall2('=') || wff.isCall2('=>')) {
        targetWff = path.isLeft() ? wff.getLeft() : wff.getRight();
        targetPath = path.rest;
      }
      var target = targetWff.get(targetPath);

      var eqn;
      var eqnWff = eqnStep.wff;
      function test(term, pth) {
        if (term.isCall2('=') && term.getLeft().matches(target)) {
          return term;
        }
      }
      // searchMost finds the rightmost occurrence, which seems best.
      var eqn = eqnStep.searchMost(test);
      assert(eqn, 'Occurrence of {1} = ... not found', target.toUnicode());
      var result = rules.r5239(targetWff, targetPath, eqn);
      return result.justify('replaceIsEquiv', arguments, []);
    },
    inputs: {site: 1, equation: 3},
    form: ('Replace this using equation step <input name=equation>'),
    menu: 'replace giving equivalent',
    description: ('replace {site};; ' +
                  '{in step siteStep} {using step equation}'),
    labels: 'uncommon'
  },


  ////
  //// Rewriting -- beyond Andrews' textbook
  ////

  // Inline helper for rewriteOnly*.
  // If the step has the form a => (b => c), moves all conjuncts
  // of a to the inner level, erasing one level of "=>".
  {name: 'flattenAsms',
    action: function(step) {
      let flatter = step;
      const once = Toy.applyMatchingFact;
      const rw = rules.rewriteOnly;
      const mover = ['a1 & a2 => (b => c) == (a1 => (b & a2 => c))'];
      // This loop flattens out the assumptions.
      while (true) {
        let next = once(flatter, '', mover, 'rewriteOnly');
        if (!next) {
          // Mover made no progress. Remove a "=>" and quit.
          flatter = once(flatter, '',
		         ['a => (b => c) == (b & a => c)'],
		         'rewriteOnly');
          return flatter.justify('flattenAsms', arguments, [step]);
        }
        flatter = next;
      }
    }
  }
);

//// Rewriting

/** Currently commented out!

// TODO: Implement these, which refactor and extend existing
//   functionality.
//
// Write code to perform the operations implied by the return values.
// Use all of it for rewriting.

// Seeks a substitution into the given "rule" step, to potentially
// be followed by one or more beta reductions, that together make it
// match the target term so replacement can be applied to them using
// rules.replace.
//
// The target term is an arbitrary term at the given path within the
// WFF.  The rule term is a part of the rule argument as determined
// by our conventions for interpreting a fact as a rewrite rule.  If
// the rule is a (potentially conditional) equation or equivalence
// (often conditional), it is the LHS part.  Otherwise if the rule
// is conditional, it is the conclusion part, and in all other cases
// it is the entire step.  (In the last two cases, the target is
// rewritten to "T".)
//
// Note that the inputs are WFFs, not steps.
//
// If the match is unsuccessful this returns null.  If it finds
// suitable operations to make the match, this returns a plain
// object with properties:
//
// map: a substitution in the usual form.
//
// reduce: a Map with keys that are paths or path strings and values
// that are positive integers indicating the number of reductions to
// apply at that location.
//
function matchRuleTo(ruleWff, wff, path) {

}

// Like matchRuleTo, above, this seeks a substitution to match the
// target term and rule term (determined as above), but this one
// seeks a substitution into the target term rather than the rule
// term.  It also may do beta reduction after substitution as in
// matchRuleTo.
// 
// The target term may be within the scope of bound variables, and
// these constrain allowable substitutions here and also limit
// applicability of rules.replace.  The match process for this rule
// can include renaming of variables bound in the target.
//
// Note that the inputs are WFFs, not steps.
//
// Returns null if matching is unsuccessful.  On success returns a
// plain object with properties:
//
// map: a substitution in the usual form to be applied to the step
// containing the target term.
//
// reduce: a Map with keys that are paths or path strings and values
// that are positive integers indicating the number of reductions to
// apply at that location.
//
// rename: a substitution, possibly empty, that renames free variables
// of the rule to match names of bound variables of the wff, if needed
// to make the key terms match.
//
function matchToRule(wff, path, ruleWff) {

}
*/

// Interprets the equation argument as a potential rewriter for the
// part of the step at the given path, and determines a substitution
// to match it with that part of the step.  Returns the substitution,
// or null if it finds none.
function canRewrite(step, path, eqn_arg) {
  const expr = step.get(path);
  return expr.findSubst(Toy.schemaPart(eqn_arg));
}

declare(
  // Rewriters take a proof step, a path, and a proved step, typically
  // an equation.  Seeks a substitution into the equation that makes
  // the part of the step at the given path match to the LHS of the
  // equation.  Replaces that part of the step with the appropriate
  // instance of the equation.
  //
  // If the equation argument is not an equation according to
  // isEquation, they convert its main part to <main> = T and use that
  // as the equation.  To rewrite using an entire conditional "A => B"
  // (not just its main part), rewrite with the fact "(A => B) == T".
  //
  // TODO: Consider renaming _free_ variables introduced into the step
  //   by the equation so they are distinct from all free variables
  //   that were already in the equation.  Doing so would enable
  //   maximum flexibility in following substitutions, but can we
  //   then refer to the new variable(s) by some name?  Potentially
  //   add a utility to get the new name by referring to the step where
  //   it was introduced and the formula (e.g. step) it came from.
  //

  // Inline utility for all of the rewriters; proves an equation
  // whose LHS is the same as the part of step at path.
  {name: '_rewriterFor',
    action: function(step, path, eqn_arg) {
      const map = canRewrite(step, path, eqn_arg);
      if (!map) {
        abort('Fact not applicable: {1}', eqn_arg);
      }
      // Convert to an actual equation if necessary.
      var equation = (eqn_arg.isEquation()
                      ? eqn_arg
                      // Coerce to an equation.
                      : eqn_arg.andThen('rewriteOnly',
                                        '/main', 'a == (a == T)'));

      // TODO: Consider moving much of this below here to
      //   rules.matchTerm and using that here.
      let funSites = new Map();
      for (const key in map) {
        if (map[key] instanceof Lambda) {
          funSites.set(key, equation.locateFree(key));
        }
      }
      let simpler = rules.instMultiVars(equation, map);
      // Now (back)reduce applications of newly-substituted Lambda terms,
      // normally to just a variable, simplifying the result.
      //
      // TODO: Generate fixups while generating the substitution they
      //   are to follow; e.g. list of paths to backReduce, each with
      //   a count.
      funSites.forEach(function(rPaths) {
          rPaths.forEach(function (rPath) {
              for (let r = rPath; r.segment === 'fn'; r = r.rest) {
                // First time r refers to the lambda, then successive
                // parents as this does more reductions.  Could be
                // done more efficiently.
                const path = r.rest.reverse();
                const s = rules.backReduce(simpler, path);
                if (!s) {
                  break;
                }
                simpler = s;
              }
            });
        });

      // Uncomment these lines to restore afterMatch functionality:
      // const info = resolveToFactInfo(eqn_arg);
      // const after = (info && info.afterMatch) || function(x) { return x; };
      // simpler = after(simpler);
      return simpler;
    }
  },

  // Out of line version of _rewriterFor.
  //
  // TODO: Tentatively replace _rewriterFor with this, otherwise
  //   perhaps remove this.
  {name: 'substForRewrite',
    action: function(step, path, eqn) {
      return (rules._rewriterFor(step, path, eqn)
              .justify('substForRewrite', arguments, [step, eqn]));
    },
    inputs: {site: 1, equation: 3},
    form: ('Equation to rewrite the site using step <input name=equation>'),
    menu: 'rewriter for site',
    isRewriter: true,
    description: 'substitute;; {into step equation} {to rewrite step siteStep}',
    labels: 'uncommon'
  },

  // Minimal rewriter that does not simplify the assumptions resulting
  // from the substitution and replacement.  Only appends new
  // assumptions to existing ones; does not deduplicate or arrange
  // them.
  {name: 'rewriteOnlyFrom',
    action: function(step, path_arg, eqn) {
      const path = step.wff.asPath(path_arg);
      const rewriter = rules._rewriterFor(step, path, eqn);
      const rewritten = rules.r2(step, path, rewriter);
      let flatter = rewritten;
      if (step.implies() && eqn.implies() && !path.isEnd()) {
	flatter = rules.flattenAsms(rewritten);
      }
      return flatter.justify('rewriteOnlyFrom', arguments, [step, eqn]);
    },
    inputs: {site: 1, equation: 3},
    form: ('Rewrite using equation step <input name=equation>'),
    menu: 'minimal rewrite',
    isRewriter: true,
    description: 'rewrite;; {in step siteStep} {using step equation}'
  },

  // Minimal rewriter with no simplification; like rewriteOnlyFrom
  // except takes a fact statement rather than a step.
  {name: 'rewriteOnly',
    action: function(step, path_arg, stmt_arg) {
      const path = step.wff.asPath(path_arg);
      const statement = rules.fact(stmt_arg);
      const rewriter = rules._rewriterFor(step, path, statement);
      const rewritten = rules.r2(step, path, rewriter);
      let flatter = rewritten;
      if (step.implies() && statement.implies() && !path.isEnd()) {
	flatter = rules.flattenAsms(rewritten);
      }
      return flatter.justify('rewriteOnly', arguments, [step]);
    },
    inputs: {site: 1, bool: 3},
    form: ('(Primitive) rewrite {term} using fact <input name=bool>'),
    menu: 'primitive rewrite using a fact',
    isRewriter: true,
    description: 'use;; {shortFact} {&nbsp;in step siteStep}',
    labels: 'primitive'
  },

  // Variant of rules.rewrite for use from the UI when the equation
  // is a proof step, not a well-known fact; otherwise the same as
  // rules.rewrite.
  //
  // TODO: Render (programmatic) calls to this and "rewrite" according to
  //   whether the equation is a statement or a step.
  {name: 'rewriteFrom',
    action: function(step, path, equation) {
      // Can throw; tryRule will report any problem.
      const step2 = rules._rewriterFor(step, path, equation);
      const step3 = rules.replace(step, path, step2);
      const simpler = rules.simplifyAsms(step3);
      return simpler.justify('rewrite', arguments, [step, equation]);
    },
    inputs: {site: 1, equation: 3},
    form: ('Rewrite the site using step <input name=equation>'),
    menu: 'rewrite',
    isRewriter: true,
    // TODO: Consider modifying descriptions of rewrite rules to
    //   say "replace" rather than "rewrite" when the substitution
    //   is empty, perhaps with a new {rewrite} directive.
    description: 'rewrite;; {in step siteStep} {using step equation}',
    labels: 'basic'
  },

  // Version of the rewrite rule good for general use in code and for
  // indirect use in the UI with well-known facts.  (In the display
  // this does not give access to the proof of the fact.)  This does
  // trivial simplification of assumptions including numeric type
  // assumptions after rewriting.
  {name: 'rewrite',
    action: function(step, path, statement) {
      // Can throw; tryRule will report any problem.
      var fact = rules.fact(statement);
      const rewriter0 = rules._rewriterFor(step, path, fact);
      const rewriter = rules.simplifyAsms(rewriter0);
      const step2 = rules.replace(step, path, rewriter);
      var simpler = rules.simplifyAsms(step2);
      // Does not include the fact as a dependency, so it will not
      // display as a separate step.
      return simpler.justify('rewrite', arguments, [step]);
    },
    autoSimplify: function(step) {
      const inStep = step.ruleArgs[0];
      const path = step.ruleArgs[1];
      const stmt = step.ruleArgs[2];
      const info = resolveToFactInfo(stmt);
      if (info && info.autoSimplify) {
        const simp = info.autoSimplify;
        return simp(step);
      } else {
        if (Toy.isDistribFact(stmt)) {
          var step1 = rules.arrangeTerm(step, path.concat('/right'));
          var step2 = rules.arrangeTerm(step1, path.concat('/left'));
          var step3 = rules.simplifyFocalPart(step2);
          return step3;
        } else if (!(step.wff.isCall2('=>') && path.isLeft())) {
          // The left part may already be transformed,
          // and the target may not even exist.
          const info = resolveToFactInfo(stmt);
          return (info && info.desimplifier
                  ? step
                  : rules.simplifyFocalPart(step));
        }
      }
    },
    inputs: {site: 1, bool: 3},
    form: ('Rewrite {term} using fact <input name=bool>'),
    menu: 'rewrite using a fact',
    isRewriter: true,
    description: 'use;; {shortFact} {&nbsp;in step siteStep}'
  },

  // E-Rule (5244), specified by a step and name.  Checks first for
  // assumptions preceding a boolean term containing the variable,
  // then for a simple conditional with it in the antecedent.
  {name: 'eRule',
    precheck: function(step, name) {
      var map = (step.matchPattern('a => (p => q)')
                 || step.matchPattern('p => q'));
      // Returns the map if all preconditions are OK.
      return (map && (!map.a || !map.a.freeVars()[name]) &&
              map.p.freeVars()[name] &&
              !map.q.freeVars()[name] &&
              map);
    },
    action: function(step, name) {
      var map = Toy._actionInfo;
      if (map.a) {
        var qstep = rules.toForall1(step, name);
        return (rules.rewrite(qstep, '/main/left', rules.existImplies())
                .justify('eRule', arguments, [step]));
      } else {
        var qstep = rules.toForall0(step, name);
        return (rules.rewrite(qstep, '/main', rules.existImplies())
                .justify('eRule', arguments, [step]));
      }
    },
    inputs: {step: 1, varName: 2},
    form: ('In step <input name=step>, existentially quantify ' +
           '<input name=varName>'),
    menu: 'existentially quantify',
    tooltip: ('Existentially quantify antecedent'),
    description: '&exist; {var};; {in step step}'
  },

  // E-Rule (5244), specified by a step and a path to an occurrence of
  // a free variable.  The variable must occur free in a suitable part
  // of the step.
  {name: 'eRule2',
    precheck: function(step, path) {
      var v = step.get(path);
      var name = v.isVariable() && v.name;
      return rules.eRule.precheck(step, name);
    },
    action: function(step, path) {
      var name = step.get(path).name;
      // Note that this rule is currently inline.
      return rules.eRule(step, name);
    },
    inputs: {site: 1},
    menu: ('[A => B] to [&exist; A => B]'),
    tooltip: 'Existentially quantify antecedent',
    description: '&exist; {site};; {in step step}',
    labels: 'basic'
  },

  ////
  //// Conjunction management
  //// 

  // NOTE: A chain of conjuncts (or other binary operator) is an
  // expression that can be written a & b & ... & z.  An expression
  // that does not have the operator at top-level is a chain of one
  // conjunct.  A chain of two elements is of the form a & b, where a
  // itself is a chain.
  
  // Given a chain of at least two conjunctions, derives an equation
  // with the chain as LHS and RHS similar but with the rightmost
  // chain element bubbled into place in the RHS.  When the "less"
  // function returns true, its first argument should appear before
  // the second.
  //
  // While bubbling left, removes duplicates.
  {name: 'bubbleLeft',
    action: function(chain, less) {
      // This does all the work except the justification of the subproof.
      function bubble(eqn) {
        var expr = eqn.getRight();
        var a = expr.getLeft();
        var b = expr.getRight();
        // expr is a & b
        if (a.isCall2('&')) {
          // expr is a & b & c
          var c = b;
          b = a.getRight();
          a = a.getLeft();
          // Eqn is lhs = (a & b) & c
          if (b.matches(c)) {
            // RHS is a & b & b
            var simpler =
              rules.rewriteOnly(eqn, '/right',
                                rules.tautology('a & b & b == a & b'));
            // Keep bubbling the rightmost to the left.
            return bubble(simpler);
          } else if (less(c, b)) {
            // Replace the equation's RHS according using associativity.
            var assoc = rules.tautology('a & b & c == a & c & b');
            var map = expr.findSubst(assoc.getLeft());
            var assocInstance = rules.instMultiVars(assoc, map);
            var step1 = rules.r(assocInstance, eqn, '/right');
            // Then recursively bubble the C in A & C to its proper place.
            var step2 = rules.bubbleLeft(step1.get('/right/left'), less);
            // Replace the A & C in RHS of step1 with the result.
            var step3 = rules.r(step2, step1, '/right/left');
            // and replace the RHS of the argument with the final result.
            return step3;
          } else {
            // C is in place.
            return eqn;
          }
        } else {
          // Base case: Eqn is lhs = a & b.
          if (a.matches(b)) {
            return rules.rewriteOnly(eqn, '/right',
                                     rules.tautology('a & a == a'));
          } else if (less(b, a)) {
            return rules.rewriteOnly(eqn, '/right',
                                     rules.tautology('a & b == b & a'));
          } else {
            // B is properly placed.
            return eqn;
          }
        }
      }
      var equation = rules.eqSelf(chain, chain);
      var result = bubble(equation);
      return result.justify('bubbleLeft', arguments, [equation]);
    }
  },

  // Given an equation with RHS that is a conjunction of two chains of
  // conjunctions, derives an equation with the same LHS, but with the
  // last expression of the first chain moved to the end of the
  // second.  If the first chain has only one element, the result is
  // just the new second chain.
  {name: 'mergeRight',
    action: function(eqn) {
      var expr = eqn.getRight();
      // The merge step moves the last element of the left chain to
      // the end of the right chain.
      expr.assertCall2('&');
      var mover = (expr.getLeft().isCall2('&')
                   ? rules.tautology('(a & b) & c == a & (c & b)')
                   : rules.tautology('a & b == b & a'));
      var result = rules.rewriteOnly(eqn, '/right', mover);
      return result.justify('mergeRight', arguments, [eqn]);
    },
  },

  // Internal rule for conjunctionsMerger, with a comparator parameter.
  {name: 'mergeConj',
    action: function(expr, less) {
      expr.assertCall2('&');
      var eqn = rules.eqSelf(expr);
      if (expr.getRight().isCall2('&')) {
        // The right chain is nontrivial, combine the chains.
        while (eqn.getRight().getLeft().isCall2('&')) {
          // The left chain has at least 2 elements.
          var eqn1 = rules.mergeRight(eqn);
          var chain2 = eqn1.get('/right/right');
          var eqn3 = rules.bubbleLeft(chain2, less);
          eqn = rules.r(eqn3, eqn1, '/right/right');
        }
        // Always simplify at least once since the RHS is assumed to be
        // made of two chains.  This time the first chain will disappear
        // as its one element moves to the second chain.
        eqn = rules.mergeRight(eqn);
        var chain2 = eqn.getRight();
      } else {
        var chain2 = expr;
      }
      var eqn3 = rules.bubbleLeft(chain2, less);
      return rules.r(eqn3, eqn, '/right');
    },
  },

  // From a term that is a conjunction of two normalized chains of
  // conjunctions, derive an equation that has the input as its LHS
  // and as its RHS has conjuncts ordered by asmLess, with
  // duplicates eliminated.
  {name: 'conjunctionsMerger',
    action: function(expr) {
      // TODO: Consider whether this line needs to use Toy.hypIsless.
      var result = rules.mergeConj(expr, Toy.asmLess);
      return result.justify('conjunctionsMerger', arguments);
    },
    inputs: {bool: 1},
    // Too technical to expose for most users.
    // form: ('Conjunctions to merge: <input name=bool>'),
    menu: 'Derives an equation to merge chains of input conjunctions',
    description: 'merge conjunctions in {bool}'
  },    

  // Given a proof step of the form [a => b] and a path that refers to
  // an element "e" of a taken as a conjunction chain, derives a step
  // of the form [a' => (e => b)] where e is the referenced element,
  // and h' is h with all occurrences of "e" removed.
  //
  // If e is a, returns its input (or a copy?).
  //
  // TODO: Disallow this as unreliable.  Refer to it by its content.
  {name: 'extractHypAt',
    precheck: function(step, path_arg) {
      const path = Toy.asPath(path_arg);
      return step.wff.isCall2('=>') && path.isLeft();
    },
    action: function(step, path) {
      var result = rules.extractHyp(step, step.get(path));
      return result.justify('extractHypAt', arguments, [step]);
    },
    inputs: {site: 1},
    menu: 'extract the assumption',
    description: 'extract assumption;; {in step siteStep}',
    labels: 'basic'
  },

  // Like extractHypAt, accepting a term to be matched against the
  // assumptions Useful for pulling out implicit assumptions such as
  // variable types.
  //
  // TODO: Decide what to do if there is no such assumption.
  {name: 'extractHyp',
    action: function(step, hyp_arg) {
      var hyp = termify(hyp_arg);
      assert(step.isCall2('=>'));
      if (hyp.matches(step.getLeft())) {
        var result = step;
      } else {
        var taut = rules.tautology(step.getLeft().hypMover(hyp));
        var step1 = rules.rewriteOnly(step, '/left', taut);
        var taut2 = rules.tautology('a & b => c == a => (b => c)');
        var result = rules.rewriteOnly(step1, '', taut2);
      }
      return result.justify('extractHyp', arguments, [step]);
    },
    inputs: {step: 1, bool: 2},
    menu: 'extract an assumption',
    form: 'extract assumption <input name=bool> from step <input name=step>',
    description: 'extract assumption {bool};; {in step step}',
    labels: 'uncommon',
    tooltip: 'extract an assumption'
  },

  // Converts a => (b => c) to a & b => c.
  {name: 'asAssumption',
    precheck: function(step, path_arg) {
      const path = step.asPath(path_arg);
      return (step.matchSchema('a => (b => c)') &&
              step.wff.prettifyPath(path).toString() == '/right/left');
    },
    action: function(step, path) {
      var taut = rules.tautology('a => (b => c) == a & b => c');
      // TODO: Consider whether this code should "arrange" assumptions.
      var result = rules.rewriteOnly(step, '', taut);
      return result.justify('asAssumption', arguments, [step]);
    },
    inputs: {site: 1},
    menu: Toy.mathText('[a => (p => q)] to [a & p => q]'),
    labels: 'basic',
    description: 'use {site} as an assumption;; {in step siteStep}'
  },

  // Efficiently proves that the given chain of conjuncts imply the
  // specific conjunct "c", which must match one of them.  Proves
  // by cases on the truth of "c", where the T case is simple, and
  // the F case is proved by breaking down the chain into smaller
  // chains until the occurrence of "c" is found.
  //
  // TODO: At least simplify this to prove (and remember?) the
  // underlying tautology, and apply the tautology using tautInst.
  // Or generalize to lists of optionally negated disjuncts.
  {name: 'conjunctsImplyConjunct',
    action: function(conjuncts, c) {
      var infix = Toy.infixCall;
      var tautFX = rules.tautology('F & x == F');
      // Prove that "chain = F", where "chain" is a chain of conjuncts.
      // One conjunct must be "F".
      function falsify(hyps) {
        if (hyps.isCall2('&')) {
          if (hyps.getRight().matches(F)) {
            return rules.tautInst('p & F == F', {p: hyps.getLeft()});
          } else {
            var left = hyps.getLeft();
            var falsy = falsify(left);
            var eqn = rules.eqSelf(hyps);
            var step1 = rules.r1(eqn, '/right/left', falsy);
            return rules.rewriteOnly(step1, '/right', tautFX)
          }
        } else if (hyps.matches(F)) {
          return rules.eqSelf(F);
        }
        assert(false, 'Bad input to falsify!');
      }
      var map = new Toy.TermMap();
      conjuncts.scanConj(function (h) { map.addTerm(h); });
      assert(map.has(c), 
             'Must be one of the conjuncts: {1}', c);
      var cVar = map.get(c);
      // Make a schema for the desired theorem.
      var goalSchema = infix(buildHypSchema(conjuncts, map), '=>', cVar);
      // Make a version of the theorem with T for "c".
      var trueGoal = goalSchema.subFree1(T, cVar);
      // This is a simple tautology:
      var trueCase = rules.tautInst('p => T', {p: trueGoal.getLeft()});
      // Make a version of the theorem with F for "c".
      var falseGoal = goalSchema.subFree1(F, cVar);
      // Prove that its LHS is equal to F.
      var step1 = falsify(falseGoal.getLeft());
      // This means the LHS implies F, which is the desired F case.
      var taut = rules.tautology('p = F => (p => F)');
      var falseCase = rules.forwardChain(step1, taut);
      // This will be the desired tautology.
      var step2 = rules.casesTF(trueCase, falseCase, cVar);
      // Instantiate back to get the desired instance:
      var result = rules.instMultiVars(step2, map.subst);
      return result.justify('conjunctsImplyConjunct', arguments);
    }
  },

  // Treats conj as a tree of conjunctions.  Equates it with a
  // deduplicated and "linearized" version, omitting occurrences of T.
  // The result will conform to the ordering of terms defined by the
  // Array.sort comparator.
  {name: 'conjunctionArranger',
    // Implemented by building an appropriate equivalence tautology,
    // proving it with rules.tautology, and instantiating.
    //
    // TODO: The tautology could be proved in a number of proof steps
    //   quadratic in length of A.  For a list A of conjunctions,
    //   pre-prove [A => Ai] for each member of A, each taking time
    //   linear in length of A.  Use these to prove each conjunct
    //   separately, then build the equal list with rules.and.  Also
    //   prove in the opposite direction if desired.
    //
    //   Or perhaps even better, prove the desired tautology by by
    //   considering k+1 cases where k is the number of variables in
    //   the desired consequent.  The cases are those with one
    //   variable in the consequent being false, and one with them all
    //   true.  These cases each trivially simplify to true, and case
    //   analysis proves the whole thing true.
    action: function(conj, comparator) {
      var map = new Toy.TermMap();
      var infix = Toy.infixCall;
      function transform(term) {
        if (term.isCall2('&')) {
          return infix(transform(term.getLeft()), '&',
                       transform(term.getRight()));
        } else if (term.sameAs(T)) {
          // Return it without mapping it to a variable.
          return T;
        } else {
          return map.addTerm(term);
        }
      }
      var schema = transform(conj);

      // Create a list of the variables for terms that will go into the
      // RHS of the result equation, sorted by the desired ordering of
      // the terms themselves.
      
      function compare(a, b) {
        return comparator(a.value, b.value);
      }
      var keepTermsInfo = Toy.sortMap(map.subst, compare);
      // The desired list of variables:
      var keepTerms = keepTermsInfo.map(function(pair) { return pair.key; });
      var rewriter = Toy.infixCall(schema, '==',
                                   Toy.chainCall('&', keepTerms, T));
      var result = rules.instMultiVars(rules.tautology(rewriter), map.subst);
      return result.justify('conjunctionArranger', arguments);
    }
  },

  // Derives a step with assumptions deduplicated and ordered as by
  // asmComparator, including removal of occurrences of T.  In some
  // cases this can remove all assumptions and a top-level
  // conditional, and in that case the meanings of /main paths into
  // the step may not be as expected if the resulting step remains
  // conditional, though this is an exceptional case.
  //
  // TODO: Attempt to eliminate T by some other means where
  //   appropriate.
  //
  // TODO: Make this much faster by using sets of tautologies that
  //   show conjuncts imply a single one of its conjuncts, and using
  //   those to build the rearranged conjunction.
  {name: 'arrangeAsms',
    action: function(step) {
      if (!step.isCall2('=>')) {
        return step;
      }
      // conjunctionArranger also sorts assumptions, which we
      // currently expect to be done, and removes occurrences of T,
      // which is not exactly desired, but convenient to do there.
      // See TODOs there for some ideas.
      var deduper =
        rules.conjunctionArranger(step.getLeft(), Toy.asmComparator);
      const deduped = rules.r1(step, '/left', deduper);
      const result = (deduped.getLeft().isConst('T')
                      ? rules.rewriteOnly(deduped, '', '(T => a) == a')
                      : deduped);
      return result.justify('arrangeAsms', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    tooltip: 'remove redundant assumptions',
    description: 'arrange assumptions;; in step {step}',
    labels: 'uncommon'
  },

  // A simplifier that removes all lambda calls.
  {name: 'reduceAll',
   toOffer: function(step, term) {
     return term && term.search(x => x.isLambdaCall());
   },
   action: function(step, path) {
     return (rules.simplifySite(step, path, [{apply: tryReduce, pure: true}])
             .justify('reduceAll', arguments, [step]));
   },
   inputs: {site: 1},
   menu: 'reduce all function calls',
  },

  // Beta-reduce the lambda call at the given path.  If the argument
  // of the call is a variable bound in a containing scope, rename it
  // using rules.unbind.
  //
  // When used with substitution of lambdas for higher-order
  // variables, this treatment has the effect of preferentially using
  // the names in the substituted lambda, which tends to keep existing
  // variables in steps rewritten using quantifier laws.
  //
  // If no reduction is available, returns null.
  {name: 'backReduce',
    toOffer: function(step, term) {
      return term.isLambdaCall();
    },
    action: function(step, path_arg) {
      // TODO: Perhaps avoid finding the term twice here.
      const step1 = rules.unbind(step, path_arg);
      if (step1 !== step) {
        return step1.justify('backReduce', arguments, [step]);
      } else {
        const term = step.get(path_arg);
        if (term.isLambdaCall() && term.arg.isVariable()) {
          const step2 = rules.reduce(step, path_arg);
          return step2.justify('backReduce', arguments, [step]);
        }
      }
      return null;
    },
    inputs: {site: 1},
    menu: 'reduce with unbind',
    description: 'smart reduce'
  },

  // If possible, beta reduce the target term by renaming an outer
  // bound variable and leaving the body of the lambda alone.  If the
  // argument is an occurrence of a variable bound in a containing
  // scope, rename it to be the same or at least similar to the bound
  // variable of the lambda of the call before reducing.  The idea is
  // that this may effectively erase the lambda, retaining its body
  // as-is or at least looking very similar.  The bound variable of
  // the enclosing lambda takes its new name from the name of the
  // bound variable of the lambda in the call.
  //
  // If such a reduction is not available, returns the input step.
  {name: 'unbind',
    action: function(step, path_arg) {
      // This uses uglify to prepare the path for use in pathBindings.
      const path = step.wff.asPath(path_arg).uglify();
      const call = step.get(path);
      if (call instanceof Call &&
          call.fn instanceof Lambda &&
          call.arg.isVariable()) {
        const argName = call.arg.name;
        const bindings = step.pathBindings(path);
        // If non-null, this is the path to the lambda that
        // binds the variable at term.arg.
        const bindingPath = bindings.get(argName);
        if (bindingPath) {
          const desiredName = call.fn.bound.name;
          // Rename the bound var in the fact to the name that
          // was in the source step, then beta reduce.  This
          // reduction just erases the lambda, in other words
          // ({v. A} v) reduces to just A.
          return (rules.renameBound(step, bindingPath, desiredName)
                  .andThen('reduce', path)
                  .justify('unbind', arguments, [step]));
        }
      }
      // If not applicable just return the input step.
      return step;
    },
    inputs: {site: 1},
    menu: 'unbind',
    description: 'unbind'
  },

  // Prove an equation asserting that two chains of conjunctions are
  // equal by showing that their schemas are a tautology.
  {name: 'equalConjunctions',
    action: function(equation) {
      var termMap = new Toy.TermMap();
      var lhs = buildHypSchema(equation.getLeft(), termMap);
      var rhs = buildHypSchema(equation.getRight(), termMap);
      var taut = rules.tautology(Toy.infixCall(lhs, '=', rhs));
      return rules.tautInst(taut, termMap.subst);
    },
    inputs: {equation: 1},
    form: 'Equation of conjunctions: <input name=equation>',
    tooltip: 'prove equality of two chains of conjunctions',
    labels: 'uncommon'
  },

  ////
  //// From the section "Equality and descriptions" in the book.
  ////

  {name: 'equalitySymmetric',
    statement: '(x = y) == (y = x)',
    proof: function() {
      var x = varify('x');
      var y = varify('y');
      var step1 = rules.assume('x = y');
      var step2 = rules.eqSelf(x);
      // This use of replace is safe.
      var step3 = rules.replace(step2, '/left', step1);
      var subst = {x: y, y: x};
      var step5 = rules.instMultiVars(step3, subst);
      var step6 = rules.and(step3, step5);
      var taut = rules.tautology('(p => q) & (q => p) => (p == q)');
      return rules.forwardChain(step6, taut);
    },
    inputs: {},
    description: 'symmetry of equality',
    labels: 'algebra'
  },

  {name: 'equalityTransitive',
    statement: 'x = y & y = z => x = z',
    proof: function() {
      var step1 = rules.axiom2();
      var step2 = rules.instVar(step1, Toy.parse('{t. t = z}'), varify('h'));
      var step3 = rules.apply(step2, '/right/left');
      var step4 = rules.apply(step3, '/right/right');
      var taut = rules.tautology('(a => (b = c)) => (a & c => b)');
      return rules.forwardChain(step4, taut);
    },
    inputs: {},
    description: 'transitivity of equality',
    labels: 'basic'
  },

  // Proves an equation that can replace the given boolean term.
  // Applies itself recursively to the given list of equational facts,
  // descending into the arguments of conjunctions (a & b), bottom-up,
  // applying the first fact (if any) that succeeds to each
  // subexpression.  Returns an equation with the given term on the
  // LHS and the replacement on the right.  The facts currently must
  // be pure equations.
  //
  // TODO: This is unused; remove?
  // TODO: Extend to take a conversion function in place of the facts.
  {name: 'conjunctsSimplifier',
    action: function(term, facts) {
      // A pure equation. 
      var step = rules.equivSelf(term);
      var step1;
      if (term.isCall2('&')) {
        var stepLeft = rules.conjunctsSimplifier(term.getLeft(), facts);
        var stepRight = rules.conjunctsSimplifier(term.getRight(), facts);
        step1 = (rules.r1(step, '/right/left', stepLeft)
                 .andThen('r1', '/right/right', stepRight));
      } else {
        step1 = step;
      }
      const result1 = (Toy.applyMatchingFact(step1, '/right', facts,
                                             'rewriteOnly') ||
                       step1);
      const taut = 'a & (b & c) == a & b & c';
      const result2 = (Toy.applyMatchingFact(result1, '/right', [taut],
                                             'rewriteOnly') ||
                       result1);
      return result2.justify('conjunctsSimplifier', arguments);
    }
  },

  // If the given statement is a proved step, returns the input.
  // Otherwise if the statement is a string, parses it with mathParse
  // into a wff.  If the wff matches a recorded fact, permitting
  // changes of variable names, it proves it from the fact by changing
  // variable names, and returns the proved result.
  //
  // If the above conditions do not apply, attempts to prove the wff
  // as a tautology or simple arithmetic fact.  Removes any " = T"
  // from boolean-valued arithmetic facts.  Programmatic usage
  // supports theorems by name, but not the UI.
  //
  // For tautologies, proved statements, and theorems in particular,
  // this rule is inline.
  {name: 'fact',
    action: function(synopsis) {
      // Check if the synopsis string has already resulted in a proved
      // fact with suitable variable names.
      //
      // TODO: Consider upgrading _factMap to an actual Map, or using
      //   mathParse and resolveToFactInfo here, then removing it.
      if (typeof synopsis === 'string') {
        if (Toy.isIdentifier(synopsis)) {
          const result = Toy.getTheorem(synopsis);
          if (result) {
            // Behavior is inline.
            return result;
          }
        }
        var proved = _factMap[synopsis];
        if (proved) {
          // In this case the the argument is the statement
          // and the result is the proved step.
          return proved.justify('fact', arguments);
        }
      }
      if (Toy.isProved(synopsis)) {
        // Argument is an already proved statement.
        // Behavior of "fact" is inline.
        return synopsis;
      }
      // Currently rules.fact parses any string synopsis
      // with mathParse.
      const wff = mathParse(synopsis);
      const factInfo = resolveToFactInfo(wff);
      // Try ordinary proved facts.
      if (factInfo) {
        var fact = Toy.getResult(factInfo.goal);
        // TODO: Try to compute the map more efficiently by
        //   factoring out computation of the map from factExpansion.
        const expansion = Toy.factExpansion(synopsis);
        // Maps free variables of the fact into ones given here.
        const map = expansion.getMain().matchSchema(fact.getMain());
        const instance = rules.instMultiVars(fact, map);
        // Remember the proof for future reference.
        ((typeof synopsis === 'string') && (_factMap[synopsis] = instance));
        // Justify the final result in each usage of the fact.
        return instance.justify('fact', arguments);
      }
      // Next try arithmetic facts.
      if (wff.isEquation()) {
        var result = Toy.tryArithmetic(wff.eqnLeft());
        if (result && result.alphaMatch(wff)) {
          return result.justify('fact', arguments);
        }
      } else {
        // Relational operators can go here.
        var result = Toy.tryArithmetic(wff);
        // x = T is the expected result.
        if (result && result.matchSchema('x = T')) {
          return (rules.rewriteOnly(result, '', '(x = T) = x')
                  .justify('fact', arguments));
        }
      }
      // Try tautologies.
      try {
        // Inline for tautologies.  Call looksBoolean to avoid ugly
        // and unnecessary errors from rules.tautology.
        return (Toy.looksBoolean(wff)
                ? rules.tautology(wff)
                : abort(''));
      } catch(err) {}  // TODO: Consider returning a strict error
      //                    from rules.tautology.
      return Toy.newError('No such fact: ' + wff + ' (as ' + synopsis + ')');
    },
    // The "fact" rule does not accept a selection, and converts its
    // form input as needed.  
    inputs: {string: 1},
    form: ('Look up fact <input name=string size=40>'),
    autoSimplify: noSimplify,
    menu: 'look up a fact',
    tooltip: (''),
    description: function(step) {
      var info = resolveToFactInfo(step.ruleArgs[0]);
      var d = info && info.description;
      return d || 'fact';
    },
    labels: 'basic'
  },

  // Traditionally in lambda calculus (use of) this is referred to as
  // "eta conversion".
  {name: 'eta',
    statement: '{x. p x} = p',
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    proof: function() {
      // fact1 is: forall {x. {x. p x} x = p x}
      var fact1 = rules.axiom4('{x. p x} x').andThen('toForall0', 'x');
      // fact2 is: <fact1> == {x. p x} = p
      var fact2 = (rules.axiom3()
                   .andThen('eqnSwap')
                   .andThen('instMultiVars', {f: '{x. p x}', g: 'p'}));
      return rules.r(fact2, fact1, '');
    },
    // When used as a simplifier, this seems to interact badly in some
    // cases with higher-order matching.  An example is proving andExists
    // with assertFacts == false.
    // simplifier: true,
    description: 'eta conversion'
  }
);

// This fact states the truth table for ==.  At present the
// proof display for it shows proofs of facts for rows in the truth
// table that use tautologies, but all of those facts are proved
// in this file without using truth tables.
declare
    ({statement: '(==) = {a. {b. if a b (not b)}}',
      proof:
      [
       `(1 given
         (t (forall {a. (forall {b. ((a == b) == ((if a b) (not b)))})})))`,
       `(2 rewrite (s 1) (path "/main/right/arg/body")
         (t ((forall {a. (g a)}) == ((g T) & (g F)))))`,
       `(3 rewrite (s 2) (path "/main/right")
         (t ((forall {a. (g a)}) == ((g T) & (g F)))))`,
       `(4 reduceAll (s 3) (path "/main/right"))`,
       `(5 rewrite (s 4) (path "/main/right/right/right/right")
         (t (((if F x) y) = y)))`,
       `(6 rewrite (s 5) (path "/main/right/right/right/right")
         (t ((not F) == T)))`,
       `(7 rewrite (s 6) (path "/main/right/right/left/right")
         (t (((if F x) y) = y)))`,
       `(8 rewrite (s 7) (path "/main/right/right/left/right")
         (t ((not T) == F)))`,
       `(9 rewrite (s 8) (path "/main/right/left/right/right")
         (t (((if T x) y) = x)))`,
       `(10 rewrite (s 9) (path "/main/right/left/left/right")
         (t (((if T x) y) = x)))`,
       `(11 fact "x = x == T")`,
       `(12 fact "T == F == F")`,
       `(13 fact "F == T == F")`,
       `(14 instantiateVar (s 11) (path "/main/left/left") (t T))`,
       `(15 instantiateVar (s 11) (path "/main/left/left") (t F))`,
       `(16 trueBy0 (s 10) (path "/main/right/right/right") (s 15))`,
       `(17 trueBy0 (s 16) (path "/main/right/right/left") (s 13))`,
       `(18 trueBy0 (s 17) (path "/main/right/left/right") (s 12))`,
       `(19 trueBy0 (s 18) (path "/main/right/left/left") (s 14))`,
       `(20 simplifySiteWith (s 19) (path "/main/right") (t ((T & T) == T)))`,
       `(21 rewrite (s 20) (path "") (t ((x == T) == x)))`,
       `(22 rewrite (s 21) (path "/main/arg/body")
         (t ((forall {x. ((f x) = (g x))}) == (f = g))))`,
       `(23 rewrite (s 22) (path "/main")
         (t ((forall {x. ((f x) = (g x))}) == (f = g))))`
      ]});
  
declare(
   // Derive exists {x. p x} from a witnessing term.  This only replaces the
   // selected occurrence, not substituting throughout. (5242)
   {name: 'witnessExists',
    precheck: function(step, path) {
      var term = step.get(path);
      var type = Toy.findType(term);
      // The current check merely excludes booleans.
      // TODO: Improve this when types are truly available.  Support
      //   predicates and functions of individuals, et cetera.
      // TODO: Also screen out terms with locally free occurrences
      //   of variables bound in an enclosing scope.
      return type !== Toy.boolean;
    },
    action: function(step, path_arg) {
      var path = step.asPath(path_arg);
      var term = step.get(path);
      var v = step.wff.freshVar('x');
      function replacer(term) { return v; }
      var replaced = step.wff.replaceAt(path, replacer);
      var test = Toy.lambda(v, replaced);
      var eqn = rules.axiom4(call(test, term));
      assert(eqn.getRight().matches(step.wff));
      // This is the step, converted to be application of predicate to term.
      var step2 = rules.r(rules.eqnSwap(eqn), step, '');
      var fact = rules.fact('p x => exists p');
      var result = rules.forwardChain(step2, fact);
      return result.justify('witnessExists', arguments, [step]);
    },
    inputs: {site: 1},
    menu: "A to &exist; x. A'",
    description: 'existentially quantify',
    labels: 'basic'
   },

   // 5304
   {name: 'exists1b',
    statement: 'exists1 p == exists {x. p = {y. y = x}}',
    proof: function() {
       return (rules.equivSelf('exists1 p')
               .andThen('apply', '/right'));
     }
   },

   // 5305
   {name: 'r5305',
    statement: 'exists1 p == exists {x. forall {y. p y == y = x}}',
    proof: function() {
       const step1 = rules.exists1b();
       const step2 = rules.rewriteOnly(step1, '/right/arg/body',
                                       rules.axiom3a());
       return step2;
     }
   },

   // Useful for showing a constant is unique, thus the "c" in the name.
   // 5306
   {name: 'exists1c',
    statement: 'exists1 p == exists {y. p y & forall {z. p z => z = y}}',
    proof: function() {
      const step1 = rules.r5305();
      const step2 = rules.rewrite(step1, '/right/arg/body/arg/body',
                                  '(a == b) == (a => b) & (b => a)');
      const step3 = rules.rewrite(step2, '/right/arg/body', 'forallAnd');
      const step4 = (rules.axiom2a()
                     .andThen('forwardChain',
                              '(a => (b == c)) => (a => b == a => c)'));
      const rw = rules.rewriteOnlyFrom;
      // Note that the result has no assumptions for rw to change.
      const step5 = rw(step3, '/main/right/arg/body/right/arg/body', step4);
      const step6 = rules.axiom4('{y. y = x} y').andThen('eqnSwap');
      // Note: no assumptions in the equation.
      const step7 = rules.r1(step5,
                             '/main/right/arg/body/right/arg/body/left',
                             step6);
      const step8 = rules.rewriteOnly(step5,
                                      '/main/right/arg/body/right',
                                      'existImplies');
      const step10 = rules.fact('exists {y. y = x}');
      const step11 = (rules.trueBy0(step8, '/main/right/arg/body/right/left',
                                   step10)
                      .andThen('simplifySite', ''));
      return rules.rewriteOnly(step11, '/main/right/arg/body',
                               'a & b == b & a');
     }
  },

   // From unique existence for p conclude an equivalence with "the"
   // (the1) for all x.
   //
   // Simplified statement of 5312.
   // Or use exists1TheLaw, which uses "the" in place of "the1".
   {name: 'exists1Law',
    statement: 'exists1 p => (p x == x = the1 p)',
    proof:
    [
     `(1 assume (t (p = {x. (x = y)})))
     (2 axiom5)
     (3 rewrite (s 1) (path "/right") (t ((x = y) == (y = x))))
     (4 rewriteFrom (s 2) (path "/main/left/arg") (s 3))
     (5 rewrite (s 4) (path "/right") (t ((x = y) == (y = x))))
     (6 rewriteFrom (s 1) (path "/right/right/body/right") (s 5))
     (7 rewrite (s 6) (path "/right")
        (t ((p = q) == (forall {x. ((p x) == (q x))}))))
     (8 instForall (s 7) (path "/right") (t x))
     (9 toForall0 (s 8) "y")
     (10 rewrite (s 9) (path "/main")
         (t ((forall {x. ((p x) => q)}) == ((exists p) => q))))
     (11 rewrite (s 10) (path "/left")
         (t ((exists {x. (p = {y. (y = x)})}) = (exists1 p))))`
     ]
   },

   {name: 'exists1TheLaw',
    statement: 'exists1 p => (p x == x = the p)',
    proof: function() {
      return (rules.fact('exists1 p => (p x == x = the1 p)')
              // This rewrite does merge the assumptions.
              .andThen('rewrite', '/right/right/right',
                       'exists1 p => the1 p = the p'));
    }
   },

   {name: 'inverseFunLaw',
    statement: 'v = the1 p & exists1 p => (p x == x = v)',
    proof: function() {
       const asm = rules.assume('the1 p = v');
       return (rules.fact('exists1 p => (p x == x = the1 p)')
               .andThen('rewriteFrom', 'the1 p', asm)
               .andThen('rewrite', 'the1 p = v', 'x = y == y = x'));
     }
   },

   // Convenient corollary that uses a typical definition of an inverse
   // function and a suitable unique existence predicate to show the
   // usual property of the inverse function.  The E! predicate is
   // generally conditional on some assumptions that limit its
   // applicability.
   {name: 'inverseFunLaw_old',
    statement: 'f x = the1 (Q x) & exists1 (Q x) => (Q x y == f x = y)',
    proof: [
      '(1 exists1Law)',
      '(2 instantiateVar (s 1) (path "/right/right/left") (t y))',
      '(3 assume (t ((the1 p) = (f x))))',
      '(4 rewriteFrom (s 2) (path "/right/right/right") (s 3))',
      '(5 rewrite (s 4) (path "/left/left") (t ((x = y) == (y = x))))',
      '(6 rewrite (s 5) (path "/right/right") (t ((x = y) == (y = x))))',
      '(7 display (s 6))',
      '(8 instantiateVar (s 7) (path "/left/left/right/arg") (t (Q x)))'
    ]
   },

  // This theorem aids in proving that a constant defined by a
  // property is unique.
   {name: 'uniqueTerm',
    statement: 'p x & forall {y. p y => y = x} => exists1 p',
    proof: function() {
      const eqn = rules.exists1c().andThen('eqnSwap');
      const map = {p: '{y. p y & forall {x. p x => x = y}}'};
      return (rules.fact('p x => exists p')
              .andThen('instMultiVars', map)
              .andThen('rewriteOnlyFrom', '/right', eqn)
              .andThen('reduce', '/left'));
    }
  },

   /* TODO: Remove these two as not very useful.
   {name: 'ifTrue',
    statement: 'c => if c x y = x',
    proof:function() {
      var assumed = rules.assume('T == c');
      var fact = rules.fact('if T x y = x');
      return (fact.andThen('r1', fact.find('T'), assumed)
              .andThen('rewriteOnly', '/left', 'T == x == x'));
    }
   },

   {name: 'ifFalse',
    statement: 'not c => if c x y = y',
    proof:function() {
      var assumed = rules.assume('F == c');
      var fact = rules.fact('if F x y = y');
      return (fact.andThen('r1', fact.find('F'), assumed)
              .andThen('rewriteOnly', '/left', 'F == x == (not x)'));
    }
   },
  */

   {name: 'exists1The',
    statement: 'exists1 p => the1 p = the p',
    proof: function() {
       var assumed = rules.assume('exists1 p');
       var step1 = rules.fact('the p = if (exists1 p) (the1 p) none');
       var loc1 = step1.find('exists1 p');
       return (step1.andThen('trueBy1', loc1, assumed)
               .rewrite('/right/right', 'if T x y = x')
               .andThen('eqnSwap'));
     }
   }
);


//// LOGIC FACTS

// The fact information is organized with the synopsis as
// a map key to take advantage of debug printing of the functions
// in the Chrome debugger.

declare(
   {statement: '(T == a) == a',
    simplifier: true,
    proof: function() {
       return rules.theorem('tIsXIsX');
     }
   },
   {statement: '(a == T) == a',
    simplifier: true,
    proof: function() {
      var step1 = rules.theorem('r5230FT_alternate');
      var step2 = rules.eqT(T);
      var step3 = rules.eqnSwap(step2);
      return rules.equationCases(step3, step1, 'x');
     }
   },

   // Somewhat useful fact to stick at the end of the list.
   {statement: 'not F',
    proof: function() {
       return rules.tautology('not F');
     }
   },

   {statement: '(T => a) == a',
    simplifier: true,
    proof: function() {
       return rules.tautology('(T => a) == a');
     }
   },

   {statement: '(a != b) == not (a = b)',
    proof: function() {
       return (rules.eqSelf('a != b')
               .andThen('useDefinition', '/right')
               .andThen('apply', '/right/fn')
               .andThen('apply', '/right'));
     }
   },

   {statement: 'x != y == y != x',
    proof: function() {
       return (rules.equivSelf('x != y')
               .andThen('rewrite', '/right', '(a != b) == not (a = b)')
               .andThen('rewrite', 'x = y', 'x = y == y = x')
               .andThen('rewrite', '/right', 'not (a = b) == a != b'));
     }
   },

   {statement: 'not (a != b) == (a = b)',
    simplifier: true,
    proof: function() {
       return (rules.fact('a != b == not (a = b)')
               .rewrite('', 'a == b == (not a == not b)')
               .andThen('simplifySite', '/right'));
     }
   },

   {statement: 'T == (x = x)',
    desimplifier: true,
    proof: function() {
       return rules.eqT('x');
     }
   },

   {statement: 'ident x = x',
    simplifier: true,
    proof: function() {
       return (rules.eqSelf('ident x')
               .andThen('useDefinition', '/right/fn')
               .andThen('reduce', '/right'));
     }
   },

   {statement: 'negate p = {x. not (p x)}',
    proof: function() {
       return (rules.consider('negate p').andThen('apply', '/right'));
     }
   },

   {statement: 'negate (negate p) = p',
    simplifier: true,
    proof: function() {
       return (rules.consider('(negate (negate p)) x')
               .andThen('simplifySite', '/right')
               .andThen('toForall0', 'x')
               .andThen('rewrite', '',
                        'forall {x. q x == p x} == (q = p)'));
     }
   },

   {statement: '(negate p) x == not (p x)',
    simplifier: true,
    proof: function() {
       return (rules.consider('(negate p) x')
               .andThen('apply', '/right/fn')
               .andThen('apply', '/right'));
     }
   },

   // This is the classic definition of the existential quantifier,
   // proved from a concise definition.  We could have based the
   // definition directly off of this.
   {name: 'existDef',
    statement: 'exists p == not (forall {x. not (p x)})',
    proof: function() {
       var all = (rules.axiom3()
                  .andThen('instMultiVars', {f: 'p', g: '{x. F}'})
                  .andThen('apply', '/right/arg/body/right')
                  .rewrite('/right/arg/body', '(a == F) == (not a)'));
       return (rules.eqSelf('exists p')
               .andThen('useDefinition', '/right/fn')
               .andThen('apply', '/right')
               .rewrite('/right', 'x != y == not (x = y)')
               .andThen('rewriteOnlyFrom', '/right/arg', all));
     },
    labels: 'generalMode',
    desimplifier: true
   },

   {statement: 'not (exists p) == forall {x. not (p x)}',
    proof: function() {
       return (rules.fact('exists p == not (forall {x. not (p x)})')
               .andThen('rewriteOnly', '', 'a == b == (not a == not b)')
               .andThen('simplifySite', '/right'));
     }
   },

   // TODO: Consider if uses of "negate" like this might better use
   //   {x. not (p x)} instead, and if p is a lambda, propagate its
   //   bound variable upward to the binding of x, thus retaining a
   //   name that appeared in the use of this fact.
   {statement: 'exists p == not (forall (negate p))',
    proof: function() {
       return (rules.fact('exists p == not (forall {x. not (p x)})')
               .andThen('rewriteOnly', '/right/arg/arg',
                        '{x. not (p x)} = negate p'));
     },
    desimplifier: true
   },

   // TODO: QM: Eta expand "p".
   {statement: 'exists {x. not (p x)} == not (forall p)',
    proof: function() {
       var step1 = (rules.fact('exists p == not (forall {x. not (p x)})')
                    .andThen('instMultiVars', {p: 'negate p'})
                    .andThen('rewriteOnly', '/left/arg', 'negate p = {x. not (p x)}'));
       var loc1 = step1.find('negate p x');
       return (step1.andThen('rewriteOnly', loc1, 'negate p x = not (p x)')
               .andThen('simplifySite', '/right/arg')
               .andThen('rewriteOnly', '/right/arg/arg', '{x. p x} = p'));
     }
   },

   // This has the core reasoning for 5242, existential generalization
   // (EGen / witnessExists / 2126).
   //
   // TODO: Consider adding a rule that converts an arbitrary step with
   //   selected term to an application of a lambda to the selected term.
   //   The code for that is in witnessExists.
   //
   // TODO: Consider for each of the above, a rule that replaces
   //   another occurrence of the same term with the new bound
   //   variable.  For existential quantification, the rule may need to
   //   look at the step from which the selected one is derived, to
   //   determine whether it is such an occurrence.
   {statement: 'p x => exists p',
    proof: function() {
       return (rules.r5225()
               .andThen('instVar', '{x. not (p x)}', 'p')
               .andThen('reduce', '/right')
               .andThen('rewriteOnly', '',
                        'a => not b == b => not a')
               .andThen('rewriteOnly', '/right',
                        'not (forall {x. not (p x)}) == exists p'));
     }
   },

   {statement: 'exists {y. y = x}',
    proof: function() {
       return (rules.fact('p x => exists p')
               .andThen('instVar', '{y. y = x}', 'p')
               .andThen('reduce', '/left')
               .andThen('simplifySite', ''));
     }
   },

   {statement: 'exists {y. x = y}',
    proof: function() {
       // This could be derived from the previous, but here is a nice
       // alternative proof.
       return (rules.eqSelf('x')
               .andThen('forwardChain', 'p x => exists p')
               .andThen('rewriteOnly', '/arg', 'p = {x. p x}'));
     }
   }
);

declare(
   {statement: 'not (multi p) == forall {x. forall {y. p x & p y => x = y}}',
    name: 'notMulti',
    proof: function() {
       const notEx = 'not (exists p) == forall {x. not (p x)}';
       return (rules.consider('not (multi p)')
               .andThen('apply', '/right/arg')
               .andThen('rewrite', '/right', notEx)
               .andThen('rewrite', '/right/arg/body', notEx)
               .andThen('rewrite', '/right/arg/body/arg/body',
                        'not (a & b) == a => not b')
               .andThen('simplifySite', '/right'));
     }
   },
   // This is an equivalent formulation of unique existence, directly
   // comparable to eu2 in Metamath.  The proof is somewhat lengthy, see
   // the proofs of eu2 and mo in Metamath.
   {name: 'exists1a',  // TODO: Prove this.
    statement: 'exists1 p == exists p & not (multi p)'
   },
   {statement: 'exists1 p => exists p',
    proof: function() {
       return (rules.theorem('exists1a')
               .andThen('forwardChain', '(a == b & c) => (a => b)'));
     }
   },
   {statement: 'exists1 p => not (multi p)',
    proof: function() {
       return (rules.theorem('exists1a')
               .andThen('forwardChain', '(a == b & c) => (a => c)'));
     }
   }
);

definition('intersect = {p. {q. {x. ((p x) & (q x))}}}');
definition('subclass = {p. {q. (forall {x. ((p x) => (q x))})}}');

declare(
   {statement: '((subclass p q) = (p = (intersect p q)))',
    name: 'SubclassInter',
    proof: [
            '(1 fact "subclass p q = forall{x. p x => q x}")',
            '(2 rewrite (s 1) (path "/main/right/arg/body") (t ((a => b) == (a == (a & b)))))',
            '(3 fact "(p x & q x) = intersect p q x")',
            '(4 rewriteOnlyFrom (s 2) (path "/main/right/arg/body/right") (s 3))',
            '(5 fact "forall {x. p x == q x} == p = q")',
            '(6 instantiateVar (s 5) (path "/main/right/right") (t (intersect p q)))',
            '(7 rewriteOnlyFrom (s 4) (path "/main/right") (s 6))'
            ]
   }
);

//// Other initializations

// Make defn facts available and stop deferring their proofs.
Toy.enableDefnFacts();


//// EXPORT NAMES

const tautologyCounts = Toy.tautologyCounts = new Map();

Toy.asmSimplifiers = ['a & T == a', 'T & a == a'];
Toy.simplifyStep = simplifyStep;
Toy.canRewrite = canRewrite;

}();
