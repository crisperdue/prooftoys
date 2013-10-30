// Copyright 2011, 2012, 2013 Crispin Perdue.  All rights reserved.

// Set all of this up immediately upon load, but avoiding changes
// to the global environment (except through the "Toy" namespace).
(function() {

//// THEOREMS AND RULES

var assert = Toy.assertTrue;

//  Make some useful names available here.
var assertEqn = Toy.assertEqn;
var varify = Toy.varify;
var call = Toy.call;
var equal = Toy.equal;
var implies = Toy.implies;
var lambda = Toy.lambda;

var Expr = Toy.Expr;
var Var = Toy.Var;
var Call = Toy.Call;
var Lambda = Toy.lambda;

var memo = Toy.memo;

// Include all variables that appear in axioms, plus common constants.
var f = varify('f');
var g = varify('g');
var h = varify('h');
var x = varify('x');
var y = varify('y');

var T = varify('T');
var F = varify('F');
var zero = Toy.parse('0');
var one = Toy.parse('1');
var identity = lambda(x, x);
var allT = lambda(x, T);

// Map from tautology string representation to tautology,
// for proved tautologies.  Private to the tautology rule.
var _tautologies = {};

// All hypotheses in a map keyed by textual representation from
// "dump".  Private to rules.assume and findHyp.
// Representation should probably ignore names of bound variables.
// TODO: Consider changing the rep accordingly.
var _allHyps = {};

// Map from inference rule name to a JavaScript function that
// implements it.  The functions may use a global variable
// named "rules" that should have all of these functions in it.
// Properties here for each name are:
//
// action: function implementing the inference rule.
// inputs: map from type to argument number(s), either a single
//   number or an array if more than one such argument.
// form: HTML template for the rule's input form to be presented
//   by the step editor.
// hint: plain text for the hint to be displayed by the autocompleter
//   of the step editor.
// comment: plain text comment to become the title of mentions of the rule
//   name in proof displays and the description in subproof displays.
// result: For theorems with no parameters only; this is the statement
//   of the theorem.  If given as text in ruleInfo, converted into an
//   expression in "rules".
// description: HTML word or phrase to display for the rule name.
// isRewriter: true to highlight on hover like a rewrite rule.
//   TODO: Consider removing this as unnecessary.
// using: if present, normally the equation or implication used for
//   the rule, as for rewriters.  The equation may have conditions.
//   When working forward the left side of the main equation must
//   match the site to be operated on.
// inputSide: may be 'right' to indicate that the rule uses
//   the converse equality (rewrites matching the right side of the
//   equation rather than the left side).
//

// Conventions for menu items (using "hint:")
// Step templates are in square brackets, such as [T = A].
// Rules (including axiom 4) that take a term as input use A, B to
//   show where the term goes, not enclosed in square brackets.

var ruleInfo = {

  /**
   * The name "assertion" is used in displays to indicate that
   * the result of the inference is an assertion.  If given a string,
   * parses it and uses the result as its input.
   */
  assert: {
    action: function(assertion) {
      if (typeof assertion == 'string') {
	assertion = Toy.parse(assertion);
      }
      return assertion.justify('assert', [assertion]);
    },
    inputs: {term: 1},
    form: ('Assert <input name=term>'),
    hint: 'assert without proof',
    labels: 'advanced',
    description: 'assert',
    comment: 'WFF to assert (possibly to prove later)'
  },

  define: {
    action: function(name, definition) {
      return Toy.define(name, definition).justify('define', arguments);
    },
    inputs: {varName: 1, term: 2},
    form: ('Define name <input name=varName> as <input name=term>'),
    labels: 'uncommon',
    description: 'define {var}',
    comment: 'create a simple definition'
  },

  /**
   * Suppose the given expression to be true.  This is the standard
   * way to introduce hypotheses into proofs.  If given a string,
   * parses it and uses the result.  Automatically assumes variables
   * used as input to "math operations" are real numbers.
   *
   * TODO: Enable users to disable the automatic real number assumptions.
   */
  assume: {
    action: function(assumption) {
      if (typeof assumption == 'string') {
	assumption = Toy.parse(assumption);
      }
      var types = assumption.mathVarConditions();
      // TODO: Fix tautInst to not copy.
      if (types) {
        var step1 = rules.tautInst('h & a ==> a', {
            a: assumption,
            h: types
          });
        var step = rules.dedupeHyps(step1);
      } else {
        var step = rules.tautInst('a ==> a', {a: assumption});
      }
      // Flag the step as one with hypotheses, and record this step as
      // the source of the assumption.
      var result = step.asHyps().justify('assume', arguments);
      assumption.sourceStep = result;
      _allHyps[assumption.dump()] = assumption;
      return result;
    },
    inputs: {term: 1},
    form: ('Assume <input name=term>'),
    hint: 'assume hypothetically',
    comment: 'Hypothesis to assume',
    description: 'assumption',
    labels: 'basic'
  },

  copy: {
    action: function(step) {
      return step.dup().justify('copy', arguments, [step]);
    },
    inputs: {step: 1},
    description: 'copy;; {of step step}'
  },

  /**
   * From an implication with LHS consisting of a set of hypotheses,
   * derives the equivalent step with the hypotheses.
   */
  asHypotheses: {
    action: function(step) {
      step.assertCall2('==>');
      // Use dup to prevent "justify" from getting input identical
      // to "step".
      var result = step.dup().justify('asHypotheses', arguments, [step]);
      result.hasHyps = true;
      return result;
    },
    inputs: {implication: 1},
    form: ('Convert implication to hypotheses in step '
           + '<input name=implication>'),
    hint: 'assumptions implicit',
    description: 'assumptions implicit;; {in step implication}',
  },

  /**
   * Converts a wff with hypotheses to an implication.  If there are
   * no hypotheses, returns its input unchanged.
   */
  asImplication: {
    action: function(step) {
      // Use dup to prevent "justify" from getting input identical
      // to "step".
      var result = step.dup().justify('asImplication', arguments, [step]);
      result.hasHyps = false;
      return result;
    },
    inputs: {step: 1},
    form: ('Convert hypotheses to explicit implication in step '
           + '<input name=step>'),
    comment: 'assumptions explicit',
    description: ';;explicit assumptions {in step step}',
    labels: 'algebra basic'
  },

  /**
   * A no-op step that breaks the cycle of displaying with elision.
   */
  display: {
    action: function(step) {
      // Call copyStep to persuade Expr.justify not to entirely
      // ignore this step.
      return step.copyStep().justify('display', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Does nothing, but result will display in full. '
           + '<input name=step>'),
    comment: 'show full equation',
    description: 'show full equation;; {in step step}',
    labels: 'display basic'
  },
      
  /**
   * Refer to a theorem by looking it up in the database rather
   * than proving it all over again.
   */
  theorem: function(name) {
    // See the "axiom" rule for explanation of the
    // re-justification on each lookup.
    return Toy.getTheorem(name).justify('theorem', [name]);
  },

  /**
   * Refer to a definition in the definitions database.  If the
   * definition is by cases, takes a second argument of T or F
   * as desired.  Throws an exception if not found.
   */
  definition: {
    action: function(name, tOrF) {
      // The derivations are computed in advance, and have the name or
      // name and true/false as the argument(s).
      var args = arguments.length == 1 ? [name] : [name, tOrF];
      return Toy.getDefinition(name, tOrF).justify('definition', args);
    },
    inputs: {string: 1, optString: 2},
    form: ('Definition of <input name=string> '
           + 'if by cases enter T or F <input name=optString>'),
    comment: 'look up a definition',
    description: '=definition'
  },

  /**
   * Refers to an axiom (one that takes no arguments).  Obsolete.
   */
  axiom: function(name) {
    // TODO: Remove this; just use the axioms directly as rules.
    //   These days they run efficiently.
    //
    // The "length" is the number of declared arguments.
    assert(name.substring(0, 5) == 'axiom' && rules[name].length == 0,
           function() { return 'Not an axiom: ' + name; });
    return rules[name]();
  },

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R.  The subexpression must match
   * the equation's LHS, meaning they are the same except possibly
   * in names of vound variables.
   */
  r: {
    action: function(equation, target, path) {
      path = Toy.path(path, target);
      assert(equation.isCall2('='), function() {
	return 'Rule R requires equation: ' + equation;
      }, equation);
      if (equation.getLeft() === equation.getRight()) {
        // The equation LHS must "match" the site, but can differ in
        // bound variables, so the replacement could be a no-op if
        // these are not identical too.  (This is a cheap but not
        // complete check for a no-op.)
        if (target.locate(path) === equation.getLeft()) {
          // Quick return if the replacement is a no-op.
          return target.justify('r', [equation, target, path],
                                [target, equation]);
        }
      }
      function replacer(expr) {
	if (expr.matches(equation.getLeft())) {
	  return equation.getRight();
	} else {
	  assert(false, 'Rule R: subexpression ' + expr +
                 '\n of ' + target +
                 '\n must match ' + equation.getLeft(), target);
	}
      }
      // Auto-justify input steps if requested by the current configuration.
      if (!equation.ruleName) {
        assert(Toy.autoAssert,
               function() { return 'Rule R unproven equation: ' + equation; });
	equation.assert();
      }
      if (!target.ruleName) {
        assert(Toy.autoAssert,
               function() { return 'Rule R unproven target: ' + target; });
	target.assert();
      }
      var result = target.replaceAt(path, replacer);
      var lvars = equation.getLeft().freeNames();
      // TODO: Review this assumption.  It appears we really should
      // compare the set of constraints generated by the two sides.
      //
      // If the right side has any free names not in the left side,
      // the result may have constraints not met by the target, so
      // typecheck it.
      var rvars = equation.getRight().freeNames();
      for (var name in rvars) {
	if (!(name in lvars)) {
	  Toy.findType(result);
	  break;
	}
      }
      var result = target.hasHyps ? result.asHyps() : result;
      var justified = result.justify('r', [equation, target, path],
                                     [target, equation]);
      justified.details = null;
      return justified;
    },
    inputs: {equation: 1, site: 2},
    // Currently not offered in forms; use "replace".
    // form: ('Replace selection with right side of step <input name=equation>'),
    comment: ('Replace an occurrence of a term with an equal term.'),
    hint: 'replace term with equal term',
    description: 'replace {site};; {in step siteStep} {using step equation}'
  },

  axiom1: {
    action: function() {
      var result = rules.assert('g T & g F == forall {a. g a}');
      return result.justify('axiom1');
    },
    inputs: {},
    form: '',
    description: 'axiom of T & F',
    comment: ('T and F are all the booleans')
  },

  axiom2: {
    action: function() {
      var result = rules.assert('x = y ==> h x = h y');
      return result.justify('axiom2');
    },
    inputs: {},
    form: '',
    description: 'axiom of function application',
    comment: ('functions take equal values to equal values')
  },

  axiom3: {
    action: function() {
      var result = rules.assert('(f = g) = forall {x. f x = g x}');
      return result.justify('axiom3');
    },
    inputs: {},
    form: '',
    comment: ('extensionality: functions are equal based on equal results'
	      + ' on all inputs.'),
    description: 'axiom of equal functions'
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: {
    action: function(call) {
      call = typeof call == 'string' ? Toy.parse(call) : call;
      assert(call.isOpenCall(), function() {
	return 'Axiom 4 needs ({v. B} A), got: ' + call.toString();
      });
      var lambda = call.fn;
      var result =
        (call.arg instanceof Toy.Var && call.arg.name === lambda.bound.name
         // Same idea as optimization in Lambda._subFree.
         ? equal(call, lambda.body)
         : equal(call, lambda.body.subFree(call.arg, lambda.bound)));
      // Always make sure the call has a type.  It came from elsewhere.
      Toy.findType(call);
      return rules.assert(result).justify('axiom4', [call]);
    },
    inputs: {term: 1},  // Specifically a Call to a Lambda.
    form: 'Enter {v. body} expr <input name=term>',
    hint: 'apply a function to its argument',
    description: 'axiom of substitution',
    comment: ('')
  },

  axiom5: {
    action: function() {
      var result = rules.assert('(the ((=) y)) = y');
      return result.justify('axiom5');
    },
    inputs: {},
    form: '',
    comment: ('axiom of description'),
    description: 'axiom of description'
  },

  // Generalizes axiomTIsNotF.
  // Rewrite to (forall {p. F = [p = [not p]]}), instantiate, expand "not":
  // 1. F = [F = [F = F]], so 2. F = [F = T] (r5230FT)
  // 3. F = [T = [F = T]], so F = [T = F] (r5230TF) by
  // Rule R on r5230FT and step 3.
  axiomPNeqNotP: {
    action: function() {
      var result = rules.assert('forall {p. not (p = not p)}');
      return result.justify('axiomPNeqNotP');
    },
    inputs: {},
    form: '',
    description: 'boolean axiom',
    comment: ('')
  },

  // Definition of F, for book-style proofs.
  defFFromBook: function() {
    return equal(F, call('forall', lambda(x, x))).justify('defFFromBook');
  },

  // Book only.
  defAnd: function() {
    var result =
      equal('&', lambda(x, lambda(y, equal(lambda(g, call(g, T, T)),
                                            lambda(g, call(g, x, y))))));
    return result.justify('defAnd');
  },

  // Book only.
  defImplies: function() {
    return equal('==>', Toy.parse('{x. {y. x == x & y}}')).justify('defImplies');
  },

  //
  // Theorems and rules of inference.
  //

  // Takes an arbitrary expression A, concluding that it is equal
  // to itself. (5200)
  eqSelf: {
    action: function(a) {
      a = Toy.termify(a);
      var step1 = rules.axiom4(call(lambda(x, x), a));
      var result = rules.r(step1, step1, '/left');
      return result.justify('eqSelf', arguments);
    },
    inputs: {term: 1},
    form: 'Term to prove equal to itself: <input name=term>',
    hint: 'A = A',
    comment: 'Derives A = A.',
    description: 'A = A',
    labels: 'primitive'
  },

  // The two forms of "=" are interchangeable (other than precedence).
  eqIsEquiv: {
    action: function() {
      var step1 = rules.eqSelf(new Toy.Var('='));
      var step2 = rules.eqSelf(new Toy.Var('=='));
      var result = rules.r(step2, step1, '/right');
      return result.justify('eqIsEquiv', []);
    },
    form: '',
    comment: '= and \u21d4 are the same',
    labels: 'uncommon'
  },

  // Given A, proves A == A.  This is intended for use only when
  // A is boolean.
  equivSelf: {
    action: function(a) {
      var step1 = rules.eqSelf(a);
      var eqn = rules.theorem('eqIsEquiv');
      var result = rules.r(eqn, step1, '/binop');
      return result.justify('equivSelf', []);
    },
    inputs: {term: 1},
    form: 'Term to prove equal to itself: <input name=term>',
    hint: 'A \u21d4 A',
    comment: 'Derives A \u21d4 A.',
    description: 'A \u21d4 A',
    labels: 'primitive'
  },

  // r5201a, not used.  Works with hypotheses.
  replaceWhole: {
    action: function(a, ab) {
      var aa = rules.eqSelf(a);
      var b = ab.getRight();
      var result = rules.replace(ab, a, '/');
      return result.justify('replaceWhole', arguments, arguments);
    },
    inputs: {step: 1, equation: 2},
  },

  // r5201b.  Works with hypotheses.
  eqnSwap: {
    action: function(h_ab) {
      var ab = h_ab.unHyp();
      var aa = rules.eqSelf(ab.getLeft());
      var ba = rules.replace(h_ab, aa, '/left');
      return ba.justify('eqnSwap', arguments, arguments);
    },
    inputs: {equation: 1},
    form: 'Swap sides in step <input name=equation>',
    hint: '[a = b] to [b = a]',
    comment: 'from a = b deduce b = a',
    description: '[a = b] to [b = a]',
    labels: 'basic algebra'
  },

  // r5201c.  Works with hypotheses.
  eqnChain: {
    action: function(ab, bc) {
      var ac = rules.replace(bc, ab, '/main/right');
      var result = ac;
      return result.justify('eqnChain', arguments, arguments);
    },
    description: '[a = b] and [b = c] to [a = c]',
    hint: '[a = b] and [b = c] to [a = c]',
    comment: 'from a = b and b = c deduce a = c'
  },

  // r5201d, not used.  Works with hypotheses.
  applyBySides: {
    action: function(ab, cd) {
      var a = ab.getLeft();
      var b = ab.getRight();
      var c = cd.getLeft();
      var d = cd.getRight();
      var ac = call(a, c);
      var acac = rules.eqSelf(ac);
      var acbc = rules.replace(ab, acac, '/right/fn');
      var acbd = rules.replace(cd, acbc, '/right/arg');
      var result = acbd;
      return result.justify('applyBySides', arguments, arguments);
    },
    inputs: {equation: [1, 2]}
  },

  // r5201e.  Works with hypotheses.
  applyBoth: {
    action: function(h_eqn, a) {
      var eqn = h_eqn.unHyp();
      var step1 = rules.eqSelf(call(eqn.locate('/left'), a));
      var step2 = rules.replace(h_eqn, step1, '/right/fn');
      return step2.justify('applyBoth', arguments, [h_eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Apply both sides of step <input name=equation>'
	   + ' to term <input name=term>'),
    hint: '[f = g] to [f x = g x]',
    comment: 'given f = g, deduce (f x) = (g x)',
    description: '[f = g] to [f x = g x]',
  },

  // r5201f.  Works with hypotheses.
  // If f is a lambda expression, also applies it to both sides.
  applyToBoth: {
    action: function(f, h_ab) {
      var ab = h_ab.unHyp();
      var fafa = rules.eqSelf(call(f, ab.getLeft()));
      var fafb = rules.replace(h_ab, fafa, '/right/arg');
      var result = fafb;
      if (f instanceof Toy.Lambda) {
        var step2 = rules.apply(fafb, '/main/left');
        var result = rules.apply(step2, '/main/right');
      }
      return result.justify('applyToBoth', arguments, [h_ab]);
    },
    inputs: {term: 1, equation: 2},
    form: ('Apply function <input name=term>'
	   + ' to both sides of step <input name=equation>'),
    hint: '[a = b] to [f a = f b]',
    comment: 'given a = b deduce (f a) = (f b)',
    description: 'from a = b to (f a) = (f b)'
  },

  // Use the definition of the given name at the given location
  // in WFF A.  If the definition is by cases the location should
  // be a call to the named function, with T or F as the argument.
  // Works with hypotheses.
  useDefinition: {
    action: function(a, path) {
      var args = [a, path];
      path = Toy.path(path, a);
      var target = a.locate(path);
      if (target instanceof Toy.Var) {
        var result = rules.replace(rules.definition(target.name), a, path);
        return result.justify('useDefinition', args, [a]);
      } else {
        assert(target instanceof Toy.Call && target.arg instanceof Toy.Var,
                 'Target of useDefinition not suitable: ' + target);
        var arg = target.arg;
        assert(arg.name == 'T' || arg.name == 'F',
                 'Target of useDefinition not suitable: ' + target);
        var result =
	  rules.replace(rules.definition(target.fn.name, arg), a, path);
        return result.justify('useDefinition', args, [a]);
      }
    },
    inputs: {site: 1},
    form: '',
    hint: 'replace name with its definition',
    comment: (''),
    description: 'definition of {site}'
  },

  // Just applies an anonymous lambda to an argument at the
  // specified location in a step.
  simpleApply: {
    action: function(step, path) {
      // Note that axiom 4 checks validity of its argument.
      var equation = rules.axiom4(step.locate(path));
      var result = rules.replace(equation, step, path);
      return result.justify('simpleApply', arguments, [step]);
    },
    inputs: {reducible: 1},
    isRewriter: true,
    // form: '',
    hint: 'apply a function to its argument',
    comment: ('Applies a lambda to its argument'),
    description: '=simpleApply',
    labels: 'uncommon'
  },

  // Derives a rewriter for a call that reduces a call to a lambda, or
  // expands the definition of a one- or two-argument function and
  // reduces resulting lambdas.  If none of these apply to the call,
  // returns null.
  applier: {
    action: function(expr) {
      var args = [expr];
      assert(expr instanceof Toy.Call);
      var fn = expr.fn;
      if (fn instanceof Toy.Lambda) {
        var result = rules.axiom4(expr);
        return result.justify('applier', args);
      }
      // Call that looks like (<constant> <expr>).
      if (fn.isConst()) {
        var defn = Toy.findDefinition(fn.name);
        if (defn) {
          var step1 = rules.eqSelf(expr);
          var step2 = rules.useDefinition(step1, '/right/fn');
          return step2.justify('applier', args);
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
            var step3 = rules.simpleApply(step2, '/right');
            var step4 = rules.eqSelf(expr);
            var step5 = rules.replace(step3, step4, '/right/fn');
            var step6 = rules.simpleApply(step5, '/right');
            return step6.justify('applier', args);
          }
        }
      }
      return null;
    },
    inputs: {term: 1},
    description: 'apply function in {term}',
    hint: 'apply the function',
    comment: 'Equate to call with definition expanded and lambdas reduced'
  },
    

  // "Reduces" a call identified by a path within a theorem. If the
  // call is an application of a lambda expression to an argument,
  // beta-reduces it.  If the target expression is a call to a named
  // function supplying one or two arguments, expands the definition
  // and applies the expansions to the argument(s).
  apply: {
    action: function(step, path) {
      path = Toy.path(path, step);
      var target = step.locate(path);
      assert(target, function() {
        return 'Path ' + path + ' not found in ' + step;
      }, step);
      var equation = rules.applier(target);
      assert(equation, function() { return 'Cannot apply at ' + target; });
      var result = rules.replace(equation, step, path);
      return result.justify('apply', [step, path], [step]);
    },
    isRewriter: true,
    inputs: {site: 1},
    form: '',
    hint: 'apply a function to its argument',
    comment: ('Applies a function, named or not, to one or two arguments'),
    description: '=apply'
  },

  /**
   * Change the name of a bound variable.  Replaces the lambda
   * subexpression in expr at path with one that binds newName, which
   * may be a string or Var, and uses it in place of any references to
   * the old bound variable.
   */
  changeVar: {
    action: function(step, path, newVar) {
      newVar = varify(newVar);
      path = Toy.path(path, step);
      var target = step.locate(path);
      assert(target instanceof Toy.Lambda, 'Not a function: ' + target, step);
      assert(!step.freeNames()[newVar.name],
             'New bound variable ' + newVar.name + ' must not occur free.',
             step);
      var changed = lambda(newVar,
                           target.body.subFree(newVar, target.bound));
      var step1 = rules.eqSelf(changed);
      var step2 = rules.r(step1, step, path);
      return step2.justify('changeVar', arguments, [step]);
    },
    inputs: {bindingSite: 1, varName: 3},
    form: ('Rename to <input name=varName>'),
    hint: 'rename a bound variable',
    comment: ('Change the name of a bound variable.  The new name '
              + 'must not occur free in the target expression.  '
              + 'Uses the fact that the original expression matches '
              + 'the one with changed bound variable.'),
    description: '=changeVar'
  },

  /**
   * From an equation, infers a similar equation with each
   * side wrapped in a binding of the given variable or variable name.
   */
  bindEqn: {
    action: function(h_eqn, v) {
      v = Toy.varify(v);
      var eqn = h_eqn.unHyp();
      eqn.assertCall2('=');
      var step1 = rules.eqSelf(lambda(v, eqn.getLeft()));
      var step2 = rules.replace(h_eqn, step1, '/right/body');
      return step2.justify('bindEqn', arguments, [h_eqn]);
    },
    inputs: {equation: 1, varName: 2},
    form: ('Bind variable <input name=varName> in step <input name=equation>'),
    hint: '[a = b] to [{v. a} = {v. b}]',
    comment: ('Makes each side of an equation into a function'
              + ' of the variable you choose.'),
    description: '[a = b] to [{v. a} = {v. b}]',
    labels: 'primitive'
  },

  /**
   * Substitutes term "a" for variable or name "v" in equation b_c,
   * with the result a consequence of b_c.  (5209) Does not support
   * hypotheses.
   */
  instEqn: {
    action: function(b_c, a, v) {
      var bound = rules.bindEqn(b_c, v);
      var step2 = rules.applyBoth(bound, a);
      var step3 = rules.apply(step2, '/left');
      var step4 = rules.apply(step3, '/right');
      return step4.justify('instEqn', arguments, [b_c]);
    },
    inputs: {equation: 1, term: 2, varName: 3},
    form: ('Instantiate <input name=varName> with <input name=term> '
	   + 'in step <input name=equation>'),
    hint: 'substitute for a variable in equation',
    comment: ('Instantiates a free variable in an equation.'),
    description: 'substitute for {var}',
    labels: 'primitive'
  },

  /**
   * forall {x. x = x}
   * Helper lemma for eqT.
   */
  xAlwaysX: {
    action: function() {
      var a3 = rules.axiom('axiom3');
      var step1 = rules.instEqn(a3, f, g);
      var step2 = rules.instEqn(step1, lambda(y, y), f)
      var step3 = rules.apply(step2, '/right/arg/body/right');
      var step4 = rules.apply(step3, '/right/arg/body/left');
      var step5 = rules.eqSelf(lambda(y, y));
      var step6 = rules.replace(step4, step5, '');
      return step6.justify('xAlwaysX', arguments);
    }
  },

  // T = [B = B] (5210)
  eqT: {
    action: function(b) {
      var lemma = rules.theorem('xAlwaysX');
      var step0 = rules.useDefinition(lemma, '/fn')
      var step1 = rules.applyBoth(step0, b);
      var step2 = rules.apply(step1, '/right');
      var step3 = rules.apply(step2, '/left');
      return step3.justify('eqT', arguments, []);
    },
    inputs: {term: 1},
    form: ('Term to prove equal to itself: <input name=term>'),
    hint: '(T = (A = A))',
    comment: ('Proves T = [A = A].'),
    description: 'T = (A = A)',
    labels: 'primitive'
  },

  /**
   * "T" is a theorem.  In the book, T is defined as an instance of
   * eqSelf.
   */
  t: function() {
    var step1 = rules.eqSelf(T);
    var step2 = rules.eqT(T);
    var step3 = rules.rRight(step2, step1, '');
    return step3.justify('t');
  },

  // Target is forall {x. B}, expr is A, which will replace
  // all occurrences of x.  Uses no book-specific definitions,
  // and relies only on theorem "T", 5200, and reduce. (5215)
  // Handles hypotheses.
  instForall: {
    action: function(h_target, expr) {
      var target = h_target.unHyp();
      assert(target.fn instanceof Toy.Var && target.fn.name == 'forall',
             "Must be 'forall': " + target.fn,
             h_target);
      assert(target.arg instanceof Toy.Lambda,
             "Must be lambda expression: " + target.arg,
             h_target);
      var step1 = rules.useDefinition(h_target, '/main/fn');
      var step2 = rules.applyBoth(step1, expr);
      var step3 = rules.apply(step2, '/main/left');
      var step4 = rules.apply(step3, '/main/right');
      // Rule fromTIsA depends on instForall via tIsXIsX and
      // equationCases, though this next step is a simplified fromTIsA
      // without hypotheses.
      var step5 = rules.replace(step4, rules.theorem('t'), '/main');
      return step5.justify('instForall', arguments, [h_target]);
    },
    inputs: {step: 1, term: 2, condition: {1: function(target) {
      return (target instanceof Toy.Call
	      && target.fn instanceof Toy.Var
	      && target.fn.name == 'forall');
    }}},
    form: ('In step <input name=step> instantiate bound var'
	   + ' with term <input name=term>'),
    hint: 'instantiate "forall"',
    comment: ('In a "forall", instantiates the bound variable with'
              + ' a given term.'),
    description: '=instForall'
  },

  // From [A = B] deduce T = [A = B].
  toTIsEquation: {
    action: function(a_b) {
      assertEqn(a_b);
      var step1 = rules.eqT(a_b.locate('/left'));
      var step2 = rules.replace(a_b, step1, '/right/right');
      return step2.justify('toTIsEquation', arguments, [a_b]);
    },
    inputs: {equation: 1},
    form: 'Introduce "T = " into step <input name=equation>',
    hint: '[a = b] to [T = (a = b)]',
    comment: ('From [a = b] deduce T = [a = b].'),
    description: 'from a = b to T = (a = b)',
    labels: 'primitive'
  },

  // Prove [F = T] = F.  Number reflects dependencies in the book
  // proof, but this proof needs only simple rules and axiomPNeqNotP.
  //
  // (Or r5230TF, see the alternate proof further below.)
  r5230FT: {
    action: function() {
      var step1 = rules.axiom('axiomPNeqNotP');
      var step2 = rules.instForall(step1, F);
      var step3 = rules.useDefinition(step2, '/fn');
      var step4 = rules.useDefinition(step3, '/arg/right/fn');
      var step5 = rules.rRight(rules.eqT(F), step4, '/right/right');
      var step6 = rules.eqnSwap(step5);
      return step6.justify('r5230FT');
    },
    comment: ('[F = T] = F')
  },

  // Bookish: (F = T) = F
  r5230FTBook: {
    action: function() {
      var step1 = rules.axiom('axiom2');
      var map = {h: Toy.parse('{x. x = F}'),
                 x: F,
                 y: T};
      var step2 = rules.instMultiVars(step1, map);
      var step3 = rules.apply(step2, '/right/right');
      var step4 = rules.apply(step3, '/right/left');
      var step5 = rules.r5218(F);
      var step6 = rules.r(step5, step4, '/right/right');
      var step7 = rules.eqT(F);
      var step8 = rules.rRight(step7, step6, '/right/left');
      var step9 = rules.r(step5, step8, '/right');
      var step10 = rules.defImplies();
      var step11 = rules.r(step10, step9, '/binop');
      var step12 = rules.apply(step11, '/fn');
      var step13 = rules.apply(step12, '');
      // TODO: Infer by cases from 5229 (rules about '&').
      var step14 = rules.tautology('x & F == F');
      var step15 = rules.instEqn(step14, Toy.parse('F = T'), 'x')
      var step16 = rules.r(step15, step13, '/right');
      return step16.justify('r5230FTBook');
    }
  },

  // Prove [T = F] = F.  Number reflects dependencies in the book
  // proof, but this proof needs only simple rules and axiomPNeqNotP.
  r5230TF: {
    action: function() {
      var step1 = rules.axiom('axiomPNeqNotP');
      var step2 = rules.instForall(step1, T);
      var step3 = rules.useDefinition(step2, '/fn');
      var step4 = rules.useDefinition(step3, '/arg/right/fn');
      var step5 = rules.r(rules.r5230FT(), step4, '/right/right');
      var step6 = rules.eqnSwap(step5);
      return step6.justify('r5230TF');
    },
    comment: ('[T = F] = F')
  },

  // Prove [F = T] = F from r5230TF.
  //
  // Note that the proof of r5230TF depends on r5230FT; but if
  // something like r5230TF were an axiom, then this would make sense.
  //  
  // TODO: Is there a more elegant proof of this?
  r5230FT_alternate: {
    action: function() {
      // Note: this uses instVar on facts of the form A ==> B,
      // which is only supported by instVar by using fromTIsA and toTisA.
      // It is applied to steps that have no hypotheses, but still
      // instVar uses toTIsA (and fromTIsA).
      // TODO: Confirm that this is all correct.
      var step1a = rules.instVar(rules.axiom('axiom2'), F, x);
      var step1b = rules.instVar(step1a, T, y);
      var step1c = rules.instVar(step1b, lambda(x, equal(x, F)), h);
      var step2a = rules.apply(step1c, '/right/left');
      var step2b = rules.apply(step2a, '/right/right');
      var step3aa = rules.eqT(F);
      var step3a = rules.rRight(step3aa, step2b, '/right/left');
      var step3bb = rules.r5218(F);
      var step3b = rules.r(step3bb, step3a, '/right/right');
      var step3c = rules.r(step3bb, step3b, '/right');
      // From this point most of the work is basically a proof
      // that [A ==> F] ==> not A, a tautology.
      var step4 = rules.toTIsA(step3c);
      // We are going to prove the cases of: (x ==> F) = (x = F)
      // First with x = F.
      var step11 = rules.definition('==>', F);
      var step12 = rules.applyBoth(step11, F);
      var step13 = rules.apply(step12, '/right');
      var step14 = rules.r(step3aa, step13, '/right');
      // Then with x = T.
      var step21 = rules.definition('==>', T);
      var step22 = rules.applyBoth(step21, F);
      var step23 = rules.apply(step22, '/right');
      var step24 = rules.r5230TF();
      var step25 = rules.rRight(step24, step23, '/right');
      // Now use the cases rule:
      var step5 = rules.equationCases(step25, step14, x);
      // Then instantiate [F = T] for x.
      var step6 = rules.instEqn(step5, equal(F, T), x);
      // And use the fact that [F = T] ==> F
      var step7 = rules.rRight(step4, step6, '/left');
      var step8 = rules.fromTIsA(step7);
      return step8.justify('r5230FT_alternate');
    },
    comment: ('[F = T] = F')
  },

  // [T & T] = T.  Uses no book-specific definitions.
  // Only used in 5212 and book version of 5216.
  r5211: function() {
    var step1 = rules.definition('&', T);
    var step2 = rules.applyBoth(step1, T);
    var step3 = rules.apply(step2, '/right');
    return step3.justify('r5211');
  },

  // Book version of r5211.
  r5211Book: function() {
    var step1 = rules.instEqn(rules.axiom('axiom1'), lambda(y, T), g);
    var step2a = rules.apply(step1, '/right/arg/body');
    var step2b = rules.apply(step2a, '/left/right');
    var step2c = rules.apply(step2b, '/left/left');
    var step3a = rules.eqT(lambda(x, T));
    var step3b = rules.rRight(rules.definition('forall'), step3a, '/right/fn');
    var step4 = rules.rRight(step3b, step2c, '/right');
    return step4.justify('r5211Book');
  },

  // T & T.  Uses no book-specific definitions.
  // Used to prove equationCases.  The "cases" rule
  // and makeConjunction could treat this as a tautology.
  r5212: function() {
    var step1 = rules.rRight(rules.theorem('r5211'),
                             rules.theorem('t'),
                             '/');
    return step1.justify('r5212');
  },

  r5212Book: {
    action: function() {
      var step1 = rules.r5211Book();
      var step2 = rules.theorem('t');
      var step3 = rules.rRight(step1, step2, '');
      return step3.justify('r5212Book');
    }
  },

  // Bookish: From theorems A = B and C = D, derives theorem
  // [A = B] & [C = D].  Used in andTBook.
  r5213: function(a_b, c_d) {
    assertEqn(a_b);
    var a = a_b.locate('/left');
    var b = a_b.locate('/right');
    assertEqn(c_d);
    var c = c_d.locate('/left');
    var d = c_d.locate('/right');
    var step1 = rules.eqT(a);
    var step2 = rules.r(a_b, step1, '/right/right');
    var step3 = rules.eqT(c);
    var step4 = rules.r(c_d, step3, '/right/right');
    var step5 = rules.r(step2, rules.theorem('r5212'), '/left');
    var step6 = rules.r(step4, step5, '/right');
    return step6.justify('r5213', arguments, arguments);
  },


  // Bookish: T & F = F
  r5214: {
    action: function() {
      var step1 = rules.axiom('axiom1');
      var step2 = rules.instEqn(step1, Toy.parse('{x. x}'), 'g');
      var step3 = rules.apply(step2, '/right/arg/body');
      var step4 = rules.apply(step3, '/left/right');
      var step5 = rules.apply(step4, '/left/left');
      var step6 = rules.defFFromBook();
      var step7 = rules.rRight(step6, step5, '/right');
      return step7.justify('r5214');
    }
  },

  // 5216 by the book.
  andTBook: function(a) {
    var step1 = rules.axiom('axiom1');
    var step2 =
      rules.instEqn(step1, lambda(x, equal(call('&', T, x), x)), g);
    var step3 = rules.apply(step2, '/left/left');
    var step4 = rules.apply(step3, '/left/right');
    var step5 = rules.apply(step4, '/right/arg/body');
    var step7 = rules.r5214();
    var step8 = rules.r5213(rules.theorem('r5211'), step7);
    var step9 = rules.r(step5, step8, '/');
    var step10 = rules.instForall(step9, a);
    return step10.justify('andTBook', arguments);
  },

  // 5216, using the definition of "true and".  Not used.
  andT: function(a) {
    var step1 = rules.applyBoth(rules.definition('&', T), a);
    var step2 = rules.apply(step1, '/right');
    return step2;
  },

  // Book only.  We use axiomPNeqNotP instead of defining F.
  r5217Book: function() {
    var step1 = rules.instEqn(rules.axiom('axiom1'),
                              lambda(x, equal(T, x)), g);
    var step2a = rules.apply(step1, '/left/left');
    var step2b = rules.apply(step2a, '/left/right');
    var step2c = rules.apply(step2b, '/right/arg/body');
    var step3 = rules.rRight(rules.eqT(T), step2c, '/left/left');
    var step4a = rules.andT(equal(T, F));
    var step4b = rules.r(step4a, step3, '/left');
    var step5a = rules.instEqn(rules.axiom('axiom3'), lambda(x, T), f);
    var step5b = rules.instEqn(step5a, lambda(x, x), g);
    var step6a = rules.apply(step5b, '/right/arg/body/left');
    var step6b = rules.apply(step6a, '/right/arg/body/right');
    var step6c = rules.useDefinition(rules.defFFromBook(),
                                     '/right/fn');
    var step6d = rules.rRight(step6c, step6b, '/left');
    var step7 = rules.rRight(step6d, step4b, '/right');
    return step7.justify('r5217Book');
  },

  // 5217 is the same as 5230TF.
  // [T = F] = F
  // Not used, though previously used in 5218.

  // Given two WFFs each of the form A = B that are the result
  // of substituting T and F respectively for a variable,
  // proves the WFF with the variable.
  equationCases: {
    action: function(caseT, caseF, v) {
      v = varify(v);
      var stepT1 = rules.toTIsEquation(caseT);
      var stepF1 = rules.toTIsEquation(caseF);
      var step2 = rules.replace(stepT1, rules.theorem('r5212'), '/left');
      var step3 = rules.replace(stepF1, step2, '/right');
      // Note: If a variable is not in caseT it is also not in caseF.
      var newVar = Toy.genVar('w', caseT.allNames());
      var gen = caseT.generalizeTF(caseF, newVar);
      var lexpr = lambda(newVar, gen);
      var step4 = rules.instEqn(rules.axiom('axiom1'), lexpr, g);
      var step5 = rules.apply(step4, '/right/arg/body');
      var step6 = rules.apply(step5, '/left/right');
      var step7 = rules.apply(step6, '/left/left');
      var step8 = rules.replace(step7, step3, '');
      var step9 = rules.instForall(step8, v);
      return step9.justify('equationCases', arguments, [caseT, caseF]);
    },
    inputs: {equation: [1, 2], varName: 3},
    form: ('Cases: true case step <input name=equation1>'
	   + ' false case step <input name=equation2>,'
	   + ' use variable <input name=varName>'),
    hint: 'proof by cases, for equations',
    comment: ('Given two proved equations C and D obtainable by substitution' +
              ' for a free variable of an equation A = B; C by substituting' +
              ' T, and D by substituting F, proves A = B.'),
    labels: 'primitive'
  },

  // Note that this or 5230TF or symmetry of equality of booleans
  // might be taken as an axiom given r5230FT_alternate.
  tIsXIsX: {
    action: function() {
      // TODO: Switch back to r5230TF whenever desired.
      var step1 = rules.theorem('r5217Book');
      var step2 = rules.eqT(T);
      var step3 = rules.eqnSwap(step2);
      var step4 = rules.equationCases(step3, step1, 'x');
      return step4.justify('tIsXIsX');
    }
  },

  // 5218: [T = A] = A
  // Stepping stone to universal generalization.
  r5218: {
    action: function(a) {
      var step1 = rules.theorem('tIsXIsX');
      var step2 = rules.instEqn(step1, a, x);
      return step2.justify('r5218', arguments);
    },
    inputs: {term: 1},
    form: ('Term to use in ((T = A) = A): <input name=term>'),
    hint: '(T = A) = A',
    labels: 'uncommon',
    comment: ('For any expression derives (T = A) = A.'),
    description: '(T = A) = A'
  },

  // 5219.  Works with hypotheses.
  toTIsA: {
    action: function(h_a) {
      var step1 = rules.r5218(h_a.unHyp());
      var step2 = rules.rRight(step1, h_a, '/main');
      return step2.justify('toTIsA', arguments, [h_a]);
    },
    inputs: {step: 1},
    form: 'Introduce "T = " into step <input name=step>',
    hint: '[a] to [T = a]',
    comment: ('From A derives T = A'),
    description: '[a] to [T = a];; {in step step}',
    labels: 'primitive'
  },

  // also 5219.  Works with hypotheses.
  fromTIsA: {
    action: function(h_t_a) {
      var t_a = h_t_a.unHyp()
      assertEqn(t_a);
      var left = t_a.locate('/left');
      assert(left instanceof Toy.Var && left.name == 'T',
             'Input should be [T = A]: ' + t_a,
             h_t_a);
      var a = t_a.locate('/right');
      var result = rules.replace(rules.r5218(a), h_t_a, '/main');
      return result.justify('fromTIsA', arguments, [h_t_a]);
    },
    inputs: {equation: 1, condition: {1: function(h_eqn) {
      var eqn = h_eqn.unHyp();
      var left = eqn.getLeft();
      return (left instanceof Toy.Var && left.name == 'T');
    }}},
    form: 'Eliminate "T = " from step <input name=equation>',
    description: '[T = a] to [a]',
    hint: '[T = a] to [a]',
    comment: ('From T = A derives A'),
    labels: 'primitive'
  },

  // Lemma helper for addForall, a pure theorem.
  forallXT: {
    action: function() {
      var step1 = rules.eqSelf(Toy.parse('{x. T}'));
      var fa = rules.definition('forall');
      var result = rules.rRight(fa, step1, '/fn');
      return result.justify('forallXT', arguments);
    }
  },

  // 5220 (universal generalization).  From A deduces forall {v. A}.
  // The variable v may be given as a string, which it converts
  // internally to a variable.  Supports hypotheses.
  addForall: {
    action: function(h_a, v) {
      v = varify(v);
      assert(!(h_a.hasHyps && h_a.getLeft().hasFreeName(v.name)),
	     function() {
	       return v.name + ' occurs free in hypotheses of ' + h_a;
	     },
             h_a);
      var step1 = rules.toTIsA(h_a);
      var step2 = rules.theorem('forallXT');
      var step3 = rules.changeVar(step2, '/arg', v);
      var step4 = rules.replace(step1, step3, '/arg/body');
      return step4.justify('addForall', arguments, [h_a]);
    },
    inputs: {step: 1, varName: 2},
    form: ('In step <input name=step> generalize on variable '
           + '<input name=varName>'),
    hint: 'add "forall"',
    comment: ('Universal Generalization, wrap a theorem A in'
              + ' (forall v A) using the variable of your choice.'),
    description: 'add \u2200',
  },

  // 5221 (one variable), in the given step substitute term A for free
  // variable v, which may also be a string, which will be converted
  // to a variable.  Handles hypotheses, allowing substitution for a
  // variable even if free in the hypotheses.
  instVar: {
    action: function(step, a, v) {
      a = Toy.termify(a);
      v = Toy.varify(v);
      var map = {};
      map[v.name] = a;
      var result = rules.instMultiVars(step, map);
      return result.justify('instVar', arguments, [step]);
    },
    inputs: {step: 1, term: 2, varName: 3},
    form: ('In step <input name=step>, for variable <input name=varName> '
           + 'substitute <input name=term>'),
    hint: 'substitute for a free variable',
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.'),
    description: 'substitute for {var};; {in step step}'
  },

  // Same functionality as instVar, but with a site (step+path) and a
  // term as the arguments.
  instantiateVar: {
    action: function(step, path, term) {
      v = step.locate(path);
      assert(v instanceof Toy.Var, 'Not a variable: ' + v);
      var map = {};
      map[v.name] = term;
      var result = rules.instMultiVars(step, map);
      var simpler = rules.simplifyAssumptions(result);
      return simpler.justify('instantiateVar', arguments, [step]);
    },
    inputs: {site: 1, term: 3},
    form: ('Substitute <input name=term> for the variable.'),
    hint: 'substitute for a free variable',
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.'),
    description: 'substitute for {site};; {in step siteStep}',
    labels: 'algebra basic'
  },

  // More like the book's 5221.  For each name in the map (a string),
  // substitutes the expression associated with it in the map, using
  // simultaneous substitution.  Handles hypotheses, allowing
  // substitution for variables that are free in the hypotheses.
  // Optimized to avoid substitutions that have no effect, thus
  // doing nothing if the substitution is a no-op.
  instMultiVars: {
    action: function(b, map) {
      var hyps = b.hasHyps;
      var step0 = hyps ? rules.asImplication(b) : b;
      var isEqn = step0.isCall2('=');
      var step = isEqn ? step0 : rules.toTIsA(step0);
      var namesReversed = [];
      for (var name in map) {
        var value = map[name];
        if (value.isVariable() && value.name === name) {
          continue;
        }
        step = rules.bindEqn(step, name);
	namesReversed.unshift(name);
      }
      if (namesReversed.length === 0) {
        return b.justify('instMultiVars', arguments, [b]);
      }
      // Then substitute for the renamed variables.
      namesReversed.forEach(function(name) {
          var step2 = rules.applyBoth(step, map[name]);
          var step3 = rules.apply(step2, '/right');
          step = rules.apply(step3, '/left');
        });
      if (!isEqn) {
        step = rules.fromTIsA(step);
      }
      if (hyps) {
        step = rules.asHypotheses(step);
      }
      return step.justify('instMultiVars', arguments, [b]);
    },
    inputs: {step: 1},
    hint: 'substitute for multiple variables',
    comment: ('Substitute in B for each variable named in the map, '
              + 'its value in the map'),
    description: '=instMultiVars'
  },

  // Given two theorems a and b, proves a & b.
  // Handles hypotheses.
  makeConjunction: {
    action: function(a, b) {
      var stepa = rules.toTIsA(a);
      var stepb = rules.toTIsA(b);
      var step1 = rules.theorem('r5212');
      var step2 = rules.replace(stepa, step1, '/left');
      var step3 = rules.replace(stepb, step2, '/main/right');
      return step3.justify('makeConjunction', arguments, [a, b]);
    },
    inputs: {step: [1, 2]},
    form: ('Conjoin steps <input name=step1> and <input name=step2>'),
    hint: '[p] and [q] to [p & q]',
    comment: ('Given a and b, derive a & b'),
    description: 'p & q;; using steps {step1}, {step2}'
  },

  // (5222) Given two theorems that are substitutions of T and
  // F respectively into a WFF; and a variable or variable name,
  // proves the WFF.  Works with hypotheses.
  cases: {
    action: function(caseT, caseF, v) {
      v = varify(v);
      // Note: caseF has no variables not in caseT, so no need to
      // calculate all of its names.
      var newVar = Toy.genVar('v', caseT.allNames());
      var gen = caseT.unHyp().generalizeTF(caseF.unHyp(), newVar);
      var step1a = rules.axiom4(call(lambda(newVar, gen), T));
      var step1b = rules.rRight(step1a, caseT, '/main');
      var step2a = rules.axiom4(call(lambda(newVar, gen), F));
      var step2b = rules.rRight(step2a, caseF, '/main');
      var step4 = rules.makeConjunction(step1b, step2b);
      var step5 = rules.instVar(rules.axiom('axiom1'),
                                lambda(newVar, gen), g);
      var step6 = rules.replace(step5, step4, '/main');
      var step7a = rules.instForall(step6, v);
      var step7b = rules.apply(step7a, '/main');
      return step7b.justify('cases', arguments, [caseT, caseF]);
    },
    inputs: {step: [1, 2], varName: 3},
    form: ('Cases: true case step <input name=step1>,'
	   + ' false case <input name=step2>,'
	   + ' use variable name <input name=varName>'),
    hint: 'proof by cases',
    comment: ('Prove a theorem by cases given two theorems that'
              + ' show it with T and F.'),
    description: 'cases: {var} true in step {step1}, false in step {step2}'
  },

  // Given P and P ==> Q, derive Q. (5224)
  // Handles hypotheses.
  modusPonens: {
    action: function(a, b) {
      var step1 = rules.toTIsA(a);
      // Replace the "a" in "b" with T.
      var step2 = rules.rRight(step1, b, '/main/left');
      // Use the definition of ==>.
      var step3 = rules.useDefinition(step2, '/main/fn');
      // From T ==> x derive x.
      var step4 = rules.apply(step3, '/main');
      return step4.justify('modusPonens', arguments, arguments);
    },
    inputs: {step: 1, implication: 2},
    form: ('Modus ponens: hypothesis step <input name=step>,'
	   + ' implication in step <input name=implication>'),
    hint: 'modus ponens',
    comment: ('Modus Ponens.  Given A and A ==> B derives B.'),
    description: '[p] and [p &rArr; q] to q',
    labels: 'primitive'
  },

  // (forall f) ==> f x
  r5225: {
    action: function() {
      var step1 = rules.axiom('axiom2');
      var map = {h: Toy.parse('{g. g x}'),
                 x: Toy.parse('{x. T}'),
                 y: f};
      var step2 = rules.instMultiVars(step1, map);
      var step3 = rules.rRight(rules.definition('forall'), step2, '/left/fn');
      var step4 = rules.apply(step3, '/right/left');
      var step5 = rules.apply(step4, '/right/left');
      var step6 = rules.apply(step5, '/right/right');
      var step7 = rules.r(rules.r5218(Toy.parse('f x')), step6, '/right');
      return step7.justify('r5225');
    }
  },

  // F ==> x; bookish
  r5227: {
    action: function() {
      var step1 = rules.theorem('r5225');
      var step2 = rules.instVar(step1, Toy.parse('{x. x}'), 'f');
      var step3 = rules.defFFromBook();
      var step4 = rules.rRight(step3, step2, '/left');
      var step5 = rules.apply(step4, '/right');
      return step5.justify('r5227');
    }
  },

  // [not T] = F
  r5231T: {
    action: function() {
      var step1 = rules.eqSelf(call('not', T));
      var step2 = rules.r(rules.definition('not'), step1, '/right/fn');
      var step3 = rules.r(rules.theorem('r5230FT'), step2, '/right');
      return step3.justify('r5231T');
    },
    comment: ('[not T] = F')
  },

  // [not F] = T
  r5231F: {
    action: function() {
      var step1 = rules.eqSelf(call('not', F));
      var step2 = rules.r(rules.definition('not'), step1, '/right/fn');
      var step3 = rules.eqT(F);
      var step4 = rules.rRight(step3, step2, '/right');
      return step4.justify('r5231F');
    }
  },

  // Helper for evalBool, not in book.
  // [[F =] = not].
  falseEquals: {
    action: function() {
      return rules.eqnSwap(rules.definition('not')).justify('falseEquals');
    }
  },

  // Another helper for evalBool, not in book.
  // [[T =] = {x. x}].
  trueEquals: {
    action: function() {
      var step1 = rules.r5218(x);
      var step2 = rules.eqSelf(Toy.parse('{x. x} x'));
      var step3 = rules.apply(step2, '/left');
      var step4 = rules.r(step3, step1, '/right');
      var step5 = rules.addForall(step4, x);
      var step6 = rules.instVar(rules.axiom('axiom3'), equal(T), f);
      var step7 = rules.instVar(step6, lambda(x, x), g);
      var step8 = rules.rRight(step7, step5, '');
      return step8.justify('trueEquals', arguments);
    }
  },

  // Equates the given expression to a similar one where boolean terms
  // are reduced.  (These are calls to =, &, |, ==>, or "not", and
  // lambda expressions, with an argument of T or F.)  Reduces
  // repeatedly until no subexpression can be reduced.
  // TODO: Prove all the truth table facts and use them directly
  // here.  Can we have unnamed theorems?
  evalBool: {
    action: function(expr) {
      var boolOps = {'&': true, '|': true, '==>': true, '=': true, not: true};
      function isReducible(expr) {
        return (expr instanceof Toy.Call
                && ((expr.fn instanceof Toy.Var
                     && boolOps[expr.fn.name]
                     && expr.arg instanceof Toy.Var
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
        var target = right.locate(_path);
        var fn = target.fn;
        if (fn instanceof Toy.Var) {
          var defn;
          if (fn.name == 'not') {
            defn = rules.theorem(target.arg.name == 'T'
                                 ? 'r5231T'
                                 : 'r5231F');
            result = rules.r(defn, result, '/right' + _path);
          } else if (fn.name == '=') {
            // TODO: To avoid dependencies on trueEquals and
            //   falseEquals, we could break this down into
            //   all 4 cases.
            defn = rules.theorem(target.arg.name == 'T'
                                 ? 'trueEquals'
                                 : 'falseEquals');
            result = rules.r(defn, result, '/right' + _path);
          } else {
            // &, |, ==>
            result = rules.useDefinition(result, '/right' + _path);
          }
        } else if (fn instanceof Toy.Lambda) {
          result = rules.apply(result, '/right' + _path);
        } else {
          assert(false, 'Unexpected expression: ' + target);
        }
      }
    },
    inputs: {term: 1},
    form: 'Boolean term to simplify: <input name=term>',
    labels: 'uncommon',
    comment: ('simplify a boolean term'),
    description: 'calculate boolean value'
  },

  // Proves an inference that the wff is a tautology and
  // returns it.  Checks that it is indeed proven to be a
  // tautology.  (5233)
  //
  // Accepts a parseable string as the wff.
  tautology: {
    action: function(wff) {
      if (typeof wff == 'string') {
        wff = Toy.parse(wff);
      }
      var key = wff.dump();
      var taut = _tautologies[key];
      if (taut) {
        return taut;
      } else {
        var names = wff.freeNames();
        // Not really a loop, just works with the first free (variable!)
        // name returned.
        for (var name in names) {
          if (wff instanceof Toy.Call && wff.fn instanceof Toy.Call
              && wff.fn.fn instanceof Toy.Var && wff.fn.fn.name == '=') {
            // WFF is already an equation.
            var step1 = rules.tautology(wff.subFree(T, name));
            var step2 = rules.tautology(wff.subFree(F, name));
            var step3 = rules.equationCases(step1, step2, name);
            var result = step3.justify('tautology', arguments);
            _tautologies[key] = result;
            return result;
          } else {
            var step1 = rules.tautology(equal(T, wff.subFree(T, name)));
            var step2 = rules.tautology(equal(T, wff.subFree(F, name)));
            var step3 = rules.equationCases(step1, step2, name);
            var step4 = rules.fromTIsA(step3);
            var result = step4.justify('tautology', arguments);
            _tautologies[key] = result;
            return result;
          }
        }
        // There are no free variables, evaluate the expression.
        var step11 = rules.evalBool(wff);
        assert(step11.isCall2('=')
               && step11.getRight() instanceof Toy.Var
               && step11.getRight().name == 'T',
               'Not a tautology: ' + step11.getLeft(),
               step11);
        var step12 = rules.rRight(step11, rules.theorem('t'), '');
        var result = step12.justify('tautology', arguments);
        _tautologies[key] = result;
        return result;
      }
    },
    inputs: {term: 1},
    form: 'Enter tautology: <input name=term>',
    hint: 'prove a tautology',
    comment: ('Tautology decider.'),
    description: 'tautology'
  },

  // Any instance of a tautology is a theorem.  This is part
  // of the book's Rule P.
  //
  // Given an expression that is a tautology, possibly with
  // hypotheses, and a substitution, derives an instantiation of the
  // tautology using the substitution, with the same hypotheses.
  // The tautology can be given as a parseable string.
  // Handles hypotheses.
  tautInst: {
    action: function(h_tautology, map) {
      if (typeof h_tautology == 'string') {
        h_tautology = Toy.parse(h_tautology);
      }
      var tautology = h_tautology.unHyp();
      var step1 = rules.tautology(tautology);
      var step2 = rules.instMultiVars(step1, map);
      if (h_tautology.hasHyps) {
	var h = h_tautology.getLeft();
	var step3 = rules.anyImpliesTheorem(h, step2);
	return step3.asHyps().justify('tautInst', arguments);
      } else {
	return step2.justify('tautInst', arguments);
      }
    },
    comment: ('substitute into tautology'),
    description: '=tautInst'
  },

  // TODO: Complete this.
  simplifyBool: {
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
        '==>': {
            T: 'T ==> T == T',
            F: 'T ==> F == F'
          },
          F: {
            T: 'F ==> T == T',
            F: 'F ==> F == T'
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
      var boolOps = {'=': true, '&': true, '|': true, '==>': true};
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
  },

  // Adds an assumption to the given step.  Works with or without
  // hypotheses.
  addAssumption: {
    action: function(step, expr) {
      if (step.hasHyps) {
        var step0 = rules.asImplication(step);
        var taut = rules.tautology('(p ==> q) ==> (p & a ==> q)');
        var map = {p: step.getLeft(), q: step.getRight(), a: expr};
        var step1 = rules.tautInst(taut, map);
        var step2 = rules.modusPonens(step0, step1);
      } else {
        var taut = rules.tautology('p ==> (a ==> p)');
        var map = {p: step, a: expr};
        var step1 = rules.tautInst(taut, map);
        var step2 = rules.modusPonens(step, step1);
      }
      return step2.asHyps().justify('addAssumption', arguments, [step]);
    },
    inputs: {step: 1, term: 2},
    form: ('Add assumption <input name=term> in step <input name=step>'),
    hint: 'add assumption',
    description: 'add assumption {term};; {in step step}'
  },

  // Given a theorem and an arbitrary boolean term, proves that the
  // term implies the theorem.  Note that theorems do not have
  // hypotheses.
  anyImpliesTheorem: {
    action: function(any, theorem) {
      assert(!theorem.hasHyps, function() {
          return 'Expecting a theorem, got: ' + theorem.getRight();
        },
        theorem);
      var step1 = rules.toTIsA(theorem);
      var step2 = rules.tautInst('p ==> T', {p: any});
      var step3 = rules.r(step1, step2, '/right');
      return step3.justify('anyImpliesTheorem', arguments, [theorem]);
    },
    inputs: {term: 1, step: 2},
    form: ('Derive that <input name=term> implies theorem <input name=step>'),
    hint: '[q] to [p ==> q]',
    comment: ('Given a theorem, derive that something implies it.'),
    labels: 'uncommon'
  },

  // Given a variable v that is not free in the given wff A, and a wff B, derive
  // ((forall {v. A | B}) ==> A | (forall {v. B})).  Could run even if
  // the variable is free, but would not give desired result.
  // This is Axiom Schema 5 of Andrews' first-order logic F.
  //
  // TODO: Prove a theorem schema for removing quantification over terms
  // that do not depend on the bound variable.  Something like:
  // {v. f A B} c = f A ({v. B} c) where v is not free in f or a.
  r5235: {
    action: function(v, a, b) {
      v = Toy.varify(v);
      var aFree = a.freeNames();
      assert(!aFree.hasOwnProperty(v.name),
	     'r5235: variable ' + v + 'cannot occur free in ' + a);
      var map1 = {
        p: call('forall', lambda(v, call('|', T, b))),
        q: call('forall', lambda(v, b))
      };
      var step1 = rules.tautInst('p ==> T | q', map1);
      var step2 = rules.tautInst('p ==> F | p',
                                 ({p: call('forall', lambda(v, b))}));
      var step3 = rules.tautInst('p == F | p',
                                 ({p: b}));
      var step4 = rules.r(step3, step2, '/left/arg/body');

      var freeNames = $.extend({}, aFree, b.freeNames());
      // Treat v as a free variable also.
      freeNames[v.name] = true;
      var p0 = Toy.genVar('p', freeNames);
      var step5 = rules.cases(step1, step4, p0);
      var step6 = rules.instVar(step5, a, p0);
      return step6.justify('r5235', arguments);
    },
    inputs: {varName: 1, term: [2, 3]},
    /* Do not show, hard to use and seldom helpful.
    form: ('Variable: <input name=varName> '
	   + 'wff without it free: <input name=term1> '
	   + 'other wff: <input name=term2>'),
    */
    labels: 'uncommon',
    comment: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".'),
    description: 'move forall'
  },

  // Given a proof step H |- A ==> B and a variable v, derives
  // H |- (A ==> forall {v. B}) provided that v is not free in A or H.
  // (5237)  This version implemented via 5235, so much less efficient.
  //
  // Handles hypotheses.
  implyForallBook: {
    action: function(v, h_a_b) {
      var a_b = h_a_b.unHyp();
      v = Toy.varify(v);
      assert(a_b.isCall2('==>'), 'Must be an implication: ' + a_b, h_a_b);
      var a = a_b.getLeft();
      var b = a_b.getRight();
      // Restriction to ensure the desired result.
      assert(!a.hasFreeName(v.name),
	     'implyForall: variable ' + v + 'cannot occur free in ' + a, h_a_b);
      if (h_a_b.hasHyps) {
	assert(!h.hasFreeName(v.name),
	       'implyForall: variable ' + v + 'cannot occur free in ' + h,
	       h_a_b);
      }
      var map1 = {a: a, b: b};
      var step1 = rules.tautInst('(a ==> b) ==> not a | b', map1);
      var step2 = rules.modusPonens(h_a_b, step1);
      var step3 = rules.addForall(step2, v);
      var step4 = rules.r5235(v, call('not', a), b);
      var step5 = rules.modusPonens(step3, step4);
      var map6 = {a: a, b: step5.locate('/main/right')};
      var step6 = rules.tautInst('not a | b ==> (a ==> b)', map6);
      var step7 = rules.modusPonens(step5, step6);
      return step7.justify('implyForallBook', arguments, [h_a_b]);
    },
    inputs: {varName: 1, implication: 2},
    /* Do not offer at this time, use implyForall instead.
    form: ('Move forall inside "implies" binding '
	   + 'variable <input name=varName> '
	   + 'implication <input name=implication>'),
    */
    comment: ('Move "forall" inside "implies" provided the variable '
              + 'is not free in the first argument.'),
    description: 'move forall'
  },

  // Given a variable v that is not free in the given wff A, and a wff B, derive
  // ((forall {v. A ==> B}) ==> (A ==> forall {v. B})).  Could run even if
  // the variable is free, but would not give desired result.
  implyForallThm: {
    action: function(v, a, b) {
      v = Toy.varify(v);
      var aFree = a.freeNames();
      assert(!aFree.hasOwnProperty(v.name),
	     'r5235: variable ' + v + 'cannot occur free in ' + a);
      var map1 = {
        p: call('forall', lambda(v, Toy.infixCall(F, '==>', b))),
        q: call('forall', lambda(v, b))
      };
      var step1 = rules.tautInst('p ==> (F ==> q)', map1);
      var step2 = rules.tautInst('p ==> (T ==> p)',
                                 ({p: call('forall', lambda(v, b))}));
      var step3 = rules.tautInst('p == (T ==> p)',
                                 ({p: b}));
      var step4 = rules.r(step3, step2, '/left/arg/body');

      var freeNames = $.extend({}, aFree, b.freeNames());
      // Treat v as a free variable also.
      freeNames[v.name] = true;
      var p0 = Toy.genVar('p', freeNames);
      var step5 = rules.cases(step4, step1, p0);
      var step6 = rules.instVar(step5, a, p0);
      return step6.justify('implyForallThm', arguments);
    },
    inputs: {varName: 1, term: [2, 3]},
    form: ('Variable: <input name=varName> '
	   + 'wff without it free: <input name=term1> '
	   + 'other wff: <input name=term2>'),
    hint: 'forall {v. A ==> B} ==> (A ==> forall {v. B}',
    comment: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".'),
    description: 'move forall',
    labels: 'uncommon'
  },

  // Given a proof step H |- A ==> B and a variable v, derives
  // H |- (A ==> forall {v. B}) provided that v is not free in A or H.
  // (5237)  Implemented via implyForallThm.
  //
  // Handles hypotheses.
  implyForall: {
    action: function(v, h_a_b) {
      v = Toy.varify(v);
      var a_b = h_a_b.unHyp();
      var step1 = rules.addForall(h_a_b, v);
      var step2 = rules.implyForallThm(v, a_b.getLeft(), a_b.getRight());
      var step3 = rules.modusPonens(step1, step2);
      return step3.justify('implyForall', arguments, [h_a_b]);
    },
    inputs: {varName: 1, implication: 2},
    form: ('Move forall inside "implies" binding '
	   + 'variable <input name=varName> '
	   + 'implication <input name=implication>'),
    hint: 'Move "forall" inside "implies"',
    comment: ('Move "forall" inside "implies" provided the variable '
              + 'is not free in the first argument.'),
    description: 'move forall'
  },
    
  // Rule P/Q for a single antecedent (5234).  The schema step must
  // have the form (A ==> B), where A matches the given input step and
  // all free variables of B are also free in A.  For tautologies with
  // a conjunction on the LHS as shown in the book, use this with
  // makeConjunction.  The step may have hypotheses, which are not
  // matched against the schema.
  //
  // Andrews calls his enhanced version of forward chaining "Rule P".
  // (In this implementation it is more straightforward to use
  // makeConjunction as needed, followed by forwardChain.)
  forwardChain: {
    action: function(step, schema) {
      var substitution = step.unHyp().matchSchema(schema.unHyp().getLeft());
      assert(substitution, function() {
          return (step.unHyp().toString() +
                  ' does not match LHS of schema\n' + schema);
        }, step);
      var step2 = rules.instMultiVars(schema, substitution);
      var step3 = rules.modusPonens(step, step2);
      return step3.justify('forwardChain', arguments, [step, schema]);
    },
    inputs: {step: [1, 2]},
    form: ('Match step <input name=step1> with left side of implication '
           + 'in schema <input name=step2>'),
    comment: ('[p] and [p ==> q] to q'),
    description: 'consequence;; of step {step1} using step {step2}'
  },

  // Proves the goal by matching it with the conclusion of the given
  // theorem and then applying the given inference rule to prove the
  // premise of the instantiated theorem.  The theorem must be a
  // conditional.
  //
  // TODO: Test me.
  backwardChain: {
    action: function(goal, theorem, rule) {
      theorem.assertCall2('==>');
      var subst = goal.matchSchema(theorem.getRight());
      var premise = rule(theorem.getLeft());
      var result = rules.modusPonens(premise,
                                     rules.instMultiVars(theorem, subst));
      var result = rules.instMultiVars(theorem, subst);
      return result.justify('backwardChain', arguments);
    }
  },

  // Instantiates the schema so that the part at the given path is
  // identical to the given term.
  //
  // TODO: Change "subgoal" to "expandRight"; create similar "expandLeft".
  instantiate: {
    action: function(schema, path, term) {
      var expr = schema.locate(path);
      var subst = term.matchSchema(expr);
      assert(subst, function() {
          return 'Schema ' + expr + ' should match ' + term;
        });
      var result = rules.instMultiVars(schema, subst);
      return result.justify('instantiate', arguments, [schema]);
    }
  },

  // Finds a "subgoal" statement that implies the goal via the given
  // theorem, which must be a schema of the form a ==> b.
  // Instantiates the theorem by matching the goal against the theorem
  // RHS, returning the instantiated theorem.  Returns null if the
  // theorem does not match the goal.
  subgoal: {
    action: function(goal, theorem) {
      theorem.assertCall2('==>');
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
  r5238: {
    action: function(vars, a, b) {
      assert(vars.concat, 'Variables must be an array: ' + vars);
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
    comment: ('Equal functions equate to equal expression values.')
  },

  // "Base case" of 5238, with just a single variable.
  r5238a: {
    action: function(v, a, b) {
      v = varify(v);
      var step2 = rules.axiom('axiom3');
      var step3 = rules.instMultiVars(step2,
                               ({f: lambda(v, a),
                                 g: lambda(v, b)}));
      var step4 = rules.apply(step3, '/right/arg/body/left');
      var step5 = rules.apply(step4, '/right/arg/body/right');
      var step6 = rules.changeVar(step5, '/right/arg', v);
      // Do not "derive", leave this inline.
      return step6;
    },
    comment: ('')
  },

  // 5239, closely following the description and names in the book.
  // Analog to Rule R, expressed as an implication.  Theorem schema.
  //
  // Given equation A = B, target C, and a path relative to C, returns
  // a wff of the form "forall ... (A = B) ==> (C = D), where D is
  // obtained like the result of applying Rule R to A = B and C.  The
  // "forall" binds free variables of A = B that are bound at the
  // replacement location in C.
  r5239: {
    action: function(equation, target, path) {
      path = Toy.path(path);
      assert(equation.isCall2('='),
             'Expecting an equation, got: ' + equation,
	     equation);
      var step1 = rules.axiom('axiom2');
      var a = equation.getLeft();
      var b = equation.getRight();
      var boundNames = target.boundNames(path);
      Toy.removeExcept(boundNames, equation.freeNames());
      // Is this the full set of names?
      var t =
        Toy.genVar('t', $.extend({}, target.allNames(), equation.allNames()));
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
			    ({x: aBound, y: bBound, h: lambda(t, g)}));
      var step3 = rules.apply(step2, '/right/left');
      var step4 = step3;
      for (var i = 0; i < boundNameList.length; i++) {
        step4 = rules.apply(step4, Toy.path('/right/left').concat(path));
      }
      var step5 = rules.apply(step4, '/right/right');
      var step6 = step5;
      for (var i = 0; i < boundNameList.length; i++) {
        step6 = rules.apply(step6, Toy.path('/right/right').concat(path));
      }
      if (boundNameList.length == 0) {
        return step6.justify('r5239', arguments);
      }
      var step7 = rules.r5238(boundNameList, a, b);
      var step8 = rules.r(step7, step6, '/left');
      return step8.justify('r5239', arguments);
    },
    // The site need not be part of any proof step, a situation the UI
    // does not support.
    //
    // inputs: {site: 2, term: 1},  // The term is an equation
    // form: ('Enter an equation: <input name=term>'),
    comment: ('Analog to Rule R, expressed as an implication.')
  },

  // Like Rule R', based on 5240 (the Deduction Theorem).  The
  // proof here is a subset of the proof of 5240.
  //
  // h_equation is an equation implied by hypotheses, i.e. H ==> A = B.
  // h_c is a term implied by the same hypotheses, i.e. H ==> C.
  // The path is relative to h_c, and may include a special initial
  // segment 'main', which it interprets as 'right' if h_c has
  // hypotheses, otherwise ignoring it.
  //
  // Note: When generating a no-op equation, it is desirable to make
  // the LHS and RHS be the same object (and same as the target),
  // because rule R will recognize the no-op.
  //
  // For convenience applies rule R directly if the equation is really
  // an equation and not an implication.
  //
  // TODO: Support h_c_arg with assumptions and a leftward path by
  // ignoring that there are assumptions.
  replace: {
    action: function(h_equation_arg, h_c_arg, path) {
      var args = [h_equation_arg, h_c_arg, path];
      path = Toy.path(path, h_c_arg);
      var h_c = h_c_arg;
      var h_equation = h_equation_arg;
      if (h_equation.isCall2('=')) {
        // Allow "replace" to be used for situations where "r" is
        // applicable.  The case with hypotheses in h_c can be
        // considered as rule RR (5202).
        var result = rules.r(h_equation, h_c, path);
	return result.justify('replace', args,
                              [h_equation_arg, h_c_arg]);
      }
      // h_equation must have the form H ==> A = B
      assert(h_equation.isEquation(), function() {
          return 'Not an equation: ' + h_equation;
        }, h_equation_arg);

      if (h_c.hasHyps && path.isLeft()) {
        // We are replacing an assumption with something equal
        // that may add its own assumptions.
        var step1 = rules.asImplication(h_c)
          .replace(path, h_equation)
          .apply('asImplication');
        // Use the tautology to conjoin all of the assumptions.
        // Note that forward chaining would ignore the "a" part if
        // step1 had hypotheses.
        var taut = rules.tautology('a ==> (b ==> c) ==> (a & b ==> c)');
        var step2 = rules.forwardChain(step1, taut);
        var step3 = rules.conjunctionsMerger(step2.getLeft());
        var result = rules.r(step3, step2, '/left')
          .apply('asHypotheses');
        
        return result.justify('replace', args,
                              [h_equation_arg, h_c_arg]);
      }

      // Give the two WFFs the same hypotheses.
      h_c = rules.appendStepHyps(h_c, h_equation);
      h_equation = rules.prependStepHyps(h_equation, h_c_arg);

      // Normalize the hypotheses, but only if there is really
      // something to merge.  This detects that both inputs have been
      // transformed.
      if (h_c != h_c_arg && h_equation != h_equation_arg) {
        var merger = rules.conjunctionsMerger(h_c.getLeft());
        h_c = rules.r(merger, h_c, '/left');
        h_equation = rules.r(merger, h_equation, '/left');
      }

      // Now both wffs are implications with the same LHS.  Call it "h".
      var h = h_equation.getLeft();
      if (!h_c.hasHyps) {
	// If there are no hypotheses, we did not attempt to make the
	// LHS of the two input steps match.
	assert(h_c.getLeft().matches(h),
	       'LHS mismatch in "replace" rule',
	       h_c_arg);
      }

      // From here on work with implications directly, not hypotheses.
      h_equation = rules.asImplication(h_equation);
      h_c = rules.asImplication(h_c);

      // equation is A = B
      var equation = h_equation.getRight();
      var c = h_c.getRight();
      var a = equation.getLeft();
      var b = equation.getRight();

      // Path relative to c.  This is one segment shorter than the
      // input path, but is the same length if hyps were added to h_c
      // by appendStepHyps, i.e. h_equation_arg had them but not
      // h_c_arg.
      var cpath = (h_equation_arg.hasHyps && !h_c_arg.hasHyps
		   ? path
		   : path.getRight());
      var boundNames = c.boundNames(cpath);
      Toy.removeExcept(boundNames, equation.freeNames());
      var hypFreeNames = h.freeNames();
      var step1 = h_equation;
      for (var name in boundNames) {
	// Check the variable is not free in any hypotheses.
	// TODO: Do appropriate checking in 5235 and impliesForall as well.
        assert(!hypFreeNames.hasOwnProperty(name), function() {
          return 'Conflicting binding of ' + name + ' in ' + c;
        }, h_c_arg);
        var step1 = rules.implyForall(name, step1);
      }
      var step2 = rules.r5239(equation, c, cpath);
      var step3 = rules.makeConjunction(step1, step2);
      var tautology = rules.tautology('(p ==> q) & (q ==> r) ==> (p ==> r)');
      var step4 = rules.forwardChain(step3, tautology);
      var step5 = rules.makeConjunction(h_c, step4);
      var taut2 = rules.tautology('(h ==> p) & (h ==> (p = q)) ==> (h ==> q)');
      var result = rules.forwardChain(step5, taut2);
      if (h_c_arg.hasHyps || h_equation_arg.hasHyps) {
        result = rules.asHypotheses(result);
      }
      return result.justify('replace', args, [h_equation_arg, h_c_arg]);
    },
    inputs: {equation: 1, site: 2}, // plus constraints.
    form: ('Replace selection with right side of step <input name=equation>'),
    comment: 'replace term with equal term',
    description: 'replace {site};; {in step siteStep} {using step equation}',
    labels: 'algebra basic'
  },
    
  /**
   * Same as "replace", but replaces an occurrence in target of the right
   * side of the equation with its left side.  Accepts hypotheses.
   */
  rRight: {
    action: function(equation, target, path) {
      path = Toy.path(path);
      var rev = rules.eqnSwap(equation);
      var result = rules.replace(rev, target, path);
      return result.justify('rRight', arguments, [target, equation]);
    },
    inputs: {equation: 1, site: 2},
    form: ('Replace with left side of step <input name=equation>'),
    hint: 'replace term with equal term like A = x',
    comment: ('Replaces an occurrence of a term with an equal term,'
              + ' replacing right side with left side.'),
    description: 'replace {site};; {in step siteStep} {using step equation}',
    labels: 'algebra basic'
  },

  // Add hypotheses to the target step from hypStep.  This is key to
  // providing two steps with the same hypotheses in preparation for
  // applying various rules of inference.  If hypStep has no
  // hypotheses, the result is simply the target step.
  appendStepHyps: {
    action: function(target, hypStep) {
      if (hypStep.hasHyps) {
	if (target.hasHyps) {
	  if (target.getLeft().matches(hypStep.getLeft())) {
	    // Hyps are the same, so no change to the given step.
	    return target;
	  }
          var step = rules.asImplication(target);
	  var taut = Toy.parse('(h1 ==> p) ==> ((h1 & h2) ==> p)');
	  var subst = {
	    h1: step.getLeft(),
	    h2: hypStep.getLeft(),
	    p: step.getRight()
	  };
	  var step1 = rules.tautInst(taut, subst);
	  var step2 = rules.modusPonens(step, step1);
          // Rendering of result needs hypStep rendered, so include it as dep.
	  return (step2.asHyps()
                  .justify('appendStepHyps', arguments, [target, hypStep]));
	} else {
	  // The target does not have hyps.
	  var subst = {
	    p: target,
	    h2: hypStep.getLeft()
	  };
	  var step1 = rules.tautInst('p ==> (h2 ==> p)', subst);
	  var step2 = rules.modusPonens(target, step1);
          // Rendering of result needs hypStep rendered, so include it as dep.
          return (rules.asHypotheses(step2)
                  .justify('appendStepHyps', arguments, [target, hypStep]));
	}
      } else {
	// Don't do anything and don't display any new proof step.
	return target;
      }
    },
    inputs: {step: [1, 2]},
    hint: 'combine hypotheses',
    form: ('Add to step <input name=step1> hypotheses from step '
	   + '<input name=step2>'),
    description: 'add step {step2} assumptions {to step step1}',
    labels: 'uncommon'
  },

  // Prefix hypotheses from the hypStep to the target step.  Often
  // used together with appendStepHyps.  If hypStep has no hypotheses,
  // the result is simply the target step.
  prependStepHyps: {
    action: function(target, hypStep) {
      if (hypStep.hasHyps) {
        var step = rules.asImplication(target);
	if (target.hasHyps) {
	  if (step.getLeft().matches(hypStep.getLeft())) {
	    // Hyps are the same, so no change to the given step.
            // Don't show the call to this rule.
	    return step;
	  }
	  var taut = Toy.parse('(h2 ==> p) ==> ((h1 & h2) ==> p)');
	  var subst = {
	    h1: hypStep.getLeft(),
	    h2: step.getLeft(),
	    p: step.getRight()
	  };
	  var step1 = rules.tautInst(taut, subst);
	  var step2 = rules.modusPonens(step, step1);
          // Rendering of result needs hypStep rendered, so include it as dep.
          return (rules.asHypotheses(step2)
                  .justify('prependStepHyps', arguments, [target, hypStep]));
	} else {
	  var subst = {
	    p: step,
	    h1: hypStep.getLeft()
	  };
	  var step1 = rules.tautInst('p ==> (h1 ==> p)', subst);
	  var step2 = rules.modusPonens(step, step1);
          // Rendering of result needs hypStep rendered, so include it as dep.
          return (step2.asHyps()
                  .justify('prependStepHyps', arguments, [target, hypStep]));
	}
      } else {
	// Don't display this no-op inference step.
	return target;
      }
    },
    inputs: {step: [1, 2]},
    hint: 'combine hypotheses',
    form: ('To step <input name=step1> prefix the hypotheses of step '
	   + '<input name=step2>'),
    description: 'add step {step2} assumptions {to step step1}',
    labels: 'uncommon'
  },

  // Takes a proof step, a path, and a proved equation.  The part of
  // the step at the given path must match the LHS of the equation.
  // Replaces that part of the step with the appropriate instance of
  // the equation.  The step and equation may have hypotheses.
  rewrite: {
    action: function(step, path, equation) {
      var expr = step.locate(path);
      var map = expr.findSubst(equation.unHyp().getLeft());
      assert(map, function() {
          return (step.unHyp().toString() +
                  ' must be an instance of LHS of equation\n' + equation);
        }, step);
      var step1 = rules.instMultiVars(equation, map);
      var result = rules.replace(step1, step, path);
      return result.justify('rewrite', arguments, [step, equation]);
    },
    inputs: {site: 1, equation: 3},
    // In the UI use rewriteNumeric instead.
    // form: ('Rewrite the site using equation <input name=equation>'),
    hint: 'rewrite using an equation',
    description: 'rewrite {site};; {in step siteStep} {using step equation}',
    labels: 'advanced'
  },

  // Rewrite a term using an equational fact, taking a statement of
  // the desired fact as an argument term (string or Expr).  indirect
  // use with well-known facts.  This simplifies assumptions including
  // numeric type assumptions after rewriting.
  //
  // TODO: Combine both sorts of rewrite rules into one, so a rewrite
  // works well in code and UI with any form of fact or proof step.
  rewriteWithFact: {
    action: function(step, path, statement) {
      // Can throw; tryRule will report any problem.
      var fact = rules.fact(statement);
      var expr = step.locate(path);
      var map = expr.findSubst(fact.unHyp().getLeft());
      assert(map, function() {
          return ('Sorry, term\n' +
                  expr.toString() +
                  '\n does not match LHS of\n' +
                  fact.unHyp().toString());
        }, step);
      var step1 = rules.instMultiVars(fact, map);
      var step2 = rules.replace(step1, step, path);
      var result = rules.simplifyAssumptions(step2);
      // Does not include the fact as a dependency, so it will not
      // display as a separate step.
      return result.justify('rewriteWithFact', arguments, [step]);
    },
    inputs: {site: 1, term: 3},
    form: ('Rewrite the selection using fact <input name=term>'),
    hint: 'rewrite using a fact',
    isRewriter: true,
    description: '{in step siteStep} use;; {shortFact}'
  },

  // Variant of "rewrite" that simplifies numeric types after applying
  // the fact.
  rewriteNumeric: {
    action: function(step, path, equation) {
      var step1 = rules.rewrite(step, path, equation);
      var result = rules.simplifyAssumptions(step1);
      return result.justify('rewriteNumeric', arguments, [step, equation]);
    },
    inputs: {site: 1, equation: 3},
    form: ('Rewrite the site using equation <input name=equation>'),
    hint: 'match with an equation LHS',
    description: 'rewrite {site};; {in step siteStep} {using step equation}',
    labels: 'basic'
  },

  // Simplifies the main part of the given step using the axiom of
  // arithmetic and selected simplifying facts.  Returns its result
  // inline, just the input step if there is nothing to do.
  //
  // From the UI use a rule that calls this one.
  _simplifyMath1: {
    action: function(step, _path) {
      var next = step;
      var foundPath = 
        next.locate(_path).searchCalls(function(term, p) {
            return (Toy.normalReturn(rules.axiomArithmetic, term) && p);
          });
      if (foundPath) {
        return rules.arithmetic(next, _path.concat(foundPath.reverse()));
      }
      var facts = ['a - a = 0',
                   'a + 0 = a',
                   '0 + a = a',
                   'a * 1 = a',
                   '1 * a = a',
                   {stmt: 'a * (b * c) = a * b * c'},
                   {stmt: 'a * b * c = a * c * b',
                    where: '!subst.a.hasVars() && !subst.c.hasVars()'},
                   {stmt: 'a * b / c = a / c * b',
                    where: '!subst.a.hasVars() && !subst.c.hasVars()'},
                   {stmt: 'a + b + c = a + (b + c)',
                    where: '!subst.b.hasVars() && !subst.c.hasVars()'},
                   {stmt: 'a + b - c = a + (b - c)',
                    where: '!subst.b.hasVars() && !subst.c.hasVars()'},
                   {stmt: 'a - b + c = a - (b - c)',
                    where: '!subst.b.hasVars() && !subst.c.hasVars()'},
                   {stmt: 'a - b - c = a - (b + c)',
                    where: '!subst.b.hasVars() && !subst.c.hasVars()'},
                   '0 * a = 0',
                   'a * 0 = 0',
                   'a + b - b = a',
                   'a - b + b = a',
                   'a + neg b + b = a',
                   'a + b + neg b = a'
                   ];
      var info = findMatchingCall(step.locate(_path), facts);
      return (info
              ? rules.rewriteWithFact(step,
                                      _path.concat(info.path),
                                      info.stmt)
              : step);
    }
  },

  // Repeatedly applies simplifyMath1 to do trivial simplifications.
  doAllArithmetic: {
    action: function(step) {
      var visPath = step.pathToVisiblePart();
      var next = step;
      while (true) {
        var simpler = rules._simplifyMath1(next, visPath);
        if (simpler === next) {
          return next.justify('doAllArithmetic', arguments, [step]);
        }
        next = simpler;
      }
    },
    inputs: {step: 1},
    form: ('Simplify step <input name=step>'),
    hint: 'algebra: simplify',
    description: 'basic simplification;; {in step step}',
    labels: 'algebra',
  },

  // Move all negations in past additions and multiplications;
  // eliminate double negations.
  simplifyNegations: {
    action: function(step) {
      var facts = ['neg (a + b) = neg a + neg b',
                   'neg (neg a) = a',
                   'neg (a * b) = neg a * b'
                  ];
      var simpler = applyToVisible(step, facts);
      var path1 = step.pathToVisiblePart();
      var schemas = [{match: 'neg a', where: 'subst.a.isNumeral()'}];
      while (true) {
        var info = findMatchingCall(simpler.locate(path1), schemas);
        if (!info) {
          break;
        }
        simpler = rules.arithmetic(simpler, path1.concat(info.path));
      }
      return simpler.justify('simplifyNegations', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Simplify negations in <input name=step>'),
    hint: 'algebra: simplify negations',
    description: 'simplify negations',
    labels: 'algebra'
  },

  // Remove occurrences of subtraction by adding the negative,
  // and simplifies negations.
  removeSubtraction: {
    action: function(step) {
      var facts = ['a - b = a + neg b'];
      var info = {facts: facts, searchMethod: 'searchTerms'};
      var converted = applyToVisible(step, info);
      var simplified = rules.simplifyNegations(converted);
      return simplified.justify('removeSubtraction', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Convert - to + in step <input name=step>'),
    hint: 'algebra: convert - to +',
    description: 'convert subtraction to addition',
    labels: 'algebra'
  },

  cleanUpTerms: {
    action: function(step) {
      var facts = ['a * (b * c) = a * b * c',
                   {stmt: 'a * b = b * a',
                    where: '!subst.b.hasVars() && subst.a.hasVars()'},
                   {stmt: 'a * b * c = a * (c * b)',
                    where: '!subst.c.hasVars() && subst.b.hasVars()'},
                   {stmt: 'a * b / c = a / c * b',
                    where: '!subst.a.hasVars() && !subst.c.hasVars()'}
                  ];
      var result = applyToVisible(step, facts);
      return result.justify('cleanUpTerms', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Clean up the terms in step <input name=step>'),
    hint: 'algebra: clean up terms',
    description: 'clean up each term',
    labels: 'algebra'
  },

  regroupAdditions: {
    action: function(step) {
      function applyTo(eqn, facts) {
        return applyFactsToRhs(eqn, {facts: facts,
                                     searchMethod: 'searchTerms'});
      }
      function convert(eqn) {
        // Linearize terms.
        var eqn0 = applyTo(eqn, [{stmt: 'a + (b + c) = a + b + c'}]);

        // Move terms that are numerals to the back of the bus.
        var facts1 = [{stmt: 'a + b = b + a',
                       where: '!subst.a.hasVars() && subst.b.hasVars()'},
                      {stmt: 'a + b + c = a + c + b',
                       where: '!subst.b.hasVars() && subst.c.hasVars()'}
                     ];
        var eqn1 = applyTo(eqn0, facts1);

        // Group numerals together.
        var facts2 = [{stmt: 'a + b + c = a + (b + c)',
                       where: '!subst.b.hasVars()'}
                     ];
        var eqn2 = applyTo(eqn1, facts2);

        // These come from rules.cleanupTerms.
        var cleanFacts = ['a * (b * c) = a * b * c',
                          {stmt: 'a * b = b * a',
                           where: '!subst.b.hasVars() && subst.a.hasVars()'},
                          {stmt: 'a * b * c = a * (c * b)',
                           where: '!subst.c.hasVars() && subst.b.hasVars()'},
                          {stmt: 'a * b / c = a / c * b',
                           where: '!subst.a.hasVars() && !subst.c.hasVars()'}
                         ];
        var eqn2a = applyTo(eqn2, cleanFacts);

        // Group terms with common right factor together.
        var facts3 = [{stmt: 'a * c + b * c = (a + b) * c'},
                      {stmt: 'b + a * b = (1 + a) * b'},
                      {stmt: 'a * b + b = (a + 1) * b'},
                      {stmt: 'a + a = 2 * a'}
                     ];
        return applyTo(eqn2a, facts3);
      }
      var result = convertAndReplace(step, step.pathToVisiblePart(), convert);
      return result.justify('regroupAdditions', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Regroup additive terms in step <input name=step>',
    hint: 'algebra: regroup additive terms',
    description: 'regroup additive terms',
    labels: '?'
  },

  /**
   * Regroup both addition and subtraction.
   *
   * TODO: make something like this that doesn't remove all
   *   subtraction.
   */
  regroup: {
    action: function(step) {
      return rules.removeSubtraction(step)
      .apply('regroupAdditions')
      .justify('regroup', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Regroup terms in step <input name=step>',
    hint: 'algebra: regroup terms',
    description: 'regroup terms',
    labels: 'algebra'
  },

  /** TODO: Decide whether to keep or remove this rule.
  removeRightTerm: {
    action: function(step, path) {
      // This rule assumes that the step has the form
      // H ==> lhs = rhs
      //
      var term = step.locate(path);
      assert(!step.rendering.hasLeftElision,
             'Not supported: would modify hidden equation left side');
      var xp = path.expand().toString();
      // Path to outer term of the form (A + <term>)
      var outPath;
      if (xp === '/arg/fn/arg/arg') {
        // Path is /main/left/right.
        var op = step.locate('/main/left/binop');
        assert(op.name === '+' || op.name === '-',
               'Operator needs to be + or -');
        outPath = Toy.path('/main/left');
      } else if (xp === '/arg/arg/arg') {
        // Path is /main/right/right.
        var op = step.locate('/main/right/binop');
        assert(op.name === '+' || op.name === '-',
               'Operator needs to be + or -');
        outPath = Toy.path('/main/right');
      } else {
        assert(false, function() {
            return ('Term needs to be on the right outside parentheses: '
                    + term);
          });
      }
      if (op.name === '+') {
        var result = rules.subtractFromBoth(step, term)
        .rewrite(outPath, 'a + b - c = a + (b - c)')
        .rewrite(outPath.concat('/right'), 'a - a = 0')
        .rewrite(outPath, 'a + 0 = a');
        return result.justify('removeRightTerm', arguments, [step]);
      } else {
        var result = rules.addToBoth(step, term)
        .rewrite(outPath, 'a - b + c = a + (c - b)')
        .rewrite(outPath.concat('/right'), 'a - a = 0')
        .rewrite(outPath, 'a + 0 = a');
        return result.justify('removeRightTerm', arguments, [step]);
      }
    },
    inputs: {site: 1},
    form: '',
    hint: 'move term to the other side',
    description: 'move term to the other side',
    labels: 'algebra'
  },
  */

  /* TODO: Choose a way to get varName into the "where" clauses,
   *   then finish this.
  regroupBy: {
    action: function(step, path, varName) {
      var facts = [{stmt: 'a + b = b + a',
                    where: 'subst.a.isNumeral() && !subst.b.isNumeral()'},
                   {stmt: 'a + b + c = a + c + b',
                    where: 'subst.b.isNumeral() && !subst.c.isNumeral()'}
                  ];
      var result = applyToVisible(step, facts);
      return result.justify('regroup', arguments, [step]);
    },
    inputs: {site: 1, varName: 3},
    form: 'Group terms with variable <input name=varName>',
    hint: 'algebra: group terms',
    description: 'group terms with {varName}'
  },
  */

  // Remove "T = " and "= T", evaluate boolean expression, do arithmetic.
  // Inline, throws if no simplification found.
  simplifySiteOnce: {
    action: function(step, path) {
      var facts = ['(T = x) = x', '(x = T) = x'];
      return Toy.each(facts, function(fact) {
          try {
            return rules.rewriteWithFact(step, path, fact);
          } catch(e) { }
        });
      try {
        return rules.arithmetic(step, path);
      } catch(e) { }
      throw new Error('No simplification found');
    },
    inputs: {site: 1},
    form: (''),
    hint: 'simplify the selected term'
  },

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
  bubbleLeft: {
    action: function(chain, less) {
      // This does all the work except the justification of the subproof.
      function bubble(eqn) {
        // TODO: Specialize the code slightly to work with hypotheses.
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
              rules.rewrite(eqn, '/right',
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
	    var step2 = rules.bubbleLeft(step1.locate('/right/left'), less);
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
	    return rules.rewrite(eqn, '/right',
                                 rules.tautology('a & a == a'));
	  } else if (less(b, a)) {
	    return rules.rewrite(eqn, '/right',
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
  mergeRight: {
    action: function(eqn) {
      var expr = eqn.getRight();
      // The merge step moves the last element of the left chain to
      // the end of the right chain.
      expr.assertCall2('&');
      var mover = (expr.getLeft().isCall2('&')
                   ? rules.tautology('(a & b) & c == a & (c & b)')
                   : rules.tautology('a & b == b & a'));
      var result = rules.rewrite(eqn, '/right', mover);
      return result.justify('mergeRight', arguments, [eqn]);
    },
  },

  // Internal rule for conjunctionsMerger, with a comparator parameter.
  mergeConj: {
    action: function(expr, less) {
      expr.assertCall2('&');
      var eqn = rules.eqSelf(expr);
      if (expr.getRight().isCall2('&')) {
        // The right chain is nontrivial, combine the chains.
        while (eqn.getRight().getLeft().isCall2('&')) {
	  // The left chain has at least 2 elements.
	  var eqn1 = rules.mergeRight(eqn);
	  var chain2 = eqn1.locate('/right/right');
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
  // and as its RHS has conjuncts ordered by sourceStepLess, with
  // duplicates eliminated.
  conjunctionsMerger: {
    action: function(expr) {
      // TODO: Consider whether this line needs to use Toy.hypIsless.
      var result = rules.mergeConj(expr, Toy.sourceStepLess);
      return result.justify('conjunctionsMerger', arguments);
    },
    inputs: {term: 1},
    // Too technical to expose for most users.
    // form: ('Chains of conjunctions to merge: <input name=term>'),
    hint: 'Derives an equation to merge chains of input conjunctions',
    description: 'merge conjunctions in {term}'
  },    

  // Extract the given hypothesis from the given step.  The hypothesis
  // need only match one of the step's hypotheses.  Relies on the step
  // to have normalized (flattened) hypotheses.  If the step is of the
  // form h1 ... hn ==> A, and h is one of the hypotheses, this
  // derives h1 ... hn ==> (h ==> A).
  //
  // TODO: Consider removing this. 
  extractHypothesis2: {
    // TODO: Make a version that runs in much less than exponential
    // time.  You can use the same tautology down to some depth and
    // combine it with ones resembling (h & h1) = (h & h1 & h) to
    // piece together larger tautologies.
    action: function(step, hyp) {
      var infix = Toy.infixCall;
      assert(step.hasHyps, 'Step has no hypotheses');
      var lhs = step.getLeft().hypLocater(hyp);
      var a = Toy.varify('a');
      var taut = infix(infix(lhs, '==>', a),
		       '==>',
		       infix(lhs,
			     '==>',
			     infix(Toy.varify('h'), '==>', a)));
      var step1 = rules.asImplication(step);
      var step2 = rules.forwardChain(step1, rules.tautology(taut));
      var result = rules.asHypotheses(step2);
      return result.justify('extractHypothesis2', arguments, [step]);
    },
    inputs: {step: 1, term: 2},
    form: ('Make assumption <input name=term> explicit '
           + 'in step <input name=step>'),
    description: 'make assumption {term} explicit;; {in step step}',
    labels: 'deprecated',
    comment: 'copy an assumption to the consequent'
  },

  // Given a proof step that is an implication and a path that
  // refers to an element of the LHS conjunction chain, derives a step
  // of the form h' ==> (e ==> c) where e is the referenced element,
  // h' is the proof step's hypotheses excluding occurrences of "e",
  // and c is the implication RHS.  Useful for simplifying hypotheses.
  isolateHypAt: {
    action: function(step, path) {
      var result = rules.isolateHyp(step, step.locate(path));
      return result.justify('isolateHypAt', arguments, [step]);
    },
    inputs: {site: 1},
    form: '',
    hint: 'move to conclusions',
    comment: 'move assumption to the conclusions',
    labels: 'uncommon'
  },

  // Like isolateHypAt, taking its hypotheses as a term to be matched.
  // Useful for isolating (extracting) implicit assumptions such as
  // variable types.
  isolateHyp: {
    action: function(step, hyp_arg) {
      var hyp = Toy.termify(hyp_arg);
      assert(step.isCall2('==>'));
      var taut = rules.tautology(step.getLeft().hypMover(hyp));
      var step1 = rules.rewrite(step, '/left', taut);
      var taut2 = rules.tautology('a & b ==> c == a ==> (b ==> c)');
      var result = rules.rewrite(step1, '', taut2);
      return result.justify('isolateHyp', arguments, [step]);
    },
    inputs: {step: 1, term: 2},
    form: 'extract assumption <input name=term> from step <input name=step>',
    comment: 'extract an assumption'
  },

  // Simplifies hyps ==> (a ==> b) to hyps & a ==> b. 
  useAsHyp: {
    action: function(step) {
      var taut = rules.tautology('a ==> (b ==> c) == a & b ==> c');
      var result = rules.rewriteWithFact(step, '', taut);
      return result.justify('useAsHyp', arguments, step);
    },
    inputs: {step: 1},
    form: 'step <input name=step>',
    hint: Toy.mathText('[h ==> (p ==> q)] to [h & p ==> q]'),
    labels: 'uncommon',
    description: 'absorb antecedent into the assumptions'
  },

  // Proves that the given chain of conjuncts imply the specific
  // conjunct "c", which must match one of them.
  conjunctsImplyConjunct: {
    action: function(conjuncts, c) {
      var infix = Toy.infixCall;
      var tautFX = rules.tautology('F & x == F');
      // Prove that "hyps = F", where hyps is a chain of conjuncts.
      // One conjunct must be "F".
      function falsify(hyps) {
        if (hyps.isCall2('&')) {
          if (hyps.getRight().matches(F)) {
            return rules.tautInst('p & F == F', {p: hyps.getLeft()});
          } else {
            var left = hyps.getLeft();
            var falsy = falsify(left);
            var eqn = rules.eqSelf(hyps);
            var step1 = rules.replace(falsy, eqn, '/right/left');
            return rules.rewrite(step1, '/right', tautFX)
          }
        } else if (hyps.matches(F)) {
          return rules.eqSelf(F);
        }
        assert(false, 'Bad input to falsify!');
      }
      var map = new Toy.TermMap();
      conjuncts.eachHyp(function (h) { map.addTerm(h); });
      assert(map.has(c), function() {
          return 'Must be one of the conjuncts: ' + c;
        });
      var cVar = map.get(c);
      // Make a schema for the desired theorem.
      var goalSchema = infix(buildHypSchema(conjuncts, map), '==>', cVar);
      // Make a version of the theorem with T for "c".
      var trueGoal = goalSchema.subFree(T, cVar);
      // This is a simple tautology:
      var trueCase = rules.tautInst('p ==> T', {p: trueGoal.getLeft()});
      // Make a version of the theorem with F for "c".
      var falseGoal = goalSchema.subFree(F, cVar);
      // Prove that its LHS is equal to F.
      var step1 = falsify(falseGoal.getLeft());
      // This means the LHS implies F, which is the desired F case.
      var taut = rules.tautology('p = F ==> (p ==> F)');
      var falseCase = rules.forwardChain(step1, taut);
      // Complete proof of the desired schema:
      var step2 = rules.cases(trueCase, falseCase, cVar);
      // Instantiate back to get the desired instance:
      var result = rules.instMultiVars(step2, map.subst);
      return result.justify('conjunctsImplyConjunct', arguments);
    }
  },

  // Treats conj as a chain of conjunctions.  Equates it with a
  // deduplicated version.  If a comparator function is supplied, it
  // defines an ordering of the deduplicated terms by returning true
  // when its first argument is less than its second.
  conjunctionDeduper: {
    action: function(conj, comparator) {
      var map = new Toy.TermMap();
      // A variable (or T) for each conjunct, in order of occurrence.
      var allTerms = [];
      conj.eachHyp(function(term) {
        if (term.matches(T)) {
          // Keep occurrences of T as-is in the inputs, and no output.
          allTerms.push(T);
        } else {
          allTerms.push(map.addTerm(term));
        }
      });
      var keepTermsInfo = [];
      var subst = map.subst;
      for (var name in subst) {
        keepTermsInfo.push({term: subst[name], name: name});
      }
      if (comparator) {
        function compare(a, b) { return comparator(a.term, b.term); }
        keepTermsInfo.sort(compare);
      }
      var keepTerms = [];
      keepTermsInfo.forEach(function(info) {
          keepTerms.push(new Toy.Var(info.name));
        });
      // A variable for each hypothesis to keep, in order.
      function buildConj(list) {
        var result = null;
        for (var i = 0; i < list.length; i++) {
          var term = list[i];
          result = result ? Toy.infixCall(result, '&', term) : term;
        }
        return result || T;
      }
      var rewriter =
        Toy.infixCall(buildConj(allTerms), '==', buildConj(keepTerms));
      var result = rules.instMultiVars(rules.tautology(rewriter), map.subst);
      return result.justify('conjunctionDeduper', arguments);
    }
  },

  // Derives a step with hypotheses deduplicated and ordered as by
  // sourceStepComparator, including removal of occurrences of T.
  // Works with hypotheses and with plain implications.
  dedupeHyps: {
    action: function(step) {
      step.assertCall2('==>');
      var deduper =
        rules.conjunctionDeduper(step.getLeft(), Toy.sourceStepComparator);
      var result = rules.replace(deduper, step, '/left');
      return result.justify('dedupeHyps', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    comment: 'remove redundant hypotheses',
    labels: 'uncommon'
  },

   // Prove an equation asserting that two chains of conjunctions are
   // equal by showing that their schemas are a tautology.
  equalConjunctions: {
    action: function(equation) {
      var termMap = new Toy.TermMap();
      var lhs = buildHypSchema(equation.getLeft(), termMap);
      var rhs = buildHypSchema(equation.getRight(), termMap);
      var taut = rules.tautology(Toy.infixCall(lhs, '=', rhs));
      return rules.tautInst(taut, termMap.subst);
    },
    inputs: {equation: 1},
    form: 'Equation of conjunctions: <input name=equation>',
    comment: 'prove equality of two chains of conjunctions',
    labels: 'uncommon'
  },


  // From the section "Equality and descriptions" in the book.

  equalitySymmetric: {
    action: function() {
      var step1 = rules.assume('x = y');
      var step2 = rules.eqSelf(x);
      var step3 = rules.replace(step1, step2, '/left');
      var step4 = rules.asImplication(step3);
      var subst = {x: y, y: x};
      var step5 = rules.instMultiVars(step4, subst);
      var step6 = rules.makeConjunction(step4, step5);
      var taut = rules.tautology('(p ==> q) & (q ==> p) ==> (p == q)');
      var step7 = rules.forwardChain(step6, taut);
      return step7.justify('equalitySymmetric', arguments);
    },
    inputs: {},
    form: '',
    description: 'symmetry of equality',
    comment: 'symmetry of equality',
    labels: 'basic'
  },

  equalityTransitive: {
    action: function() {
      var step1 = rules.axiom('axiom2');
      var step2 = rules.instVar(step1, Toy.parse('{t. t = z}'), varify('h'));
      var step3 = rules.apply(step2, '/right/left');
      var step4 = rules.apply(step3, '/right/right');
      var taut = rules.tautology('(a ==> (b = c)) ==> (a & c ==> b)');
      var step5 = rules.forwardChain(step4, taut);
      return step5.justify('equalityTransitive', arguments);
    },
    inputs: {},
    form: '',
    description: 'transitivity of equality',
    comment: 'transitivity of equality',
    labels: 'basic'
  },

  //
  // Real numbers
  // 
  // Assumptions (R x) & (R y), etc. are in the form:
  // (A1 ==> (A2 ==> <equation>)) to simplify introducing them from
  // the hypotheses.  This is equivalent to A1 & A2 ==> <equation>.

  axiomCommutativePlus: {
    action: function() {
      return rules.assert('R x & R y ==> x + y = y + x')
        .asHyps().justify('axiomCommutativePlus');
    },
    inputs: {},
    form: '',
    comment: 'commutativity of addition',
    description: 'commutativity of addition'
  },

  axiomAssociativePlus: {
    action: function() {
      return rules.assert('R x & R y & R z ==> x + (y + z) = (x + y) + z')
	.asHyps().justify('axiomAssociativePlus');
    },
    inputs: {},
    form: '',
    comment: 'associativity of addition',
    description: 'associativity of addition'
  },

  axiomCommutativeTimes: {
    action: function() {
      return rules.assert('R x & R y ==> x * y = y * x')
	.asHyps().justify('axiomCommutativeTimes');
    },
    inputs: {},
    form: '',
    comment: 'commutativity of multiplication',
    description: 'commutativity'
  },

  axiomAssociativeTimes: {
    action: function() {
      return rules.assert('R x & R y & R z ==> x * (y * z) = (x * y) * z')
	.asHyps().justify('axiomAssociativeTimes');
    },
    inputs: {},
    form: '',
    comment: 'associativity of multiplication',
    description: 'associativity of multiplication'
  },

  axiomDistributivity: {
    action: function() {
      return rules.assert('R x & R y & R z ==> x * (y + z) = x * y + x * z')
	.asHyps().justify('axiomDistributivity');
    },
    inputs: {},
    form: '',
    comment: 'distributive law',
    description: 'distributive law'
  },

  axiomPlusZero: {
    action: function() {
      return rules.assert('R x ==> x + 0 = x')
        .asHyps().justify('axiomPlusZero');
    },
    inputs: {},
    form: '',
    comment: 'x + 0 = x',
    description: 'additive identity'
  },

  axiomTimesOne: {
    action: function() {
      return rules.assert('R x ==> x * 1 = x')
        .asHyps().justify('axiomTimesOne');
    },
    inputs: {},
    form: '',
    comment: 'x * 1 = x',
    description: 'multiplicative identity'
  },

  axiomTimesZero: {
    action: function() {
      return rules.assert('R x ==> x * 0 = 0')
        .asHyps().justify('axiomTimesZero');
    },
    inputs: {},
    form: '',
    comment: 'x * 0 = 0',
    description: 'multiplication by 0'
  },

  axiomNeg: {
    action: function() {
      return rules.assert('R x ==> x + neg x = 0')
        .asHyps().justify('axiomNeg');
    },
    inputs: {},
    form: '',
    comment: 'x + neg x = 0',
    description: 'definition of negation'
  },

  axiomReciprocal: {
    action: function() {
      return rules.assert('R x & x != 0 ==> x * recip x = 1')
        .asHyps().justify('axiomReciprocal');
    },
    inputs: {},
    form: '',
    comment: 'x * recip x = 1 if x is not 0',
    description: 'recip is inverse to multiplication'
  },

  axiomReciprocal2: {
    action: function() {
      return rules.assert('R (recip x) & recip x != 0 == R x & x != 0')
        .justify('axiomReciprocal2');
    },
    inputs: {},
    form: '',
    comment: 'nonzero reciprocals',
    description: 'reciprocals are nonzero'
  },

  // TODO: Prove this as a consequnce of completeness.
  factNonzeroProduct: {
    action: function() {
      return rules.assert('R x & R y ==> (x * y != 0) = (x != 0 & y != 0)')
        .asHyps().justify('factNonzeroProduct');
    }
  },

  // All of the type axioms are true in actual type theory, but
  // in type theory the reciprocal is always a real number.

  // Note: not structured as a rewrite rule.
  axiomPlusType: {
    action: function() {
      return rules.assert('R x & R y ==> R (x + y)')
	.justify('axiomPlusType');
    },
    inputs: {},
    form: '',
    hint: 'axiom ' + Toy.parse('R (x + y)').toUnicode(),
    comment: 'sum of real numbers is real',
    description: 'sum of real numbers is real'
  },

  // Note: not structured as a rewrite rule.
  axiomTimesType: {
    action: function() {
      return rules.assert('R x & R y ==> R (x * y)')
	.justify('axiomTimesType');
    },
    inputs: {},
    form: '',
    hint: 'axiom ' + Toy.parse('R (x * y)').toUnicode(),
    comment: 'product of real numbers is real',
    description: 'product of real numbers is real'
  },

  axiomNegType: {
    action: function() {
      return rules.assert('R x == R (neg x)')
	.justify('axiomNegType');
    },
    inputs: {},
    form: '',
    hint: 'axiom ' + Toy.parse('R (neg x)').toUnicode(),
    comment: 'negation of real number is real',
    description: 'negation of real number is real'
  },

  // TODO: Replace me.
  axiomReciprocalType: {
    action: function() {
      return rules.assert('R x & x != 0 == R (recip x)')
	.justify('axiomReciprocalType');
    },
    inputs: {},
    hint: 'axiom ' + Toy.parse('x != 0 == R (recip x)').toUnicode(),
    form: '',
    comment: 'reciprocal of nonzero real number is real',
    description: 'reciprocal of real number'
  },

  // Evaluates arithmetic expressions with operators:
  // +, -, *, /, neg, =, !=, >, >=, <, <=, and the type operator "R".
  // Checks that inputs are all numeric and that the result can be
  // guaranteed to be an exact integer.
  axiomArithmetic: {
    action: function(term) {
      if (term.isInfixCall()) {
	var left = term.getLeft().getNumValue();
	var right = term.getRight().getNumValue();
	var op = term.getBinOp().name;
	var value;
	switch(op) {
        case '+': value = left + right; break;
        case '*': value = left * right; break;
        case '-': value = left - right; break;
        case '/':
          assert(right !== 0, 'Cannot divide by zero');
          value = left / right;
          // abs(value) <= abs(left) since abs(right) >= 1 so the
          // magnitude is not a problem.  The fractional part of a
          // result must have denominator no greater than MAX_INT,
          // so it should be distinguishable from an integer.
          assert(value === Math.floor(value), 'Inexact division');
          break;
        case '=': value = left === right; break;
        case '!=': value = left !== right; break;
        case '>': value = left > right; break;
        case '>=': value = left >= right; break;
        case '<': value = left < right; break;
        case '<=': value = left <= right; break;
        default:
          assert(false, 'Unsupported operator: ' + op);
	}
        if (typeof value == 'boolean') {
          var rhs = value ? T : F;
        } else {
          var value = Toy.checkRange(value);
          var rhs = new Toy.Var(value.toFixed(0));
        }
        return rules.assert(Toy.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else if (term instanceof Toy.Call) {
        var arg = term.arg.getNumValue();
        var op = term.fn;
        assert(op instanceof Toy.Var,
               function() { return 'Unsupported operator: ' + op; });
        if (op.name == 'neg') {
          value = -arg;
          var rhs = new Toy.Var(value.toFixed(0));
        } else if (op.name == 'R') {
          var rhs = T;
        } else {
          assert(false, 'Not an arithmetic expression: ' + term);
        }
        return rules.assert(Toy.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else {
	assert(false, 'Not an arithmetic expression: ' + term);
      }
    },
    inputs: {term: 1},
    form: 'Term to evaluate: <input name=term>',
    comment: 'evaluate arithmetic expression',
    description: 'axiom of arithmetic',
    labels: 'basic'
  },

  subtractionType: {
    action: function() {
      var step1 = rules.axiom('axiomPlusType');
      var step2 = rules.instVar(step1, Toy.parse('neg y'), 'y');
      var step3 = rules.axiom('axiomNegType');
      var step4 = rules.instVar(step3, y, x);
      var step5 = rules.rRight(step4, step2, '/left/right');
      var step6 = rules.eqSelf(Toy.parse('x - y'));
      var step7 = rules.apply(step6, '/left');
      var step8 = rules.replace(step7, step5, '/main/right/arg')
      return step8.justify('subtractionType');
    },
    form: '',
    hint: 'theorem R (x - y)',
    comment: 'difference of real numbers is real',
    description: 'difference of real numbers is real',
    labels: 'uncommon'
  },

  divisionType: {
    action: function() {
      var step1 = rules.axiom('axiomTimesType');
      var step2 = rules.instVar(step1, Toy.parse('recip y'), 'y');
      var step3 = rules.axiom('axiomReciprocalType');
      var step4 = rules.instVar(step3, y, x);
      var step5 = rules.rRight(step4, step2, '/left/right');
      var step6 = rules.eqSelf(Toy.parse('x / y'));
      var step7 = rules.apply(step6, '/left');
      var step8 = rules.replace(step7, step5, '/main/right/arg')
      // TODO: Normalize the assumptions automatically, not by hand.
      var step9 = rules.rewrite(step8, '/left',
                                rules.tautology('a & (b & c) == c & a & b'));
      return step9.justify('divisionType');
    },
    form: '',
    hint: 'theorem R (x / y)',
    comment: 'quotient of real numbers is real',
    description: 'quotient of real numbers is real',
    labels: 'uncommon'
  },

  //
  // Inference rules for real numbers
  //

  // Rewrites a simple arithmetic expression to its value.
  arithmetic: {
    action: function(step, path) {
      var term = step.locate(path);
      var result;
      if (term.isCall2('!=') &&
          term.getLeft().isNumeral() &&
          term.getRight().isNumeral()) {
        var step1 = rules.eqSelf(term);
        var step2 = rules.apply(step1, '/right');
        var step3 = rules.arithmetic(step2, '/right/arg');
        // Derive "<n> != 0 == T"
        var step4 = rules.evalBool(step3.getRight());
        // RHS of step4 becomes "T".
        var step5 = rules.r(step4, step3, '/right');
        // Replace the original expression.
        result = rules.r(step5, step, path);
      } else {
        try {
          var equation = rules.axiomArithmetic(term);
          result = rules.r(equation, step, path);
        } catch(e) {
          assert(false, 'Not an arithmetic expression: ' + term);
        }
      }
      return result.justify('arithmetic', arguments, [step]);
    },
    isRewriter: true,
    inputs: {site: 1},
    form: '',
    comment: 'arithmetic',
    labels: 'algebra'
  },

  // Managing numeric type hypotheses

  rewriteInDepth: {
    action: function(step, path, facts) {
      var equation = rules.deepTermReplacer(step.locate(path), facts);
      var result = rules.replace(equation, step.locate(path));
      return result.justify('rewriteInDepth', arguments);
    },
  },    

  // Proves an equation that can replace the given term.  Applies the
  // given List of equational facts recursively, traversing the term
  // bottom-up, applying the first fact that succeeds to each
  // subexpression.  Returns an equation with the term on the LHS and
  // the replacement on the right.
  //
  // TODO: Extend to take a conversion function in place of the facts.
  deepTermReplacer: {
    action: function(term, facts) {
      var step = rules.eqSelf(term);
      var step1;
      if (term instanceof Call) {
        var stepFn = rules.deepTermReplacer(term.fn, facts);
        var stepArg = rules.deepTermReplacer(term.arg, facts);
        step1 = step.replace('/right/fn', stepFn)
          .replace('/right/arg', stepArg);
      } else {
        step1 = step;
      }
      var result = Toy.each(facts, function(fact) {
          try {
            return step1.rewrite('/right', fact);
          } catch(e) {}
        });
      result = result || step1;
      return result.justify('deepTermReplacer', arguments);
    }
  },

  // Proves an equation that can replace the given boolean term.
  // Applies itself recursively to the given List of equational facts,
  // descending into the arguments of conjunctions (a & b), bottom-up,
  // applying the first fact (if any) that succeeds to each subexpression.
  // Returns an equation with the term on the LHS and the replacement
  // on the right.
  //
  // TODO: Extend to take a conversion function in place of the facts.
  conjunctsSimplifier: {
    action: function(term, facts) {
      var step = rules.eqSelf(term);
      var step1;
      if (term.isCall2('&')) {
        var stepLeft = rules.conjunctsSimplifier(term.getLeft(), facts);
        var stepRight = rules.conjunctsSimplifier(term.getRight(), facts);
        step1 = step.replace('/right/left', stepLeft)
          .replace('/main/right/right', stepRight);
      } else {
        step1 = step;
      }
      var result = Toy.each(facts, function(fact) {
          try {
            return step1.rewrite('/right', fact);
          } catch(e) {}
        }) || step1;
      try {
        result = result.rewrite('/main/right',
                                rules.tautology('a & (b & c) == a & b & c'));
      } catch(e) {}
      return result.justify('conjunctsSimplifier', arguments);
    }
  },

  // Given a step that is a conditional, proves a version with the
  // assumptions simplified.  Reduces assumptions about "R" type of
  // expressions with arithmetic operators to assumptions about "R"
  // type of variables; removes assumptions that specific numerals are
  // real or nonzero; simplifies assumptions about products being
  // nonzero into assertions that both operands are real; removes
  // duplicate terms and occurrences of T.
  simplifyAssumptions: {
    action: function(step) {
      if (!step.isCall2('==>')) {
        // Shortcut inline return.
        return step;
      }
      // From a conditional a ==> b, prove a ==> (b == T).
      // Returns a memoized function that yields the proved result.
      function proveIsT(stmt) {
        return memo(function() {
            return stmt.apply('asHypotheses').apply('toTIsA').apply('eqnSwap');
          });
      }
      //
      // All of these facts are returnable from getArithOp, below.
      //
      var numeraler = function(expr) {
        // We can't memoize this one because a different fact is needed
        // for each different numeral.
        assert(expr.isCall1('R'));
        return rules.axiomArithmetic(call('R', expr.arg));
      };
      var adder = proveIsT(rules.axiom('axiomPlusType'));
      var multiplier = proveIsT(rules.axiom('axiomTimesType'));
      var subtracter = proveIsT(rules.subtractionType());
      var divider = proveIsT(rules.divisionType());
      var negger = memo(function() {
          return rules.axiom('axiomNegType').apply('eqnSwap');
        });
      // x != 0 ==> (R (recip x) == R x)
      var reciper = memo(function() {
          var step = rules.axiom('axiomReciprocalType');
          var schema = rules.tautology('(a & b == c) ==> (b ==> (c == a))');
          var step2 = rules.forwardChain(step, schema);
          var result = rules.asHypotheses(step2);
          return result;
        });
      var binOps = {'+': adder, '*': multiplier,
                    '-': subtracter, '/': divider};
      binOps = Toy.ownProperties(binOps);
      var unOps = {neg: negger, recip: reciper};
      unOps = Toy.ownProperties(unOps);
      //
      // Returns the appropriate memoized rule/fact for this type
      // expression or else a falsy value.  Each fact must have the
      // form h ==> (R <expr>) = <expr2> with h as hypotheses, or just
      // (R <expr>) = <expr2>.
      function getArithOp(expr) {
        // TODO: Handle numeral arguments to R here,
        //   and direct calls of != with numerals.
        if (expr.isCall1('R')) {
          var arg = expr.arg;
          return (arg.isNumeral()
                  ? numeraler
                  : arg.isBinOp()
                  ?  binOps[arg.getBinOp()]
                  : arg.isCall1()
                  ? unOps[arg.fn]
                  : null);
        } else {
          // If it's an arithmetic expression simplifiable by the
          // axiom of arithmetic, return a function that returns
          // the appropriate statement.
          try {
            var result = rules.axiomArithmetic(expr);
            return function() { return result; };
          } catch(e) {}
          if (expr.matchSchema('x * y != 0')) {
            // Simplify statements about nonzero products.
            return memo(function() { return rules.factNonzeroProduct(); });
          }
          if (expr.matchSchema('recip x != 0')) {
            // Simplify statements about nonzero reciprocals.
            return proveIsT(rules.fact('@R a & a != 0 ==> recip a != 0'));
          }
        }
        return null;
      }
      // Finds and returns a path to a conjunct in the given term that
      // passes the test, or returns null.
      function findConjunct(term, test) {
        var Path = Toy.Path;
        function find(term, revPath) {
          if (test(term)) {
            return revPath;
          } else if (term.isCall2('&')) {
            return find(term.getLeft(), new Path('left', revPath))
              || find(term.getRight(), new Path('right', revPath));
          } else {
            return null;
          }
        }
        var rpath = find(term, Toy.path(''));
        return rpath ? rpath.reverse() : null;
      }
      function simplifyHyps(stepArg) {
        if (!stepArg.isCall2('==>')) {
          return stepArg;
        }
        var step = stepArg;
        // Repeatedly replace assumptions that match some rule
        // from getArithOp until there is none.
        while (true) {
          var hyps = step.getLeft();
          var hypsPath = findConjunct(hyps, getArithOp);
          if (!hypsPath) {
            return step;
          }
          var path = new Toy.Path('left', hypsPath);
          var expr = step.locate(path);
          var fact = getArithOp(expr)(expr);
          var simpleFact =
            simplifyHyps(rules.instantiate(fact, '/main/left', expr));
          step = rules.replace(simpleFact, step, path);
        }
      }
      return (simplifyHyps(step)
              .apply('dedupeHyps')
              .justify('simplifyAssumptions', arguments, [step]));
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    comment: 'simplify assumptions in a step',
    hint: 'simplify assumptions',
    labels: 'uncommon'
  },

  // Consider a term that we may wish to rewrite.  If the term has no
  // arithmetic operators, this is the same as eqSelf, but it
  // automatically assumes variables input to math operators are of
  // type R (real).
  consider: {
    description: 'expression to consider',
    action: function(term) {
      term = Toy.termify(term);
      var step = rules.eqSelf(term);
      var conditions = term.mathVarConditions();
      if (conditions) {
        step = rules.anyImpliesTheorem(conditions, step);
        step = rules.asHypotheses(step);
      }
      return step.justify('consider', arguments);
    },
    inputs: {term: 1},
    form: 'Term to consider: <input name=term>',
    hint: 'consider a term to transform',
    comment: ('consider a term to transform'),
    labels: 'basic'
  },

  // Similar to "consider", but uses a selected term.
  // The new step inherits hypotheses from the input step.
  considerPart: {
    action: function(step, path) {
      var eqn = rules.eqSelf(step.locate(path));
      var result = (step.hasHyps
                    ? (rules.anyImpliesTheorem(step.getLeft(), eqn)
                       .apply('asHypotheses'))
                    : eqn);
      return result.justify('considerPart', arguments);
    },
    inputs: {site: 1},
    form: '',
    comment: ('consider the selected term'),
    description: 'consider term for transformation',
    labels: 'display'
  },

  addToBoth: {
    action: function(eqn, term_arg) {
      var term = Toy.termify(term_arg);
      var x = term.freshVar();
      var fn = lambda(x, Toy.infixCall(x, '+', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('addToBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Add <input name=term> to both sides of ' +
           'step <input name=equation>'),
    hint: 'algebra: add to both sides',
    comment: ('add to both sides'),
    description: 'add {term};; {in step equation}',
    labels: 'algebra'
  },

  subtractFromBoth: {
    action: function(eqn, term_arg) {
      var term = Toy.termify(term_arg);
      var x = term.freshVar();
      var fn = lambda(x, Toy.infixCall(x, '-', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('subtractFromBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Subtract <input name=term> from both sides of ' +
           'step <input name=equation>'),
    hint: 'algebra: subtract from both sides',
    comment: ('subtract from both sides'),
    description: 'subtract {term};; {in step equation}',
    labels: 'algebra'
  },

  multiplyBoth: {
    action: function(eqn, term) {
      var x = term.freshVar();
      var fn = lambda(x, Toy.infixCall(x, '*', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('multiplyBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Multiply both sides of step <input name=equation>' +
           ' by <input name=term>'),
    hint: 'algebra: multiply both sides',
    comment: ('multiply both sides'),
    description: 'multiply by {term};; {in step equation}',
    labels: 'algebra'
  },

  divideBoth: {
    action: function(eqn, term) {
      var x = term.freshVar();
      var fn = lambda(x, Toy.infixCall(x, '/', term));
      var result = rules.applyToBoth(fn, eqn)
        .apply('addAssumption', Toy.infixCall(term, '!=', zero))
        .apply('simplifyAssumptions');
      return result.justify('divideBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Divide both sides of step <input name=equation>' +
           ' by <input name=term>'),
    hint: 'algebra: divide both sides',
    comment: ('divide both sides'),
    description: 'divide by {term};; {in step equation}',
    labels: 'algebra'
  },

  addThisToBoth: {
    action: function(step, path) {
      var term = step.locate(path);
      return (rules.addToBoth(step, term)
              .justify('addThisToBoth', arguments, [step]));
    },
    inputs: {site: 1},
    form: '',
    hint: 'algebra: add this to both sides',
    description: 'add {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  subtractThisFromBoth: {
    action: function(step, path) {
      var term = step.locate(path);
      return (rules.subtractFromBoth(step, term)
              .justify('subtractThisFromBoth', arguments, [step]));
    },
    inputs: {site: 1},
    form: '',
    hint: 'algebra: subtract this from both sides',
    description: 'subtract {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  multiplyBothByThis: {
    action: function(step, path) {
      var term = step.locate(path);
      return (rules.multiplyBoth(step, term)
              .justify('multiplyBothByThis', arguments, [step]));
    },
    inputs: {site: 1},
    form: '',
    hint: 'algebra: multiply both sides by this',
    description: 'multiply by {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  divideBothByThis: {
    action: function(step, path) {
      var term = step.locate(path);
      return (rules.divideBoth(step, term)
              .justify('divideBothByThis', arguments, [step]));
    },
    inputs: {site: 1},
    form: '',
    hint: 'algebra: divide both sides by this',
    description: 'divide by {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  // Looks up the statement string, proving it if needed. Returns that
  // result, justified as a "fact".  This is the way to refer to a
  // fact in a proof, displaying it on its own proof line.
  // Currently inline if it is a no-op.
  // Also proves statements of tautologies and simple arithmetic facts.
  // Removes any " = T" from boolean-valued arithmetic facts.
  fact: {
    action: function(statement) {
      if (statement.ruleName) {
        // It is an already proved statement.
        return statement;
      }
      var stmt = getStatement(statement);
      try {
        return getResult(stmt).justify('fact', arguments);
      } catch(err) {
        if (err.isProofError) {
          // Proof failed -- abort.
          throw err;
        }
      }
      // Next try arithmetic facts.
      try {
        var result = rules.axiomArithmetic(stmt);
        if (result.matchSchema('x = T')) {
          result = rules.rewriteWithFact(result, '', '(x = T) = x');
          return result.justify('fact', arguments);
        }
        return result;
      } catch(err) {}
      // Try tautologies.
      try {
        // Inline for tautologies.
        return rules.tautology(statement);
      } catch(err) {}
      throw new Error('No such fact: ' + statement);
    },
    inputs: {term: 1},
    form: ('Look up fact <input name=term>'),
    hint: 'look up a fact',
    comment: (''),
    description: 'fact',
    labels: 'basic'
  },

  //
  // OPTIONAL/UNUSED
  // 

  // Experiment with Andrews' definition of "and".
  funWithAnd: function() {
    var fa = rules.definition('forall');
    var a2 = rules.axiom2();
    var a3 = rules.axiom3();
    var step1 = rules.applyBoth(rules.defAnd(), T);
    var step2a = rules.apply(step1, '/right');
    var step2b = rules.applyBoth(step2a, F);
    var step2c = rules.apply(step2b, '/right');
    var step3 = rules.instEqn(a3, step2c.locate('/right/left'), f);
    var step4 = rules.instEqn(step3, step2c.locate('/right/right'), g);
    var step5 = rules.apply(step4, '/right/arg/body/left');
    var step6 = rules.apply(step5, '/right/arg/body/right');
    var step7 = rules.applyBoth(fa, step6.locate('/right/arg'));
    var step8 = rules.instEqn(a3, step7.locate('/right/left'), f);
    var step9 = rules.instEqn(step8, step7.locate('/right/right'), g);
    var step10 = rules.apply(step9, '/right/arg/body/left');
    var step11 = rules.apply(step10, '/right/arg/body/right');
    var step12 = rules.r5218(step11.locate('/right/arg/body/right'));
    var step13 = rules.r(step12, step11, '/right/arg/body');
    return step13.justify('funWithAnd');
  }

};  // End of ruleInfo.

// Map from rule name to function used in all proofs.
// Generated from ruleInfo by addRules, below.
var rules = {};

// Math markup in the position of a rule name.
// Helper for addRules.
function formulaAsDescription(text) {
  return '<span class=math>[' + Toy.mathMarkup(text) + ']</span>';
}

/**
 * Given a ruleInfo object, add its information to the "rules" object.
 * The "rules" object maps from rule name to function.  Each function
 * has an "info" property containing all the properties present in the
 * ruleInfo object entry for the name.  If not supplied in the rule
 * definition, the info.inputs is defaulted to an empty object here.
 */
function addRules(ruleInfo) {
  for (var key in ruleInfo) {
    addRule(key, ruleInfo[key]);
  }
}

function addRule(key, info) {
  // Give every info "inputs".
  if (!info.inputs) {
    info.inputs = {};
  }
  // If the rule (theorem) has an explicit statement (it should be
  // provably true), coerce it to an Expr if given as a string.
  if (typeof info.statement === 'string') {
    info.statement = Toy.parse(info.statement);
  }
  // Default the description to the marked up formula or the ruleName.
  if (!('description' in info)) {
    if (info.formula) {
      info.description = formulaAsDescription(info.formula.toString());
    } else {
      info.description = key;
    }
  }
  var fn = (typeof info == 'function') ? info : info.action;
  // Associate the action function with the key,
  rules[key] = fn;

  // Preprocess labels.  Split, and if there are no explicit labels,
  // give the rule a label of "basic".
  var labels = info.labels;
  info.labels = {};
  if (typeof labels === 'string') {
    labels.split(/\s+/)
      .forEach(function(label) { info.labels[label] = true; });
  }
  if (fn.length === 0 && key.slice(0, 5) === 'axiom') {
    info.labels.axiom = true;
  }
  if (info.form !== undefined && Toy.isEmpty(info.labels)) {
    // Anything conceivably offerable (with a form), default to
    // "basic" if no other labels.
    info.labels.basic = true;
  }

  // and metadata as the function's "info" property.
  rules[key].info = info;

  // TODO: Add this line, making addTheorem and company internal to
  // this function:
  // Function length of 0 means no positional arguments.
  // if (fn.length === 0) { addTheorem(key); }
}

// Actual rule functions to call from other code.
addRules(ruleInfo);


//// FACTS

// The fact information is organized with the synopsis as
// a map key to take advantage of debug printing of the functions
// in the Chrome debugger.

var logicFacts = {
  // Logic
  '(T = a) = a': {
    action: function() {
      return rules.theorem('tIsXIsX');
    }
  },
  '(a = T) = a': {
    action: function() {
      return rules.theorem('tIsXIsX')
      .rewrite('/left', 'equalitySymmetric');
    }
  }

};

// These are algebra facts.
var algebraFacts = {

  // Axioms

  'a + b = b + a': {
    action: function() {
      return rules.axiom('axiomCommutativePlus');
    }
  },
  'a * b = b * a': {
    action: function() {
      return rules.axiom('axiomCommutativeTimes');
    }
  },
  'a + (b + c) = a + b + c': {
    action: function() {
      return rules.axiom('axiomAssociativePlus');
    }
  },
  'a * (b * c) = a * b * c': {
    action: function() {
      return rules.axiom('axiomAssociativeTimes');
    }
  },
  'a * (b + c) = a * b + a * c': {
    action: function() {
      return rules.axiom('axiomDistributivity');
    }
  },
  'a + 0 = a': {
    action: function() {
      return rules.axiom('axiomPlusZero');
    }
  },
  'a * 1 = a': {
    action: function() {
      return rules.axiom('axiomTimesOne');
    }
  },
  'a * 0 = 0': {
    action: function() {
      return rules.axiom('axiomTimesZero');
    }
  },
  'a + neg a = 0': {
    action: function() {
      return rules.axiom('axiomNeg');
    }
  },
  '@R a & a != 0 ==> a * recip a = 1': {
    action: function() {
      return rules.axiom('axiomReciprocal');
    }
  },
  'a * b != 0 == a != 0 & b != 0': {
    action: function() {
      return rules.factNonzeroProduct();
    }
  },
  'a = b == b = a': {
    action: function() {
      return rules.equalitySymmetric();
    }
  },

  // Addition
  'a + b + c = a + (b + c)': {
    action: function() {
      return rules.eqnSwap(rules.axiom('axiomAssociativePlus'));
    }
  },
  'a + b + c = a + c + b': {
    action: function() {
      var step = rules.consider('a + b + c')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + b = b + a')
      .rewrite('/main/right', 'a + (b + c) = a + b + c');
      return step;
    }
  },
  'a + b + c = a + (c + b)': {
    action: function() {
      return rules.consider('a + b + c')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)');
    }
  },

  // Multiplication
  'a * b * c = a * (b * c)': {
    action: function() {
      var step1 = rules.axiom('axiomAssociativeTimes');
      var step2 = rules.eqnSwap(step1);
      return step2;
    }
  },
  'a * b * c = a * c * b': {
    action: function() {
      var step = rules.consider('a * b * c')
      .rewrite('/main/right', 'a * b * c = a * (b * c)')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b * c) = a * b * c');
      return step;
    }
  },

  // Distributivity
  '(a + b) * c = a * c + b * c': {
    action: function() {
      var step = rules.consider('(a + b) * c')
      .rewrite('/main/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right/left', 'a * b = b * a');
      return step;
    }
  },
  'a * c + b * c = (a + b) * c': {
    action: function() {
      var step = rules.fact('(a + b) * c = a * c + b * c')
      .apply('eqnSwap');
      return step;
    }
  },
  'a * b + a * c = a * (b + c)': {
    action: function() {
      var step1 = rules.axiom('axiomDistributivity');
      var step2 = rules.eqnSwap(step1);
      return step2;
    }
  },
  'a * b + b = (a + 1) * b': {
    action: function() {
      var step = rules.consider('a * b + b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    }
  },
  'b + a * b = (1 + a) * b': {
    action: function() {
      var step = rules.consider('b + a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    }
  },
  'a + a = 2 * a': {
    action: function() {
      return rules.consider('a + a')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * b + b = (a + 1) * b')
      .apply('arithmetic', '/main/right/left');
    }
  },

  // Distributivity with subtraction

  'a * (b - c) = a * b - a * c': {
    action: function() {
      return rules.consider('a * (b - c)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * neg b = neg (a * b)')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  '(a - b) * c = a * c - b * c': {
    action: function() {
      var step = rules.consider('(a - b) * c')
      .rewrite('/main/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b - c) = a * b - a * c')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right/left', 'a * b = b * a');
      return step;
    }
  },
  'a * c - b * c = (a - b) * c': {
    action: function() {
      var step = rules.fact('(a - b) * c = a * c - b * c')
      .apply('eqnSwap');
      return step;
    }
  },
  'a * b - a * c = a * (b - c)': {
    action: function() {
      return rules.fact('a * (b - c) = a * b - a * c')
      .apply('eqnSwap');
    }
  },
  'a * b - b = (a - 1) * b': {
    action: function() {
      return rules.consider('a * b - b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    }
  },
  'b - a * b = (1 - a) * b': {
    action: function() {
      return rules.consider('b - a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    }
  },

  // Plus zero
  'a = a + 0': {
    action: function() {
      var step1 = rules.axiom('axiomPlusZero');
      var step2 = rules.eqnSwap(step1);
      return step2;
    }
  },
  /* Omit from UI: somewhat redundant
     'a = 0 + a': {
     action: function() {
     var step1 = rules.axiom('axiomPlusZero');
     var step2 = rules.eqnSwap(step1);
     var step3 = rules.rewriteWithFact(step2, '/main/right',
     'a + b = b + a');
     return step3;
     }
     },
  */
  '0 + a = a': {
    action: function() {
      var step1 = rules.axiom('axiomPlusZero');
      var step2 = rules.rewriteWithFact(step1, '/main/left',
                                        'a + b = b + a');
      return step2;
    }
  },
  // Times one
  'a = a * 1': {
    action: function() {
      var step1 = rules.axiom('axiomTimesOne');
      var step2 = rules.eqnSwap(step1);
      return step2;
    }
  },
  'a = 1 * a': {
    action: function() {
      var step1 = rules.axiom('axiomTimesOne');
      var step2 = rules.eqnSwap(step1);
      var step3 = rules.rewriteWithFact(step2, '/main/right',
                                        'a * b = b * a');
      return step3;
    }
  },
  '1 * a = a': {
    action: function() {
      var step1 = rules.axiom('axiomTimesOne');
      var step2 = rules.rewriteWithFact(step1, '/main/left',
                                        'a * b = b * a');
      return step2;
    }
  },

  // Zero times
  '0 * a = 0': {
    action: function() {
      return rules.axiom('axiomTimesZero')
      .rewrite('/main/left', 'a * b = b * a');
    }
  },

  // Negation rules
  'a - b = a + neg b': {
    action: function() {
      var step1 = rules.consider('a - b');
      var step2 = rules.apply(step1, '/main/right');
      return step2;
    }
  },
  'a + neg b = a - b': {
    action: function() {
      return rules.eqnSwap(rules.fact('a - b = a + neg b'));
    }
  },
  'neg a + a = 0': {
    action: function() {
      return rules.axiom('axiomNeg')
      .rewrite('/main/left', 'a + b = b + a');
    }
  },
  'neg (neg a) = a': {
    action: function() {
      return rules.fact('neg a + a = 0')
      .apply('instVar', 'neg a', 'a')
      .apply('addToBoth', Toy.parse('a'))
      .rewrite('/main/left', 'a + b + c = a + (b + c)')
      .rewrite('/main/left/right', 'neg a + a = 0')
      .rewrite('/main/left', 'a + 0 = a')
      .rewrite('/main/right', '0 + a = a');
    }
  },
  'a + neg b + b = a': {
    action: function() {
      return rules.consider('a + neg b + b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'neg a + a = 0')
      .rewrite('/main/right', 'a + 0 = a');
    }
  },
  'a + b + neg b = a': {
    action: function() {
      return rules.consider('a + b + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg a = 0')
      .rewrite('/main/right', 'a + 0 = a');
    }
  },

  // Negation with multiplication
  'neg a = -1 * a': {
    action: function() {
      // 0 = -1 * a + a
      var minusOne = rules.fact('0 * a = 0')
      .replace('/main/left/left',
               rules.axiomArithmetic(Toy.parse('-1 + 1'))
               .apply('eqnSwap'))
      .rewrite('/main/left', '(a + b) * c = a * c + b * c')
      .apply('_simplifyMath1', '/main/left')
      .apply('eqnSwap');
      return rules.fact('neg a + a = 0')
      .replace('/main/right', minusOne)
      .apply('subtractFromBoth', 'a')
      .rewrite('/main/right', 'a + b - c = a + (b - c)')
      .rewrite('/main/right/right', 'a - a = 0')
      .rewrite('/main/right', 'a + 0 = a')
      .rewrite('/main/left', 'a + b - c = a + (b - c)')
      .rewrite('/main/left/right', 'a - a = 0')
      .rewrite('/main/left', 'a + 0 = a');
    }
  },
  '-1 * a = neg a': {
    action: function() {
      return rules.fact('neg a = -1 * a')
      .apply('eqnSwap');
    }
  },
  'neg (a * b) = neg a * b': {
    action: function() {
      return rules.consider('neg (a * b)')
      .rewrite('/main/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * (b * c) = (a * b) * c')
      .rewrite('/main/right/left', '-1 * a = neg a');
    }
  },
  'a * neg b = neg (a * b)': {
    action: function() {
      return rules.consider('a * neg b')
      .rewrite('/main/right/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right/left', 'a * b = b * a')
      .rewrite('/main/right', 'a * b * c = a * (b * c)')
      .rewrite('/main/right', '-1 * a = neg a');
    }
  },
  'neg (a * b) = a * neg b': {
    action: function() {
      return rules.fact('a * neg b = neg (a * b)')
      .apply('eqnSwap');
    }
  },
  'neg (a + b) = neg a + neg b': {
    action: function() {
      var step1 = rules.fact('a + neg a = 0');
      var step2 = rules.instVar(step1, Toy.parse('a + b'), 'a');
      var step3 = rules.rewriteWithFact(step2, '/right/left',
                                        'a + b + c = a + c + b');
      var step4 = rules.addToBoth(step3, Toy.parse('neg b'));
      var step5 = rules.rewriteWithFact(step4, '/right/left',
                                        'a + b + c = a + (b + c)');
      var step6 = rules.rewriteWithFact(step5, '/right/left/right',
                                        'a + neg a = 0');
      var step7 = rules.rewriteWithFact(step6, '/right/right',
                                        '0 + a = a');
      var step8 = rules.rewriteWithFact(step7, '/right/left',
                                        'a + 0 = a');
      var step9 = rules.addToBoth(step8, Toy.parse('neg a'));
      var step10 = rules.rewriteWithFact(step9, '/right/left/left',
                                         'a + b = b + a');
      var step11 = rules.rewriteWithFact(step10, '/right/left',
                                         'a + b + c = a + (b + c)');
      var step12 = rules.rewriteWithFact(step11, '/right/left/right',
                                         'a + neg a = 0');
      var step13 = rules.rewriteWithFact(step12, '/right/left',
                                         'a + 0 = a');
      var step14 = rules.rewriteWithFact(step13, '/right/right',
                                         'a + b = b + a');
      return step14;
    }
  },
  'neg (a - b) = b - a': {
    action: function() {
      return rules.consider('neg (a - b)')
      .rewrite('/main/right/arg', 'a - b = a + neg b')
      .rewrite('/main/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right', 'neg (neg a) = a')
      .rewrite('/main/right', 'a + b = b + a')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  'neg (a - b) = neg a + b': {
    action: function() {
      return rules.consider('neg (a - b)')
      .rewrite('/main/right/arg', 'a - b = a + neg b')
      .rewrite('/main/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right', 'neg (neg a) = a');
    }
  },


  // Subtraction facts

  // Moving terms to the left
  'a + b - c = a - c + b': {
    action: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right/left', 'a + neg b = a - b');
    }
  },
  'a - b + c = a + c - b': {
    action: function() {
      return rules.consider('a - b + c')
      .rewrite('/main/right/left', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  'a - b + c = a + (c - b)': {
    action: function() {
      return rules.fact('a - b + c = a + c - b')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg b = a - b');
    }
  },
  'a - (b - c) = a + (c - b)': {
    action: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right/right', 'neg (a - b) = b - a');
    }
  },
  'a - (b - c) = a + c - b': {
    action: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right', 'a - (b - c) = a + (c - b)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },

  // Four cases: each operation can be + or -, and initial association
  // can be to the left or right.
  'a + b - c = a + (b - c)': {
    action: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg b = a - b');
    }
  },
  'a - (b + c) = a - b - c': {
    action: function() {
      var step = rules.consider('a - (b + c)')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right/right',
               'neg (a + b) = neg a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', 'a + neg b = a - b')
      .rewrite('/main/right/left', 'a + neg b = a - b');
      return step;
    }
  },  
  'a - b - c = a - c - b': {
    action: function() {
      return rules.consider('a - b - c')
      .rewrite('/main/right/left', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b - c = a - c + b')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  'a + (b - c) = a + b - c': {
    action: function() {
      var step = rules.consider('a + (b - c)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', 'a + neg b = a - b');
      return step;
    }
  },
  'a - (b - c) = a - b + c': {
    action: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right/right', 'neg (neg a) = a')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right/left', 'a + neg b = a - b');
    }
  },
  'a - b + c = a - (b - c)': {
    action: function() {
      return rules.fact('a - (b - c) = a - b + c')
      .apply('eqnSwap');
    }
  },

  // Simplification
  'a - a = 0': {
    action: function() {
      return (rules.eqSelf('a - a')
              .apply('apply', '/right')
              .rewrite('/main/right', 'a + neg a = 0'));
    }
  },

  'a + b - b = a': {
    action: function() {
      return (rules.consider('a + b - b')
              .rewrite('/main/right', 'a + b - c = a + (b - c)')
              .rewrite('/main/right/right', 'a - a = 0')
              .rewrite('/main/right', 'a + 0 = a'));
    }
  },

  'a - b + b = a': {
    action: function() {
      return (rules.consider('a - b + b')
              .rewrite('/main/right', 'a - b + c = a + c - b')
              .rewrite('/main/right', 'a + b - b = a'));
    }
  },

  // Reciprocal rules

  'a != 0 ==> recip a * a = 1': {
    action: function() {
      return rules.axiom('axiomReciprocal')
      .rewrite('/main/left', 'a * b = b * a');
    }
  },
  'a != 0 ==> recip a != 0': {
    action: function() {
      var step1 = rules.axiom('axiomReciprocal');
      var step2 = rules.fact('1 != 0');
      var step3 = rules.rRight(step1, step2, '/left')
      .rewrite('/main', 'a * b != 0 == a != 0 & b != 0');
      var step4 = rules.tautology('a & b ==> b');
      var step5 = rules.forwardChain(step3, step4);
      return step5;
    }
  },
  'a / b = a * recip b': {
    action: function() {
      var step1 = rules.consider('a / b');
      var step2 = rules.apply(step1, '/main/right');
      return step2;
    }
  },
  'a * recip b = a / b': {
    action: function() {
      return rules.eqnSwap(rules.fact('a / b = a * recip b'));
    }
  },
  'a != 0 ==> recip a = 1 / a': {
    action: function() {
      return rules.consider('recip s')
      .rewrite('/main/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * recip b = a / b');
    }
  },
  'a != 0 ==> recip (recip a) = a': {
    action: function() {
      var step1 = rules.fact('a * recip a = 1');
      var step2 = rules.multiplyBoth(step1, Toy.parse('recip (recip a)'));
      var step3 = rules.rewriteWithFact(step2, '/main/right',
                                        '1 * a = a');
      var step4 = rules.rewriteWithFact(step3, '/main/left',
                                        'a * b * c = a * (b * c)');
      var step5 = rules.instVar(step1, Toy.parse('recip a'), 'a');
      var step6 = rules.replace(step5, step4, '/main/left/right');
      var step7 = rules.rewriteWithFact(step6, '/main/left',
                                        'a * 1 = a');
      var step8 = rules.eqnSwap(step7);
      return step8;
    }
  },
  '@R (recip a) & recip a != 0 ==> R a & a != 0': {
    action: function() {
      var taut = rules.tautology('(a == b) ==> (a ==> b)');
      var fact = rules.axiom('axiomReciprocal2');
      return rules.forwardChain(fact, taut);
    }
  },
  '@R a & a != 0 ==> R (recip a) & recip a != 0': {
    action: function() {
      var taut = rules.tautology('(a == b) ==> (b ==> a)');
      var fact = rules.axiom('axiomReciprocal2');
      return rules.forwardChain(fact, taut);
    }
  },
  /* Proved above from axiomReciprocal.
  '@R a & a != 0 ==> recip a != 0': {
    action: function() {
    var taut = rules.tautology('(a ==> b & c) ==> (a ==> c)');
    var fact = rules.fact('@R a & a != 0 ==> R (recip a) & recip a != 0');
    return rules.forwardChain(fact, taut);
    }
  },
  */

  'a != 0 & b != 0 ==> recip (a * b) = recip a * recip b': {
    action: function() {
      var step1 = rules.fact('a * recip a = 1');
      var step2 = rules.instVar(step1, Toy.parse('a * b'), 'a');
      var step3 = rules.rewriteWithFact(step2, '/right/left',
                                        'a * b * c = a * c * b');
      var step4 = rules.multiplyBoth(step3, Toy.parse('recip b'));
      var step5 = rules.rewriteWithFact(step4, '/right/left',
                                        'a * b * c = a * (b * c)');
      var step6 = rules.rewriteWithFact(step5, '/right/left/right',
                                        'a * recip a = 1');
      var step7 = rules.rewriteWithFact(step6, '/right/right',
                                        '1 * a = a');
      var step8 = rules.rewriteWithFact(step7, '/right/left',
                                        'a * 1 = a');
      var step9 = rules.multiplyBoth(step8, Toy.parse('recip a'));
      var step10 = rules.rewriteWithFact(step9, '/right/left/left',
                                         'a * b = b * a');
      var step11 = rules.rewriteWithFact(step10, '/right/left',
                                         'a * b * c = a * (b * c)');
      var step12 = rules.rewriteWithFact(step11, '/right/left/right',
                                         'a * recip a = 1');
      var step13 = rules.rewriteWithFact(step12, '/right/left',
                                         'a * 1 = a');
      var step14 = rules.rewriteWithFact(step13, '/right/right',
                                         'a * b = b * a');
      return step14;
    }
  },

  // Division rules

  'c != 0 ==> a * b / c = a / c * b': {
    action: function() {
      var step = rules.consider('a * b / c')
      .rewrite('/main/right', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * b * c = a * c * b')
      .rewrite('/main/right/left', 'a * recip b = a / b');
      return step;
    }
  },
  'b != 0 ==> a / b * c = a * c / b': {
    action: function() {
      var step = rules.consider('a / b * c')
      .rewrite('/main/right/left', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * b * c = a * c * b')
      .rewrite('/main/right', 'a * recip b = a / b');
      return step;
    }
  },
  'b != 0 & c != 0 ==> a / (b * c) = a / b / c': {
    action: function() {
      var step = rules.consider('a / (b * c)')
      .rewrite('/main/right', 'a / b = a * recip b')
      .rewrite('/main/right/right',
               'recip (a * b) = recip a * recip b')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right', 'a * recip b = a / b')
      .rewrite('/main/right/left', 'a * recip b = a / b');
      return step;
    }
  },  
  'c != 0 ==> a * (b / c) = a * b / c': {
    action: function() {
      var step = rules.consider('a * (b / c)')
      .rewrite('/main/right/right', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right', 'a * recip b = a / b');
      return step;
    }
  },

  // Somewhat useful fact to stick at the end of the list.
  'not F': {
    action: function() {
      return rules.tautology('not F');
    }
  },

  // MOVING EXPRESSIONS AROUND

  'a = neg b == a + b = 0': {
    action: function() {
      var step = rules.assume('a = neg b')
      .apply('addToBoth', 'b')
      .rewrite('/main/right', 'neg a + a = 0')
      .apply('isolateHyp', 'a = neg b');
      var converse = rules.assume('a + b = 0')
      .apply('addToBoth', 'neg b')
      .rewrite('/main/right', '0 + a = a')
      .rewrite('/main/left', 'a + b + c = a + (b + c)')
      .rewrite('/main/left/right', 'a + neg a = 0')
      .rewrite('/main/left', 'a + 0 = a')
      .apply('isolateHyp', 'a + b = 0');
      var conj = rules.makeConjunction(step, converse);
      var taut = rules.tautology('(a ==> b) & (b ==> a) == (a == b)');
      return rules.rewrite(conj, '/main', taut);

    }
  },
  'a = b == a - b = 0': {
    action: function() {
      return rules.fact('a = neg b == a + b = 0')
      .apply('instVar', 'neg b', 'b')
      .rewrite('/main/left/right', 'neg (neg a) = a')
      .rewrite('/main/right/left', 'a + neg b = a - b');
    }
  }
};

/**
 * Treat each key/value pair in the map as an expression and
 * a function to prove it.  Add each as a "fact".
 */
function addFactsMap(map) {
  for (synopsis in map) {
    addFact(synopsis, map[synopsis].action);
  }
}

// Put definitions into their database:
Toy.define('not', equal(F));
Toy.define('!=', '{x. {y. not (x = y)}}');
Toy.define('forall', equal(lambda(x, T)));
Toy.define('exists', '(!=) {x. F}');
Toy.defineCases('&', identity, lambda(x, F));
Toy.defineCases('|', allT, identity);
Toy.defineCases('==>', identity, allT);

Toy.define('-', '{x. {y. x + neg y}}');
Toy.define('/', '{x. {y. x * recip y}}');

//// THEOREMS

function Fact(goal, prover) {
  if (goal.ruleName) {
    // It is already proved.
    assert(!prover, function() { return 'Redundant prover for ' + expr_arg; });
    prover = function() { return goal; }
    result = goal;
  }
  assert(typeof prover === 'function', 'Not a function: ' + prover);
  this.goal = goal;
  this._prover = Toy.memo(prover);
}

$.extend(Fact.prototype, {

    // Get the proved result of the fact.
    result: function() {
      if (Toy.assertFacts && !this._prover.done) {
        return rules.assert(this.goal);
      }
      try {
        // _prover is memoized, so only really runs once.
        var result = this._prover();
      } catch(err) {
        // Flag it as an error in proof execution.
        err.isProofError = true;
        throw err;
      }

      // If there is a substitution into the result that yields
      // the goal, do it.
      var goal = this.goal;
      var subst = result.alphaMatch(goal);
      if (!subst) {
        var subst2 = result.getMain().alphaMatch(goal.getMain());
        assert(!subst2, function() {
            return 'Assumptions do not match goal ' + goal;
          }, result);
      }
      assert(subst, function() {
          return 'Failed to prove ' + goal;
        }, result);
      var result2 = rules.instMultiVars(result, subst);
      return result2;
    }
  });
      

// Private to addFact, getResult, and eachFact.  Maps from a string
// "dump" of a fact to either the proved fact, or to a function to
// prove it.
var _factsMap = {};

/**
 * Adds to the facts database a formula and optionally a function to
 * prove it on demand.  The formula may be given as an object
 * acceptable to getStatement, normally a string or Expr.
 * If the given formula is not the result of a proof, the prover
 * argument is required.  Treats any input that is an implication
 * as a statement with assumptions.
 *
 * TODO: Add the converse when adding a fact, provided the fact
 *   is not its own converse (or perhaps the converse already added).
 */
function addFact(expr_arg, prover) {
  var goal = getStatement(expr_arg);
  var fact = new Fact(goal, prover);
  _factsMap[goal.getMain().dump()] = fact;
  return fact;
}

/**
 * Accepts any argument acceptable to getStatement.  Looks up a fact
 * matching that statement, returning the proved result.
 * Automatically does alpha conversion if necessary to use the desired
 * variable names.  Throws an exception in case of failure.
 *
 * Checks that the "main" part of the result matches the "main" part
 * of the statement of the fact.
 */
function getResult(stmt) {
  var goal = getStatement(stmt);
  if (goal.ruleName) {
    // Proved!
    return goal;
  }
  // Same encoding as in addFact.
  var fact = _factsMap[goal.getMain().dump()];
  assert(fact, function() { return 'No such fact: ' + goal; });
  return fact.result();
}

/**
 * Returns a formula that is the statement of a "fact".  The fact can
 * be a theorem name, a fact object, an Expr or a parseable string.
 * Given a theorem name or fact object, accesses any known statement
 * of it, or proves it if there is no statement.  Parses a string, and
 * if the result is an implication with an equation as the
 * consequence, treats the antecedent as assumptions.  Automatically
 * adds assumptions that inputs to math operators are real numbers.
 *
 * Returns an Expr.  If the fact is given as a string, note that the
 * result is the result of Toy.mathParse applied to it, with any
 * antecedent flagged as hypotheses.
 */
function getStatement(fact) {
  if (typeof fact === 'string') {
    if (Toy.isIdentifier(fact)) {
      // It's the name of an axiom or theorem.
      var statement = rules[fact].info.statement;
      if (statement) {
        // Work with an asserted statement of the theorem if there
        // is one.
        return statement;
      }
      if (!alreadyProved(fact)) {
        console.log('Proving in getStatement: ' + fact);
      }
      return isAxiom(fact) ? rules.axiom(fact) : rules.theorem(fact);
    } else {
      // Otherwise it should be a expression in string form.
      var result = Toy.mathParse(fact);
      if (result.isCall2('==>') && result.getRight().isCall2('=')) {
        // Flag it as having assumptions, though the result is not a
        // theorem.
        result.hasHyps = true;
      }
      return result;
    }
  } else if (fact instanceof Expr) {
    return fact;
  } else if (fact instanceof Fact) {
    return fact.goal;
  } else {
    throw new Error('Bad input to getStatement');
  }
}

/**
 * Finds a single LHS match within the given term with one of the
 * given facts.  Returns the value of the successful call to
 * findMatchingFact, or undefined if no call succeeded.
 *
 * All arguments other than the term are passed via "info".  If it is
 * a plain object, it interprets the following properties:
 *
 * facts: List of facts in the format accepted by findMatchingFact.
 * context: Context information for "where" clauses as
 *   accepted by findMatchingFact.
 * searchMethod: Name of method to apply to the term to control
 *   which subexpressions of the term to apply findMatchingFact to.
 */
function findMatchingCall(term, info) {
  var facts, cxt, searchMethod;
  if (info.constructor === Object) {
    facts = info.facts;
    cxt = info.context;
    searchMethod = info.searchMethod;
  } else {
    facts = info;
  }
  searchMethod = searchMethod || 'searchCalls';
  return term[searchMethod](findMatchingFact.bind(null, facts, cxt));
}

/**
 * Searches the given facts list for one that matches the given term.
 * If it finds one, returns info about it in the format returned by
 * findMatchingCall.  The path argument should be a reverse path to
 * the term relative to the proof step where the term appears.
 *
 * Each fact is either something acceptable as an argument to
 * getStatement, or a plain object with properties as follows:
 *
 * stmt: value acceptable to getStatement.
 * where: string to evaluate, with "subst" and the "cxt" argument to
 *   findMatchingFact available for use in the string.
 * match: term to match against parts of the step; by default the
 *   equation LHS.
 *
 * The value returned is undefined or else a plain object with
 * properties:
 * 
 * stmt: statement of the matching fact (undefined if not matching a
 *   fact).
 * term: term passed to findMatchingFact.
 * path: forward version of the path argument.
 * subst: substitution that makes the given term match the fact.
 *
 */
function findMatchingFact(facts, cxt, term, pth) {
  function doEval(str, subst) {
    // Suppress acccess to the enclosing "facts" and "pth" variables.
    // OK for str to refer to "cxt" or "term".
    var facts, pth;
    return eval(str);
  }
  for (var i = 0; i < facts.length; i++) {
    var factInfo = facts[i];
    var infoIsObject = factInfo.constructor == Object;
    var stmt = infoIsObject ? factInfo.stmt : factInfo;
    var where = infoIsObject ? factInfo.where : null;
    var schema = (infoIsObject && factInfo.match
                  ? Toy.termify(factInfo.match)
                  : Toy.getStatement(stmt).getMain().getLeft());
    var subst = term.matchSchema(schema);
    if (subst && (!where || doEval(where, subst))) {
      return {stmt: stmt,
              term: term,
              path: pth.reverse(),
              subst: subst};
    }
  }
  // If no match found the value will be falsy.
};

/**
 * Apply the list of fact rewrites to the visible part of the step
 * until none of them any longer is applicable, returning the result.
 */
function applyToVisible(step, facts) {
  return applyFactsAtPath(step, facts, step.pathToVisiblePart());
}

/**
 * Apply the list of facts as rewrites to the given part of the step
 * until none of them any longer is applicable, returning the result.
 * Returns its input step if no matches are found.
 */
function applyFactsAtPath(step, facts, path_arg) {
  var path = Toy.path(path_arg);
  var eqn1 = rules.considerPart(step, path);
  var eqn2 = applyFactsToRhs(eqn1, facts);
  return (eqn2 == eqn1 ? step : rules.replace(eqn2, step, path));
}

/**
 * Apply the list of facts as rewrites to the RHS of the given step,
 * which must be an equation.  Repeats until none of them is
 * applicable, returning the result.  Returns its input step if no
 * matches are found.
 */
function applyFactsToRhs(step, facts) {
  var rhs = Toy.path('/main/right');
  var info;
  var eqn = step;
  while (info = findMatchingCall(eqn.locate(rhs), facts)) {
    var fullPath = rhs.concat(info.path);
    eqn = rules.rewriteWithFact(eqn, fullPath, info.stmt);
  }
  return eqn;
}

/**
 * Apply the function to the subexpression of step at path.
 * The result must be an equation that equates the original
 * subexpression to something else.  This replaces the
 * subexpression using the equation.
 */ 
function convertAndReplace(step, path, fn) {
  var eqn1 = rules.considerPart(step, path);
  var eqn2 = fn(eqn1);
  return rules.replace(eqn2, step, path);
}

/**
 * Call the given function for each of the registered facts, passing
 * it the fact, a function that can return some proved fact with a
 * "goal" property, an Expr stating the result.
 */
function eachFact(fn) {
  for (var key in _factsMap) {
    fn(_factsMap[key]);
  }
}

// Private to addTheorem, getTheorem, and the initializations
// at the bottom of this file.  Maps from name to an inference
// containing a proof of the theorem, or true, indicating
// that the the theorem's proof procedure has not run.
var _theoremsByName = {};

/**
 * Checks that the theorem is not already in the database, then adds a
 * function to prove it to the set of theorems, which are indexed by
 * theorem name.
 */
function addTheorem(name) {
  assert(!_theoremsByName[name], 'Theorem already exists: ' + name);
  assert(rules[name], 'No proof: ' + name);
  _theoremsByName[name] = true;
}

/**
 * Gets an existing theorem from the theorems database, or returns
 * null if there is none.  Runs the proof if it has not already run.
 */
function getTheorem(name) {
  var result = _theoremsByName[name];
  if (result == true) {
    result = _theoremsByName[name] = rules[name]();
    /* TODO: find a way to use this code here.  See explanation
       in the "axiom" rule.
    if (axiomNames.indexOf(name) >= 0) {
      result = thm.justify(name);
      // If there are details, the displayer will enable display of them,
      // but there is really no proof of the axiom.
      delete result.details;
    }
    */
  }
  return result;
}

/**
 * Returns true iff the named theorem has already been proved.
 */
function alreadyProved(name) {
  assert(_theoremsByName[name],
         function() { return 'Not a theorem: ' + name; });
  if (isAxiom(name)) {
    return true;
  } else {
    return _theoremsByName[name] instanceof Expr;
  }
}

/**
 * True iff the name is the name of an axiom.
 */
function isAxiom(name) {
  return name.substring(0, 5) === 'axiom';
}

// Add the axioms and theorems to the "database".  This can only
// include ones that are not "axiom schemas", i.e. not parameterized.
// Most of these axioms really have type parameters.  Ideally axiom
// and theorem schemas will be able to stay, but the details remain
// to be determined.
//
// TODO: Determine axioms and theorems as rules with no parameters;
//   treat them all as facts; remove these hand-generated lists.

var axiomNames = ['axiom1', 'axiom2', 'axiom3', 'axiom5', 'axiomPNeqNotP',
                  'axiomCommutativePlus', 'axiomAssociativePlus',
                  'axiomCommutativeTimes', 'axiomAssociativeTimes',
                  'axiomDistributivity', 'axiomPlusZero', 'axiomTimesOne',
                  'axiomTimesZero', 'axiomNeg', 'axiomReciprocal',
                  'axiomReciprocal2',
                  'axiomPlusType', 'axiomTimesType',
                  'axiomNegType', 'axiomReciprocalType'];

var theoremNames =
  (axiomNames.concat(['defFFromBook', 'r5217Book', 'r5225',
                      'defAnd', 'tIsXIsX', 'forallXT', 'xAlwaysX',
                      'r5211', 't', 'r5212', 'r5230TF', 'r5230FT',
                      'r5231T', 'r5231F', 'falseEquals', 'trueEquals',
                      'subtractionType', 'divisionType', 'eqIsEquiv',
                      'equalitySymmetric', 'equalityTransitive',
                      'factNonzeroProduct']));


//// UTILITY FUNCTIONS

/**
 * Build a schema for a conjunction of hypotheses, ensuring all are in
 * the TermMap, with optional exclusions, a TermSet.  The schema is of
 * the form a1 && ... && an, where the "a"s are variables for the
 * terms for each hyp in hyps.
 */
function buildHypSchema(hyps, map, exclusions) {
  var schema = null;
  hyps.eachHyp(function(hyp) {
      var v = map.addTerm(hyp);
      if (!exclusions || !exclusions.has(hyp)) {
        schema = schema ? Toy.infixCall(schema, '&', v) : v;
      }
    });
  return schema;
}

/**
 * Returns the given conjunction of hypotheses except any appearing in
 * the exclusions TermSet.  If there are no such hypotheses, returns
 * T.
 */
function hypsExcept(hyps, exclusions) {
  var result = null;
  hyps.eachHyp(function(hyp) {
      if (!exclusions.has(hyp)) {
        result = result ? Toy.infixCall(result, '&', hyp) : hyp;
      }
    });
  return result;
}

/**
 * Find a term identical to the given one among the hypotheses
 * created by the "assume" rule, or return null if none found.
 * TODO: Consider whether to keep this experimental functionality.
 */
function findHyp(term) {
  return _allHyps[term.dump()];
}

//// Export public names.

Toy.rules = rules;
Toy.logicFacts = logicFacts;
Toy.algebraFacts = algebraFacts;
Toy._factsMap = _factsMap;

// Settable variables, export right here:
Toy.autoAssert = false;
Toy.assertFacts = false;

Toy.axiomNames = axiomNames;
Toy.theoremNames = theoremNames;
Toy.addRule = addRule;
Toy.addFact = addFact;
Toy.getResult = getResult;
Toy.eachFact = eachFact;
Toy.addTheorem = addTheorem;
Toy.getTheorem = getTheorem;
Toy.findHyp = findHyp;
Toy.getStatement = getStatement;
Toy.convertAndReplace = convertAndReplace;

// For testing.
Toy.ruleInfo = ruleInfo;
Toy._tautologies = _tautologies;
Toy._buildHypSchema = buildHypSchema;
Toy._alreadyProved = alreadyProved;
Toy._findMatchingCall = findMatchingCall;
Toy._findMatchingFact = findMatchingFact;

//// INITIALIZATION CODE

// Add all the named theorems to their database.
for (var i = 0; i < theoremNames.length; i++) {
  addTheorem(theoremNames[i]);
}

addFactsMap(logicFacts);
addFactsMap(algebraFacts);

})();
