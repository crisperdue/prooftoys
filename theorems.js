// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('theorems', function(Y) {

// Math markup in the position of a rule name.
// For local use only.
function mathMarkup(text) {
  return '<span class=math>[' + Toy.mathMarkup(text) + ']</span>';
}


//// THEOREMS AND RULES

// Use the application's "assert" rather than YUI's.
var assert = Toy.assertTrue;

// And make other useful names available here.
var assertEqn = Toy.assertEqn;
var varify = Toy.varify;
var call = Toy.call;
var equal = Toy.equal;
var implies = Toy.implies;
var lambda = Toy.lambda;

// Include all variables that appear in axioms, plus T and F.
var T = varify('T');
var F = varify('F');
var f = varify('f');
var g = varify('g');
var h = varify('h');
var x = varify('x');
var y = varify('y');

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
// description: HTML word or phrase to display for the rule name.
// isRewriter: true to highlight on hover like a rewrite rule.
//   TODO: Consider removing this as unnecessary.
// template: if present, normally the equation used for the
//   rule, as for rewriters.  The equation may have conditions.
//   When working forward the left side of the main equation must
//   match the site to be operated on.
// templateSide: may be 'right' to indicate that the rule uses
//   the converse equality (rewrites matching the right side of the
//   equation rather than the left side).
//

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
    hint: 'Assert as universally true',
    description: 'assert',
    comment: 'WFF to assert (possibly to prove later)'
  },

  define: {
    action: function(name, definition) {
      return Toy.define(name, definition).justify('define', arguments);
    },
    inputs: {varName: 1, term: 2},
    form: ('Define name <input name=varName> as <input name=term>'),
    description: 'define {var}',
    comment: 'Simple definition'
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
      var result = step.justify('assume', arguments);
      result.hasHyps = true;
      assumption.sourceStep = result;
      _allHyps[assumption.dump()] = assumption;
      return result;
    },
    inputs: {term: 1},
    form: ('Assume <input name=term>'),
    hint: 'assume hypothetically',
    comment: 'Hypothesis to assume',
    description: 'assumption'
  },

  /**
   * Converts a wff with hypotheses to an implication.  If there are
   * no hypotheses, returns its input unchanged.
   */
  asImplication: {
    action: function(step) {
      var result = step.justify('asImplication', arguments, [step]);
      result.hasHyps = false;
      return result;
    },
    inputs: {step: 1},
    form: ('Convert hypotheses to explicit implication in step '
           + '<input name=step>'),
    comment: 'Convert assumptions to an explicit implication',
    description: 'display assumptions {step in step}'
  },
      
  /**
   * A no-op step that breaks the cycle of displaying with elision.
   */
  display: {
    action: function(step) {
      return step.justify('display', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Does nothing, but result will display in full. '
           + '<input name=step>'),
    comment: 'No-op, but result will be fully displayed',
    description: 'step details {step of step}'
  },
      
  /**
   * From an implication with LHS consisting of a set of hypotheses,
   * derives the equivalent step with the hypotheses.
   */
  asHypotheses: {
    action: function(step) {
      step.assertCall2('==>');
      var result = step.justify('asHypotheses', arguments, [step]);
      result.hasHyps = true;
      return result;
    },
    inputs: {implication: 1},
    form: ('Convert implication to hypotheses in step '
           + '<input name=implication>'),
    hint: 'Convert explicit implication to statement with assumptions',
    description: 'abbreviate assumptions {implication in step}'
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
    comment: 'access a definition',
    description: '=definition'
  },

  /**
   * Refer to an axiom in the theorems database.  Affects the
   * display of the proof step, but otherwise the same as "theorem".
   */
  axiom: function(name) {
    // This rule is inline.  The axioms themselves, like theorems,
    // have justifications.
    // For inline rules we still want to use an ordinal
    // consistent with their order of execution in the proof, so
    // this creates another step by calling "justify".
    // TODO: De-hackify this.
    assert(name.substring(0, 5) == 'axiom', 'Not an axiom: ' + name);
    var thm = Toy.getTheorem(name);
    assert(thm, 'No axiom ' + name);
    var result = thm.justify(name);
    // If there are details, the displayer will enable display of them,
    // but there is really no proof of the axiom.
    delete result.details;
    return result;
  },

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R.  The subexpression must match
   * the equation's LHS, meaning it they are the same except possibly
   * in names of variables bound in each.
   */
  r: {
    action: function(equation, target, path) {
      path = Toy.path(path);
      assert(equation.isCall2('='), function() {
	return 'Rule R requires equation: ' + equation;
      }, equation);
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
      var result = target.replace(path, replacer);
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
      return justified;
    },
    inputs: {equation: 1, site: 2},
    // Currently not offered in forms; use "replace".
    // form: ('Replace selection with right side of step <input name=equation>'),
    comment: ('Replace an occurrence of a term with an equal term.'),
    hint: 'Replace term with equal term',
    description: 'replace {site};; {siteStep in step} {equation using step}'
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
    hint: 'replace term with equal term',
    comment: ('Replaces an occurrence of a term with an equal term,'
              + ' replacing right side with left side.'),
    description: 'replace {site};; {siteStep in step} {equation using step}'
  },

  axiom1: {
    action: function() {
      var result = rules.assert('g T & g F == forall {x. g x}');
      return result.justify('axiom1');
    },
    inputs: {},
    form: '',
    description: 'T and F are all the booleans',
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
    comment: ('equal inputs yield equal outputs.')
  },

  axiom3: {
    action: function() {
      var result = rules.assert('(f = g) = forall {x. f x = g x}');
      return result.justify('axiom3');
    },
    inputs: {},
    form: '',
    hint: 'extensionality',
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
      var lambdaExpr = call.fn;
      var result =
        equal(call, Toy.subFree(call.arg, lambdaExpr.bound, lambdaExpr.body));
      // Always make sure the call has a type.  It came from elsewhere.
      Toy.findType(call);
      var result = rules.assert(result).justify('axiom4', [call]);
      // There are no real details in this case.
      delete result.details;
      return result;
    },
    inputs: {term: 1},  // Specifically a Call to a Lambda.
    form: 'Enter {v. body} expr <input name=term>',
    hint: 'apply a function to its argument',
    description: 'axiom of substitution',
    comment: ('')
  },

  axiom5: {
    action: function() {
      var result = rules.assert('(the (= y)) = y');
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
    hint: '(forall {p. not (p = not p)})',
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
      var step1 = rules.axiom4(call(lambda(x, x), a));
      var result = rules.r(step1, step1, '/left');
      return result.justify('eqSelf', arguments);
    },
    inputs: {term: 1},
    form: 'Term to prove equal to itself: <input name=term>',
    hint: '(A = A)',
    comment: 'Derives A = A.',
    description: mathMarkup('a = a')
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
    comment: '\u21d4 and = are the same'
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
    hint: 'From A = B to B = A',
    comment: 'from A = B deduce B = A',
    description: 'from a = b to b = a'
  },

  // r5201c.  Works with hypotheses.
  eqnChain: {
    action: function(ab, bc) {
      var ac = rules.replace(bc, ab, '/main/right');
      var result = ac;
      return result.justify('eqnChain', arguments, arguments);
    },
    description: 'from a = b and b = c to a = c',
    comment: 'from A = B and B = C deduce A = C'
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
    hint: 'From F = G to (F A) = (G A)',
    comment: 'given f = g, deduce (f A) = (g A)',
    description: 'from f = g to (f a) = (g a)'
  },

  // r5201f.  Works with hypotheses.
  applyToBoth: {
    action: function(a, h_bc) {
      var bc = h_bc.unHyp();
      var abab = rules.eqSelf(call(a, bc.getLeft()));
      var abac = rules.replace(h_bc, abab, '/right/arg');
      var result = abac;
      if (a instanceof Toy.Lambda) {
        var step2 = rules.apply(abac, '/main/left');
        var result = rules.apply(step2, '/main/right');
      }
      return result.justify('applyToBoth', arguments, [h_bc]);
    },
    inputs: {term: 1, equation: 2},
    form: ('Apply function <input name=term>'
	   + ' to both sides of step <input name=equation>'),
    hint: 'from A = B to (F A) = (F B)',
    comment: 'given B = C deduce (f B) = (f C)',
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
    description: '=simpleApply'
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
                           Toy.subFree(newVar, target.bound, target.body));
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
    hint: 'embed both sides in a variable binding',
    comment: ('Wraps each side of an equation in a function'
              + ' using the bound variable of your choice.'),
    description: 'from a = b to {v. a} = {v. b}'
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
    hint: 'substitute for a variable in both sides',
    comment: ('Instantiates a free variable in an equation.'),
    description: 'substitute for {var}'
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
    description: mathMarkup('T = (a = a)')
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
    hint: 'from (A = B) to (T = (A = B))',
    comment: ('From [A = B] deduce T = [A = B].'),
    description: 'from a = b to T = (a = b)'
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
              ' T, and D by substituting F, proves A = B.')
  },

  // Note that this or 5230TF or symmetry of equality of booleans
  // might be taken as an axiom given r5230FT_alternate.
  tIsXIsX: {
    action: function() {
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
    hint: 'prove ((T = A) = A)',
    comment: ('For any expression A derives [T = A] = A.'),
    description: '(T = a) = a'
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
    hint: 'from A to (T = A)',
    comment: ('From A derives T = A'),
    description: mathMarkup('a = (T = a)')
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
    hint: 'from (T = A) to A',
    comment: ('From T = A derives A'),
    description: mathMarkup('(T = a) = a')
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
      assert(!(h_a.hasHyps && h_a.getLeft().hasFree(v.name)),
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

  // 5221 (one variable), in the given step substitute term A for
  // variable v, which may also be a string, which will be converted
  // to a variable.  Handles hypotheses, allowing substitution for a
  // variable even if free in the hypotheses.
  instVar: {
    action: function(step, a, v) {
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
    description: 'substitute for {var}'
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
      return result.justify('instantiateVar', arguments, [step]);
    },
    inputs: {site: 1, term: 3},
    form: ('Substitute <input name=term> for the selected variable.'),
    hint: 'substitute for a free variable',
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.'),
    description: 'substitute for {site}'
  },

  // More like the book's 5221.  For each name in the map (a string),
  // substitutes the expression associated with it in the map, using
  // simultaneous substitution.  Handles hypotheses, allowing
  // substitution for variables that are free in the hypotheses.
  instMultiVars: {
    action: function(b, map) {
      var hyps = b.hasHyps;
      var b = hyps ? rules.asImplication(b) : b;
      var namesReversed = [];
      var isEqn = b.unHyp().isCall2('=');
      var step = isEqn ? b : rules.toTIsA(b);
      for (var name in map) {
        step = rules.bindEqn(step, name);
	namesReversed.unshift(name);
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
    hint: 'from A and B to (A & B)',
    comment: ('Given a and b, derive a & b'),
    description: 'a & b;; using steps {step1}, {step2}'
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
    description: 'from p, p &rArr; q to q'
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
    comment: ('Evaluates a boolean expression with no free variables.'),
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
          if (Toy.isVariable(name)) {
            if (wff instanceof Toy.Call && wff.fn instanceof Toy.Call
                && wff.fn.fn instanceof Toy.Var && wff.fn.fn.name == '=') {
              // WFF is already an equation.
              var step1 = rules.tautology(Toy.subFree(T, name, wff));
              var step2 = rules.tautology(Toy.subFree(F, name, wff));
              var step3 = rules.equationCases(step1, step2, name);
              var result = step3.justify('tautology', arguments);
              _tautologies[key] = result;
              return result;
            } else {
              var step1 = rules.tautology(equal(T, Toy.subFree(T, name, wff)));
              var step2 = rules.tautology(equal(T, Toy.subFree(F, name, wff)));
              var step3 = rules.equationCases(step1, step2, name);
              var step4 = rules.fromTIsA(step3);
              var result = step4.justify('tautology', arguments);
              _tautologies[key] = result;
              return result;
            }
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
    hint: 'enter tautology',
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
	step3.hasHyps = true;
	return step3.justify('tautInst', arguments);
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
    hint: 'From theorem B deduce A ==> B',
    comment: ('Given a theorem, derive that something implies it.'),
    description: Toy.mathMarkup('a ==> T')
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
    form: ('Variable: <input name=varName> '
	   + 'wff without it free: <input name=term1> '
	   + 'other wff: <input name=term2>'),
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
    form: ('Move forall inside "implies" binding '
	   + 'variable <input name=varName> '
	   + 'implication <input name=implication>'),
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
    description: 'move forall'
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
  // makeConjunction.  Handles hypotheses by applying modus ponens to
  // the step.
  //
  // Accepts a string for the tautology.
  //
  // Andrews calls his enhanced version of forward chaining "Rule P".
  // (In this implementation it is more straightforward to use
  // makeConjunction as needed, followed by forwardChain.)
  forwardChain: {
    action: function(step, schema) {
      var substitution = Toy.matchAsSchema(schema.getLeft(), step.unHyp());
      var step2 = rules.instMultiVars(schema, substitution);
      var step3 = rules.modusPonens(step, step2);
      return step3.justify('forwardChain', arguments, [step, schema]);
    },
    inputs: {step: [1, 2]},
    form: ('Match step <input name=step1> with left side of implication '
           + 'in schema <input name=step2>'),
    comment: ('match with A in A ==> B'),
    description: 'consequence;; of step {step1} using step {step2}'
  },

  // Proves the goal by matching it with the conclusion of the given
  // theorem and then applying the given inference rule to prove the
  // premise of the instantiated theorem.  The theorem must be an
  // implication.
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
  instantiate: {
    action: function(schema, path, term) {
      var subst = term.matchSchema(schema.locate(path));
      var result = rules.instMultiVars(schema, subst);
      return result.justify('instantiate', arguments, [schema]);
    }
  },

  // Finds a "subgoal" statement that implies the goal via the given
  // theorem, which must be a schema of the form a ==> b.
  // Instantiates the theorem by matching the goal against the theorem
  // RHS, returning the instantiated theorem.
  subgoal: {
    action: function(goal, theorem) {
      theorem.assertCall2('==>');
      var subst = goal.matchSchema(theorem.getRight());
      var result = rules.instMultiVars(theorem, subst);
      return result.justify('subgoal', arguments);
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
      var step1 = rules.axiom('axiom3');
      var step2 = rules.changeVar(step1, '/right/arg', v);
      var step3 = rules.instMultiVars(step2,
                               ({f: lambda(v, a),
                                 g: lambda(v, b)}));
      var step4 = rules.apply(step3, '/right/arg/body/left');
      var step5 = rules.apply(step4, '/right/arg/body/right');
      // Do not "derive", leave this inline.
      return step5;
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
      var g = target.replace(path, function(expr) { return texpr; });
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
  // For convenience applies rule R directly if the equation is really
  // an equation and not an implication.
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
      assert(h_equation.isCall2('==>') && h_equation.getRight().isCall2('='),
	     'Not an equation: ' + h_equation, h_equation_arg);
      // h_equation has the form H ==> A = B

      // Give the two WFFs the same hypotheses.
      h_c = rules.appendStepHyps(h_c, h_equation);
      h_equation = rules.prependStepHyps(h_equation, h_c_arg);

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
    form: ('Replace selection with right side of step <input name=step>'),
    comment: 'replace an expression with an equal one',
    description: 'replace {site};; {siteStep in step} {equation using step}'
  },
    
  // Add hypotheses to the step from hypStep.  This is key to providing
  // two steps with the same hypotheses in preparation for applying
  // various rules of inference.  If hypStep has no hypotheses, the result
  // is simply the given step.
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
	  // Simplify (h1 & h2) ==> p
	  var step4 = rules.mergeConjunctions(step2.locate('/left'));
	  var step5 = rules.r(step4, step2, '/left');
          // Rendering of result needs hypStep rendered, so include it as dep.
	  var result =
	    step5.justify('appendStepHyps', arguments, [target, hypStep]);
	  result.hasHyps = true;
	  return result;
	} else {
	  // The target does not have hyps.
	  var subst = {
	    p: target,
	    h2: hypStep.getLeft()
	  };
	  var step1 = rules.tautInst('p ==> (h2 ==> p)', subst);
	  var step2 = rules.modusPonens(target, step1);
          // Rendering of result needs hypStep rendered, so include it as dep.
	  var result =
            step2.justify('appendStepHyps', arguments, [target, hypStep]);
	  result.hasHyps = true;
	  return result;
	}
      } else {
	// Don't do anything and don't display any new proof step.
	return target;
      }
    },
    inputs: {step: [1, 2]},
    form: ('Add to step <input name=step1> hypotheses from step '
	   + '<input name=step2>'),
    hint: 'append hypotheses to step {step1} from step {step2}'
  },

  // Prefix hypotheses from the hypStep to the target step.  Often
  // used together with appendStepHyps.  If hypStep has no hypotheses,
  // the result is simply the given step.
  //
  // TODO: Combine this and appendStepHyps into one rule.  Consider a
  //   rule that derives (H ==> step1rhs) & (H ==> step2rhs) from
  //   step1 and step2.  H will be the merger of the hypotheses.
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
	  // Simplify (h1 & h2) ==> p
          var pattern = rules.mergeConjunctions(step2.getLeft());
          var step5 = rules.rewrite(step2, '/left', pattern);
          // Rendering of result needs hypStep rendered, so include it as dep.
	  var result =
            step5.justify('prependStepHyps', arguments, [target, hypStep]);
	  result.hasHyps = true;
	  return result;
	} else {
	  var subst = {
	    p: step,
	    h1: hypStep.getLeft()
	  };
	  var step1 = rules.tautInst('p ==> (h1 ==> p)', subst);
	  var step2 = rules.modusPonens(step, step1);
          // Rendering of result needs hypStep rendered, so include it as dep.
	  var result =
            step2.justify('prependStepHyps', arguments, [target, hypStep]);
	  result.hasHyps = true;
	  return result;
	}
      } else {
	// Don't display this no-op inference step.
	return target;
      }
    },
    inputs: {step: [1, 2]},
    form: ('To step <input name=step1> prefix the hypotheses of step '
	   + '<input name=step2>'),
    hint: 'prepend hypotheses from step {step2} to {step1}'
  },

  // Takes a proof step, a path, and a proved equation.
  // If the part of the step at the given path
  // matches the LHS of the equation, replaces that part of the step
  // with the appropriate instance of the equation, otherwise return
  // the input step.  The step and equation may have hypotheses.
  rewrite: {
    action: function(step, path, equation) {
      var expr = step.locate(path);
      var map = expr.findSubst(equation.unHyp().getLeft());
      assert(map, function() {
          return 'Sorry, rule does not match';
        });
      var step1 = rules.instMultiVars(equation, map);
      var result = rules.replace(step1, step, path);
      return result.justify('rewrite', arguments, [step, equation]);
    },
    inputs: {site: 1, equation: 3},
    form: ('Rewrite the site using equation <input name=equation>'),
    hint: 'Instantiate an equation so its LHS equals an expression.',
    description: 'rewrite {site} {siteStep in step} {equation using step}'
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
            // and replace the RHS of the argument with the final esult.
	    return rules.r(step3, eqn, '/right');
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

  // Internal rule for mergeConjunctions, with a comparator parameter.
  mergeConj: {
    action: function(expr, less) {
      expr.assertCall2('&');
      var eqn = rules.eqSelf(expr);
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
      var eqn1 = rules.mergeRight(eqn);
      var chain2 = eqn1.getRight();
      var eqn3 = rules.bubbleLeft(chain2, less);
      eqn = rules.r(eqn3, eqn1, '/right');
      return eqn;
    },
  },

  // From a term that is a conjunction of two normalized chains of
  // conjunctions, derive an equation that has the input as its LHS
  // and as its RHS has conjuncts ordered by sourceStepLess, with
  // duplicates eliminated.
  mergeConjunctions: {
    action: function(expr) {
      var result = rules.mergeConj(expr, Toy.sourceStepLess);
      return result.justify('mergeConjunctions', arguments);
    },
    inputs: {term: 1},
    // Too technical to expose for most users.
    // form: ('Chains of conjunctions to merge: <input name=term>'),
    hint: 'Derives an equation to merge chains of input conjunctions',
    description: 'merge conjunctions in {term}'
  },    

  // Simplify the hypotheses of a step, removing duplicates.
  // Incomplete, unused.
  simplifyHyps: {
    // Note that "replace" does not even call this if its inputs have
    // tbe same hypotheses.
    action: function(step) {
      if (!step.hasHyps) {
	// Do nothing, don't even display that simplification of
	// hypotheses was part of the proof.
	return step;
      }
      var hyps = step.getLeft();
      if (hyps.isCall2('&')) {
	
      } else {
	// Again, don't display this as a step.
	return step;
      }
    },
    inputs: {step: 1},
    // form: ('Normalize a conjunction <input name=step>'),
    hint: 'Normalize a conjunction of normalized conjunctions'
  },

  // Extract the given hypothesis from the given step.  The hypothesis
  // need only match one of the step's hypotheses.  Relies on the step
  // to have normalized (flattened) hypotheses.
  extractHypothesis: {
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
      return result.justify('extractHypothesis', arguments, [step]);
    },
    inputs: {step: 1, term: 2},
    form: ('Make assumption <input name=term> explicit '
           + 'in step <input name=step>'),
    description: 'make assumption {term} explicit {step in step}',
    comment: 'Find and extract a hypothesis from a step.'
  },

  // Given a proof step that is an implication and a path expected to
  // refer to an element of the LHS conjunction chain, derives a step
  // of the form e ==> (h' ==> c) where e is the referenced element,
  // h' is the proof step's hypotheses excluding occurrences of "e",
  // and c is the impliction RHS.  Useful for simplifying hypotheses.
  isolateCondition: {
    action: function(step, path) {
      assert(step.isCall2('==>') && !step.hasHyps, 'Not an implication');
      var taut = rules.tautology(step.getLeft().hypMover(step.locate(path)));
      var step1 = rules.rewrite(step, '/left', taut);
      var taut2 = rules.tautology('a & b ==> c == b ==> (a ==> c)');
      var result = rules.rewrite(step1, '', taut2);
      return result.justify('isolateCondition', arguments, [step]);
    },
    inputs: {site: 1},
    form: '',
    comment: 'Move conjunct of implication LHS all the way to the right'
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
  // deduplicated version, or returns null if there are no exact
  // duplicate terms.  If a comparator function is supplied, it
  // defines an ordering of the deduplicated terms by return true when
  // its first argument is less than its second.
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
      if (map.size() == allTerms.length) {
        return null;
      }
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
        Toy.infixCall(buildConj(allTerms), '=', buildConj(keepTerms));
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
      var result = (deduper
                    ? rules.replace(deduper, step, '/left')
                    : step);
      return result.justify('dedupeHyps', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    comment: 'Remove redundant hypotheses'
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
    comment: 'Prove equality of two chains of conjunctions'
  },


  // As long as "finder" finds an inference rule to apply to the term,
  // keep calling it and applying the rewrite rule it returns.  The
  // result is the step with the final replacement term, never null.
  repeatedlyRewrite: {
    action: function(step, path, finder) {
      var term = step.locate(path);
      var equation = rules.eqSelf(term);
      var rewriter;
      while (rewriter = finder(equation.getRight())) {
        equation = rules.rewrite(equation, '/right', rewriter);
      }
      var result = rules.replace(equation, step, path);
      return result.justify('repeatedlyRewrite', arguments, [step]);
    }
  },

  // From the section "Equality and descriptions"

  equalitySymmetric: {
    action: function() {
      var step1 = rules.assume('x = y');
      var step2 = rules.eqSelf(x);
      var step3 = rules.replace(step1, step2, '/left');
      var step4 = rules.asImplication(step3);
      var subst = {x: y, y: x};
      var step5 = rules.instMultiVars(step4, subst);
      var step6 = rules.makeConjunction(step4, step5);
      var taut = rules.tautology('(p ==> q) & (q ==> p) ==> (p = q)');
      var step7 = rules.forwardChain(step6, taut);
      return step7.justify('equalitySymmetric', arguments);
    },
    inputs: {},
    form: '',
    comment: 'Symmetry of equality'
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
    comment: 'Transitivity of equality'
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
    description: 'commutativity'
  },

  axiomAssociativePlus: {
    action: function() {
      return rules.assert('R x & R y & R z ==> x + (y + z) = (x + y) + z')
	.asHyps().justify('axiomAssociativePlus');
    },
    inputs: {},
    form: '',
    comment: 'associativity of addition',
    description: 'associativity'
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
    description: 'associativity'
  },

  axiomDistributivity: {
    action: function() {
      return rules.assert('R x & R y & R z ==> x * (y + z) = x * y + x * z')
	.asHyps().justify('axiomDistributivity');
    },
    inputs: {},
    form: '',
    comment: 'distributive law',
    description: 'distributivity'
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
    description: 'definition of neg'
  },

  axiomReciprocal: {
    action: function() {
      return rules.assert('R x & x != 0 ==> x * recip x = 1')
        .asHyps().justify('axiomReciprocal');
    },
    inputs: {},
    form: '',
    comment: 'x * recip x = 1 if x is not 0',
    description: 'definition of recip'
  },

  // Note: not structured as a rewrite rule.
  axiomPlusType: {
    action: function() {
      return rules.assert('R x & R y ==> R (x + y)')
	.justify('axiomPlusType');
    },
    inputs: {},
    form: '',
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
    comment: 'negation of real number is real',
    description: 'negation of real number is real'
  },

  axiomReciprocalType: {
    action: function() {
      return rules.assert('R x & x != 0 == R (recip x)')
	.justify('axiomReciprocalType');
    },
    inputs: {},
    form: '',
    comment: 'reciprocal of nonzero real number is real',
    description: 'reciprocal of real number'
  },

  // Evaluates arithmetic expressions with operators:
  // +, -, *, /, neg, =, >, >=, <, <=, and the type operator "R".
  // Checks that inputs are all numeric and that the result can be
  // guaranteed to be an exact integer.
  axiomArithmetic: {
    action: function(term) {
      if (term.isInfixCall()) {
	var left = Toy.checkNumber(term.getLeft().value);
	var right = Toy.checkNumber(term.getRight().value);
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
        case '=': value = left == right; break;
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
        var arg = Toy.checkNumber(term.arg.value);
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
    comment: 'Evaluate an arithmetic expression',
    description: 'axiom of arithmetic'
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
    comment: 'difference of real numbers is real',
    description: 'difference of real numbers is real'
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
      return step8.justify('divisionType');
    },
    form: '',
    comment: 'quotient of real numbers is real',
    description: 'quotient of real numbers is real'
  },

  //
  // Inference rules for real numbers
  //

  // Convert a simple arithmetic expression to its value.
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
    comment: 'Evaluate arithmetic expression'
  },

  // Managing numeric type hypotheses

  // Apply type expression rewriter rules (equations) to type
  // expressions of the form (R <term>) in the LHS of the given proved
  // implication.  Also does special-case removal of hyps like 2 != 0.
  numericTypesSimplifier: {
    action: function(allHyps) {
      var infix = Toy.infixCall;
      var deduper =
        rules.conjunctionDeduper(allHyps, Toy.sourceStepComparator);
      var simplifier = rules.eqSelf(allHyps);
      if (deduper) {
        simplifier = rules.replace(deduper, simplifier, '/right');
      }
      // Now RHS of simplifier has no duplicate terms.
      var hypSet = new Toy.TermSet();
      simplifier.getRight().eachHyp(function (hyp) { hypSet.add(hyp); });
      // Convert (R <n>) to T and (<n> != <m>) to T or F.
      hypSet.each(function(hyp) {
        var hyps = simplifier.getRight();
        if (hyp.isCall1('R') && (hyp.arg.isNumeral())) {
          var equation = rules.axiomArithmetic(hyp);
          var path = Toy.path('/right' + hyps.pathTo(hyp));
          simplifier = rules.replace(equation, simplifier, path);
        } else if (hyp.isCall2('!=') &&
                   hyp.getLeft().isNumeral() &&
                   hyp.getRight().isNumeral()) {
          // Special case, also simplifies hyps like "2 != 0".
          var eqn = rules.eqSelf(hyp);
          var eqn2 = rules.arithmetic(eqn, '/right');
          var path = Toy.path('/right' + hyps.pathTo(hyp));
          simplifier = rules.r(eqn2, simplifier, path);
        }
      });
      // Remove occurrences of T.
      deduper =
        rules.conjunctionDeduper(simplifier.getRight(), Toy.sourceStepComparator);
      if (deduper) {
        simplifier = rules.replace(deduper, simplifier, '/right');
      }
      // Prove types of complex expressions by breaking them down and
      // proving the parts..
      hypSet = new Toy.TermSet();
      simplifier.getRight().eachHyp(function(hyp) { hypSet.add(hyp); });
      hypSet.each(function(hyp) {
          var hyps = simplifier.getRight();
          if (hyp.isCall1('R') && hyp.arg instanceof Toy.Call) {
            var otherHyps = hypsExcept(hyps, new Toy.TermSet(hyp));
            var goal = infix(otherHyps, '==>', hyp);
            // Proved that hyp is a consequence of the others.
            // TODO: Prove the hyp from just the relevant set hypotheses,
            //   then use rules.conjunctsImplyConjunct and
            //   rules.makeConjunction to prove those hyps from the
            //   full set of hyps.
            try {
              var proved = rules.justifyNumericType(goal);
            } catch(e) {
              var msg = 'numericTypesSimplifier: unable to prove ' +
                goal.toString();
              throw new Error(msg, goal);
            }
            var taut = rules.tautology('(a ==> b) == (a & b == a)');
            // otherHyps & hyp == otherHyps:
            var subsumption = rules.rewrite(proved, '', taut);
            var ab = subsumption.getLeft();
            // hyps = otherHyps & hyp:
            var step1 = rules.equalConjunctions(infix(hyps, '=', ab));
            // So hyps = otherHyps:
            var step2 = rules.r(subsumption, step1, '/right');
            // So now allHyps = otherHyps:
            simplifier = rules.replace(step2, simplifier, '/right');
          }
        });
      return simplifier.justify('numericTypesSimplifier', arguments);
    },
    inputs: {term: 1},
    form: 'Conjunction to simplify: <input name=term>',
    comment: 'Remove redundant type hypotheses in a conjunction'
  },

  // Apply type expression rewriter rules (equations) to type
  // expressions of the form (R <term>) in the LHS of the given proved
  // implication.  Deduplicate and put them in the usual order.
  simplifyNumericTypes: {
    action: function(step) {
      var infix = Toy.infixCall;
      step.assertCall2('==>');
      var equation = rules.numericTypesSimplifier(step.getLeft());
      var result = rules.r(equation, step, '/left');
      return result.justify('simplifyNumericTypes', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    comment: 'Remove redundant type hypotheses in a step'
  },

  // Prove a goal statement of the form "hyps ==> (R <term>)" in
  // preparation for removing the term on the RHS from the full set of
  // hypotheses of some proof step.  Can throw an exception.
  justifyNumericType: {
    action: function(goal) {
      // TODO: Break down the proof using only the required conjuncts
      //   to prove the RHS, then prove that the full set of conjuncts
      //   implies the required ones.  Create a new
      //   rules.conjunctsImplyConjunct to make this fast.
      var infix = Toy.infixCall;
      var subst = goal.matchSchema('h ==> (R e)');
      assert(subst, 'Bad input to justifyNumericType: ' + goal);
      var target = goal.getRight();
      var hyps = subst.h;
      var expr = subst.e;
      var map = new Toy.TermMap();
      var schema = buildHypSchema(hyps, map);
      var result;
      // Prove the various forms of targets.
      if (expr.isNumeral()) {
        var step1 = rules.axiomArithmetic(goal.getRight());
        var step2 = rules.eqnSwap(step1);
        var step3 = rules.fromTIsA(step2);
        result = rules.anyImpliesTheorem(hyps, step3);
      } else if (map.has(target)) {
        var taut = rules.tautology(infix(schema, '==>', map.get(target)));
        result = rules.instantiate(taut, '', goal);
      } else if (expr.isVariable()) {
        // Need to prove (R x), but there is no hypothesis (R x).
        // Just add it to the hypotheses.
        result = rules.tautInst('h & a ==> a', {h: hyps, a: target});
      } else if (expr.isCall2()) {
        var op = expr.getBinOp();
        var theorems = {
          '+': rules.axiomPlusType(), '*': rules.axiomTimesType(),
          '-': rules.subtractionType(), '/': rules.divisionType()
        };
        assert(subst && op instanceof Toy.Var && theorems[op.name]);
        var theorem = theorems[op.name];
        var implication = rules.subgoal(target, theorem);
        var subst2 = implication.matchSchema('h1 & h2 ==> p');
        // Solve the two simplified problems:
        var thm1 = rules.justifyNumericType(infix(hyps, '==>', subst2.h1));
        var thm2 = rules.justifyNumericType(infix(hyps, '==>', subst2.h2));
        // Show that the conjunction of the simpler numeric type terms
        // is a consequence of the hypotheses.
        var conj = rules.makeConjunction(thm1, thm2);
        var taut = rules.tautology('(h ==> a) & (h ==> b) ==> (h ==> a & b)');
        var step1 = rules.forwardChain(conj, taut);
        var instance = rules.instantiate(theorem, '/left', step1.getRight());
        var step2 = rules.makeConjunction(step1, instance);
        var taut2 = rules.tautology('(h ==> a) & (a ==> b) ==> (h ==> b)');
        result = rules.forwardChain(step2, taut2);
      } else if (expr.isCall1('neg')) {
        var subgoal = infix(hyps, '==>', call('R', expr.arg));
        var step1 = rules.justifyNumericType(subgoal);
        var rewriter = rules.axiomNegType();
        result = rules.rewrite(step1, '/right', rewriter);
      } else if (expr.isCall1('recip')) {
        var subgoal1 = infix(hyps, '==>', call('R', expr.arg));
        var step1 = rules.justifyNumericType(subgoal1);
        // Justify this term as a consequence of either arithmetic or
        // the hypotheses:
        var term = infix(expr.arg, '!=', new Toy.Var('0'));
        var arith;
        try {
          var arithEqn = rules.eqSelf(term);
          arith = rules.arithmetic(arithEqn, '/left');
        } catch(e) {
          // The term is not true by arithmetic, is it a hypothesis?
          //
          // TODO: Consider adding the hypothesis to the proved result
          //   if needed.
          assert(map.has(term), 'Step needs hypothesis: ' + term);
          var subgoal2 = infix(hyps, '==>', term);
          var taut2 = rules.tautology(infix(schema, '==>', map.get(term)));
          var step2 = rules.instantiate(taut2, '', subgoal2);
        }
        if (arith) {
          var step1b = rules.fromTIsA(arith);
          var step2 = rules.anyImpliesTheorem(hyps, step1b);
        }
        // h ==> term is now proved.
        var conj = rules.makeConjunction(step1, step2);
        var taut = rules.tautology('(h ==> a) & (h ==> b) ==> (h ==> a & b)');
        var step3 = rules.forwardChain(conj, taut);
        var result = rules.rewrite(step3, '/right', rules.axiomReciprocalType());
      } else {
        // See if maybe the entire goal is an instance of a tautology.
        var rhs = buildHypSchema(target, map);
        var taut = infix(hyps, '==>', rhs);
        // This may throw an exception.
        return rules.tautInst(taut, map.subst);
      }
      return result.justify('justifyNumericType', arguments);
    },
    inputs: {term: 1},
    form: 'Goal wff: <input name=term>',
    comment: 'Derive H ==> R (<left> <binop> <right>).'
  },

  // Finds and returns type expression rewrite rule that can rewrite
  // the term to eliminate a call to "neg" or "recip" or a numeric
  // literal, e.g. (R (neg <term>) = (R <term>)).  Returns null if it
  // finds no suitable rewriter.
  //
  // TODO: Remove me.
  findTypeRewriter: {
    action: function(term) {
      var result = null;
      if (term.isCall1('R')) {
        if (term.arg.isNumeral()) {
          result = rules.axiomArithmetic(term);
        } else if (term.arg.isCall1('neg')) {
          var step1 = rules.axiomNegType();
          result = rules.eqnSwap(step1);
        } else if (term.arg.isCall1('recip')) {
          var step1 = rules.axiomReciprocalType();
          result = rules.eqnSwap(step1);
        }
      }
      if (result) {
        return result.justify('findTypeRewriter', arguments);
      } else {
        return null;
      }
    },
    inputs: {term: 1},
    form: 'Term to rewrite: <input name=term>',
    comment: 'Find rewriter to simplify type expression with neg or recip.'
  },

  // Consider a term that we may wish to rewrite.  If the term has no
  // arithmetic operators, this is the same as eqSelf, but it
  // automatically assumes variables input to math operators are of
  // type R (real).
  consider: {
    description: 'expression to consider',
    action: function(term) {
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
    comment: ('Term to consider for transformation')
  },

  // Identical to "consider", but uses a selected term.
  considerPart: {
    action: function(step_arg, path) {
      var term = step_arg.locate(path);
      var step = rules.eqSelf(term);
      var conditions = term.mathVarConditions();
      if (conditions) {
        step = rules.anyImpliesTheorem(conditions, step);
        step = rules.asHypotheses(step);
      }
      return step.justify('considerPart', arguments);
    },
    inputs: {site: 1},
    form: '',
    comment: ('Consider a subexpression for transformation'),
    description: 'consider'
  },

  addToBoth: {
    action: function(eqn, term) {
      var fn = lambda(x, Toy.infixCall(x, '+', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('addToBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Add <input name=term> to both sides of ' +
           'step <input name=equation>'),
    comment: ('Add the same amount to both sides of the equation'),
    description: 'add {term}'
  },

  subtractFromBoth: {
    action: function(eqn, term) {
      var fn = lambda(x, Toy.infixCall(x, '-', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('subtractFromBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Subtract <input name=term> from both sides of ' +
           'step <input name=equation>'),
    comment: ('Subtract the same amount from both sides of the equation'),
    description: 'subtract {term}'
  },

  multiplyBoth: {
    action: function(eqn, term) {
      var fn = lambda(x, Toy.infixCall(x, '*', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('multiplyBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Multiply both sides of step <input name=equation>' +
           ' by <input name=term>'),
    comment: ('Multiply both sides of the equation by the same amount'),
    description: 'multiply by {term}'
  },

  divideBoth: {
    action: function(eqn, term) {
      var fn = lambda(x, Toy.infixCall(x, '/', term));
      var result = rules.applyToBoth(fn, eqn);
      return result.justify('divideBoth', arguments, [eqn]);
    },
    inputs: {equation: 1, term: 2},
    form: ('Divide both sides of step <input name=equation>' +
           ' by <input name=term>'),
    comment: ('Divide both sides of the equation by the same amount'),
    description: 'divide by {term}'
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

};  // End of theorems and rules

// Descriptions of rewrite rules; internal.  Each of these generates
// an actual inference rule.
var rewriters = {
  commutePlus: {
    axiom: 'axiomCommutativePlus',
    description: mathMarkup('a + b = b + a')
  },
  commuteTimes: {
    axiom: 'axiomCommutativeTimes',
    description: mathMarkup('a * b = b * a')
  },
  associatePlusToLeft: {
    axiom: 'axiomAssociativePlus',
    description: mathMarkup('a + (b + c) = (a + b) + c')
  },
  associatePlusToRight: {
    axiom: 'axiomAssociativePlus',
    description: mathMarkup('(a + b) + c = a + (b + c)'),
    input: 'right'
  },
  associateTimesToLeft: {
    axiom: 'axiomAssociativeTimes',
    description: mathMarkup('a * (b * c) = (a * b) * c')
  },
  associateTimesToRight: {
    axiom: 'axiomAssociativeTimes',
    description: mathMarkup('(a * b) * c = a * (b * c)'),
    input: 'right'
  },
  distribute: {
    axiom: 'axiomDistributivity',
    description: mathMarkup('a * (b + c) = (a * b) + (a * c)')
  },
  group: {
    axiom: 'axiomDistributivity',
    description: mathMarkup('(a * b) + (a * c) = a * (b + c)'),
    input: 'right'
  },
  plusZeroElim: {
    axiom: 'axiomPlusZero',
    description: mathMarkup('a + 0 = a')
  },
  plusZeroIntro: {
    axiom: 'axiomPlusZero',
    description: mathMarkup('a = a + 0'),
    input: 'right'
  },
  timesOneElim: {
    axiom: 'axiomTimesOne',
    description: mathMarkup('a * 1 = a')
  },
  timesOneIntro: {
    axiom: 'axiomTimesOne',
    description: mathMarkup('a = a * 1'),
    input: 'right'
  },
  timesZeroElim: {
    axiom: 'axiomTimesZero',
    description: mathMarkup('a * 0 = 0')
  },
  plusNegElim: {
    axiom: 'axiomNeg',
    description: mathMarkup('a + neg a = 0')
  },
  timesRecipElim: {
    axiom: 'axiomReciprocal',
    description: mathMarkup('a * recip a = 1')
  }
};  

/**
 * Adds information to the ruleInfo map based on a map of rewriting
 * descriptors such as "rewriters".  The rewriting descriptors map has
 * an entry for each standardized rewrite rule.  The name in the map
 * becomes the name of the inference rule.  The "axiom" property
 * becomes the name of the axiom to use for the rewriting.  The
 * "input" property, either "left" or "right" indicates which side of
 * the equational axiom is the pattern to match the target.  If
 * omitted, the value is taken as "left".  The "comment" property if
 * given becomes the rule's comment.
 */
function genRewriters(map) {
  for (var name in map) {
    var info = map[name];
    var generators = {
      'left': rewriteWithAxiom,
      'right': rewriteBackWithAxiom
    };
    var input = info.input || 'left';
    if (info.comment) {
      var comment = info.comment;
    } else {
      // Remember ruleInfo is still not processed into Toy.rules.
      var fact = info.axiom;
      var desc = ruleInfo[info.axiom].description || info.axiom;
      var comment = 'Rewrite using ' + desc;
    }
    // Add this info to ruleInfo:
    ruleInfo[name] = {
      // Highlight sites in inputs as usual for rewrite rules.
      isRewriter: true,
      action: (function(axiomName, ruleName, generator) {
        // Capture the current info.axiom and name.  In JS
        // calling a new function is the way to do it.
        return function(step, path) {
          return generator(step, path, axiomName, ruleName);
        }
        })(info.axiom, name, generators[input]),
      inputs: {site: 1},
      template: info.axiom,
      templateSide: input,
      form: '',
      description: info.description || name,
      comment: comment
    };
  }
}

/**
 * Standardized rewriting rule that uses an equational axiom.
 */
function rewriteWithAxiom(step, path, axiomName, ruleName) {
  var axiom = rules[axiomName]();
  var step1 = rules.rewrite(step, path, axiom);
  var result = rules.simplifyNumericTypes(step1);
  // Justify the step with the given ruleName.  This is appropriate
  // since genRewriters attaches it as "rules.ruleName".
  return result.justify(ruleName, arguments, [step]);
}

/**
 * Standardized rewriting rule that uses an equation axiom, using RHS
 * as the pattern and the LHS as template for the result.
 */
function rewriteBackWithAxiom(step, path, axiomName, ruleName) {
  var axiom = rules[axiomName]();
  var back = rules.eqnSwap(axiom);
  var step1 = rules.rewrite(step, path, back);
  var result = rules.simplifyNumericTypes(step1);
  return result.justify(ruleName, arguments, [step]);
}

// Add rewriting rules based on the axioms.
genRewriters(rewriters);

// Map from rule name to function.  See creatRules, below.
var rules = {};

/**
 * Given a ruleInfo object, add its information to the "rules" object.
 * The "rules" object maps from rule name to function.  Each function
 * has an "info" property containing all the properties present in the
 * ruleInfo object entry for the name.  If not supplied in the rule
 * definition, the info.inputs is defaulted to an empty object here.
 */
function createRules(ruleInfo) {
  for (var key in ruleInfo) {
    var info = ruleInfo[key];
    if (!info.inputs) {
      info.inputs = {};
    }
    // The default description is just the rule name
    if (!('description' in info)) {
      info.description = key;
    }
    var fn = (typeof info == 'function') ? info : info.action;
    // Associate the action function with the key,
    rules[key] = fn;
    // and metadata as the function's "info" property.
    rules[key].info = info;
  }
}

// Actual rule functions to call from other code.
createRules(ruleInfo);

var identity = lambda(x, x);
var allT = lambda(x, T);

// Put definitions into their database:
Toy.define('not', equal(F));
Toy.define('!=', '{x. {y. not (x = y)}}');
Toy.define('forall', equal(lambda(x, T)));
Toy.define('exists', '{x. F} !=');
Toy.defineCases('&', identity, lambda(x, F));
Toy.defineCases('|', allT, identity);
Toy.defineCases('==>', identity, allT);

Toy.define('-', '{x. {y. x + neg y}}');
Toy.define('/', '{x. {y. x * recip y}}');

//// THEOREMHOOD

// Private to addTheorem, getTheorem, and the initializations
// at the bottom of this file.  Maps from name to an inference
// containing a proof of the theorem, or true, indicating
// 
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

// Add the axioms and theorems to the "database".  This can only
// include ones that are not "axiom schemas", i.e. not parameterized.
// Most of these axioms really have type parameters.  Ideally axiom
// and theorem schemas will be able to stay, but the details remain
// to be determined.

var axiomNames = ['axiom1', 'axiom2', 'axiom3', 'axiom5', 'axiomPNeqNotP',
                  'axiomCommutativePlus', 'axiomAssociativePlus',
                  'axiomCommutativeTimes', 'axiomAssociativeTimes',
                  'axiomDistributivity', 'axiomPlusZero', 'axiomTimesOne',
                  'axiomTimesZero', 'axiomNeg', 'axiomReciprocal',
                  'axiomPlusType', 'axiomTimesType',
                  'axiomNegType', 'axiomReciprocalType'];

var theoremNames =
  (axiomNames.concat(['defFFromBook', 'r5217Book', 'r5225',
                      'defAnd', 'tIsXIsX', 'forallXT', 'xAlwaysX',
                      'r5211', 't', 'r5212', 'r5230TF', 'r5230FT',
                      'r5231T', 'r5231F', 'falseEquals', 'trueEquals',
                      'subtractionType', 'divisionType']));

for (var i = 0; i < theoremNames.length; i++) {
  addTheorem(theoremNames[i]);
}


//// UTILITY FUNCTIONS

/**
 * Build a schema for a conjunction of hypotheses, ensuring all are in
 * the TermMap, with optional exclusions, a TermSet.  The schema is of
 * the form a1 && ... && an, where the "a"s are variables for the
 * terms for each hyp in hyps.  Helper for eliminateBinaryOpTypes.
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

// A settable variable, export right here:
Toy.autoAssert = false;

Toy.axiomNames = axiomNames;
Toy.theoremNames = theoremNames;
Toy.addTheorem = addTheorem;
Toy.getTheorem = getTheorem;
Toy.findHyp = findHyp;

// For testing.
Toy.ruleInfo = ruleInfo;
Toy._tautologies = _tautologies;
Toy._buildHypSchema = buildHypSchema;

}, '0.1', {requires: ['array-extras', 'expr', 'proof']});
