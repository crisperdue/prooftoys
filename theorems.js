// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('theorems', function(Y) {


//// THEOREMS AND RULES

// Use the application's "assert" rather than YUI's.
var assert = Y.assertTrue;
// And make assertEqn convenient too.
var assertEqn = Y.assertEqn;

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

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
// hint: HTML text for the hint to be displayed by the autocompleter
//   of the step editor.
// comment: plain text comment to become the title of mentions of the rule
//   name in proof displays and the description in subproof displays.
var ruleInfo = {

  /**
   * The name "assertion" is used in displays to indicate that
   * the result of the inference is an assertion.  If given a string,
   * parses it and uses the result as its input.
   */
  assert: {
    action: function(assertion) {
      if (typeof assertion == 'string') {
	assertion = Y.parse(assertion);
      }
      return assertion.justify('assert', [assertion]);
    },
    inputs: {term: 1},
    form: ('Assert <input name=term>'),
    hint: 'Assert as universally true',
    comment: 'WFF to assert (possibly to prove later)'
  },

  define: {
    action: function(name, definition) {
      return Y.define(name, definition).justify('define', arguments);
    },
    inputs: {varName: 1, term: 2},
    form: ('Define name <input name=varName> as <input name=term>'),
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
	assumption = Y.parse(assumption);
      }
      var types = assumption.mathVarConditions();
      // TODO: Fix tautInst to not copy.
      if (types) {
        var step1 = rules.tautInst('h && a --> a', {
            a: assumption,
            h: types
          });
        var step = rules.dedupeHyps(step1);
      } else {
        var step = rules.tautInst('a --> a', {a: assumption});
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
    comment: 'Hypothesis to assume'
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
    comment: 'Convert hypotheses to an explicit implication'
  },
      
  /**
   * From an implication with LHS consisting of a set of hypotheses,
   * derives the equivalent step with the hypotheses.
   */
  asHypotheses: {
    action: function(step) {
      step.assertCall2('-->');
      var result = step.justify('asHypotheses', arguments, [step]);
      result.hasHyps = true;
      return result;
    },
    inputs: {implication: 1},
    form: ('Convert implication to hypotheses in step '
           + '<input name=implication>'),
    hint: 'Convert explicit implication to statement with hypotheses'
  },

  /**
   * Refer to a theorem by looking it up in the database rather
   * than proving it all over again.
   */
  theorem: function(name) {
    return Y.getTheorem(name).justify('theorem', [name]);
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
      return Y.getDefinition(name, tOrF).justify('definition', args);
    },
    inputs: {string: 1, optString: 2},
    form: ('Definition of <input name=string> '
           + 'if by cases enter T or F <input name=optString>'),
    comment: 'access a definition'
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
    var result = Y.getTheorem(name).justify(name);
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
      path = Y.path(path);
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
        assert(Y.autoAssert,
               function() { return 'Rule R unproven equation: ' + equation; });
	equation.assert();
      }
      if (!target.ruleName) {
        assert(Y.autoAssert,
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
	  Y.findType(result);
	  break;
	}
      }
      var result = target.hasHyps ? result.asHyps() : result;
      var justified = result.justify('r', [equation, target, path],
                                     [target, equation]);
      return justified;
    },
    // inputs: {equation: 1, site: 2},
    // form: ('Replace selection with right side of step <input name=equation>'),
    comment: ('Replace an occurrence of a term with an equal term.'),
    hint: 'Replace term with equal term'
  },

  /**
   * Same as "replace", but replaces an occurrence in target of the right
   * side of the equation with its left side.  Accepts hypotheses.
   */
  rRight: {
    action: function(equation, target, path) {
      path = Y.path(path);
      var rev = rules.eqnSwap(equation);
      var result = rules.replace(rev, target, path);
      return result.justify('rRight', arguments, [target, equation]);
    },
    inputs: {equation: 1, site: 2},
    form: ('Replace with left side of step <input name=equation>'),
    hint: 'replace term with equal term',
    comment: ('Replaces an occurrence of a term with an equal term,'
              + ' replacing right side with left side.')
  },

  axiom1: {
    action: function() {
      var result = rules.assert('g T && g F == forall {x. g x}');
      return result.justify('axiom1');
    },
    inputs: {},
    form: '',
    comment: ('T and F are all of the booleans')
  },

  axiom2: {
    action: function() {
      var result = rules.assert('x = y --> h x = h y');
      return result.justify('axiom2');
    },
    inputs: {},
    form: '',
    comment: ('Equal inputs yield equal outputs.')
  },

  axiom3: {
    action: function() {
      var result = rules.assert('(f = g) = forall {x. f x = g x}');
      return result.justify('axiom3');
    },
    inputs: {},
    form: '',
    hint: 'extensionality',
    comment: ('Extensionality: functions are equal based on equal results'
	      + ' on all inputs.')
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: {
    action: function(call) {
      call = typeof call == 'string' ? Y.parse(call) : call;
      assert(call.isOpenCall(), function() {
	return 'Axiom 4 needs ({v. B} A), got: ' + call.toString();
      });
      var lambdaExpr = call.fn;
      var result =
        equal(call, Y.subFree(call.arg, lambdaExpr.bound, lambdaExpr.body));
      // Always make sure the call has a type.  It came from elsewhere.
      Y.findType(call);
      return rules.assert(result).justify('axiom4', [call]);
    },
    inputs: {term: 1},  // Specifically a Call to a Lambda.
    form: 'Enter {v. body} expr <input name=term>',
    hint: 'apply a function to its argument',
    comment: ('')
  },

  axiom5: {
    action: function() {
      var result = rules.assert('(the (= y)) = y');
      return result.justify('axiom5');
    },
    inputs: {},
    form: '',
    comment: ('axiom of description.')
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
    comment: ('')
  },

  // Definition of F, for book-style proofs.
  defFFromBook: function() {
    return equal(F, call('forall', lambda(x, x))).justify('defFFromBook');
  },

  // Book only.
  defAnd: function() {
    var result =
      equal('&&', lambda(x, lambda(y, equal(lambda(g, call(g, T, T)),
                                            lambda(g, call(g, x, y))))));
    return result.justify('defAnd');
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
    comment: 'Derives A = A.'
  },

  
  // The two forms of "=" are interchangeable (other than precedence).
  eqIsEquiv: {
    action: function() {
      var step1 = rules.eqSelf(new Y.Var('='));
      var step2 = rules.eqSelf(new Y.Var('=='));
      var result = rules.r(step2, step1, '/right');
      return result.justify('eqIsEquiv', []);
    },
    form: '',
    comment: '"Equiv" and "equal mean the same thing."'
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
    comment: 'From A = B derives B = A'
  },

  // r5201c.  Works with hypotheses.
  eqnChain: {
    action: function(ab, bc) {
      var ac = rules.replace(bc, ab, '/main/right');
      var result = ac;
      return result.justify('eqnChain', arguments, arguments);
    },
    comment: 'From A = B and B = C derives A = C'
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
    comment: 'Given f = g, derive (f A) = (g A)'
  },

  // r5201f.  Works with hypotheses.
  applyToBoth: {
    action: function(a, h_bc) {
      var bc = h_bc.unHyp();
      var abab = rules.eqSelf(call(a, bc.getLeft()));
      var abac = rules.replace(h_bc, abab, '/right/arg');
      var result = abac;
      if (a instanceof Y.Lambda) {
        var step2 = rules.apply(abac, '/main/left');
        var result = rules.apply(step2, '/main/right');
      }
      return result.justify('applyToBoth', arguments, [h_bc]);
    },
    inputs: {term: 1, equation: 2},
    form: ('Apply function <input name=term>'
	   + ' to both sides of step <input name=equation>'),
    hint: 'from A = B to (F A) = (F B)',
    comment: 'Given B = C derives (f B) = (f C)'
  },

  // Use the definition of the given name at the given location
  // in WFF A.  If the definition is by cases the location should
  // be a call to the named function, with T or F as the argument.
  // Works with hypotheses.
  useDefinition: {
    action: function(a, path) {
      var args = [a, path];
      path = Y.path(path, a);
      var target = a.locate(path);
      if (target instanceof Y.Var) {
        var result = rules.replace(rules.definition(target.name), a, path);
        return result.justify('useDefinition', args, [a]);
      } else {
        assert(target instanceof Y.Call && target.arg instanceof Y.Var,
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
    comment: ('')
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
    // form: '',
    hint: 'Apply a function to its argument',
    comment: ('Applies a lambda to its argument')
  },

  // Derives a rewriter for a call that reduces a call to a lambda, or
  // expands the definition of a one- or two-argument function and
  // reduces resulting lambdas.  If none of these apply to the call,
  // returns null.
  applier: {
    action: function(expr) {
      var args = [expr];
      assert(expr instanceof Y.Call);
      var fn = expr.fn;
      if (fn instanceof Y.Lambda) {
        var result = rules.axiom4(expr);
        return result.justify('applier', args);
      }
      // Call that looks like (<constant> <expr>).
      if (fn.isConst()) {
        var defn = Y.findDefinition(fn.name);
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
          var defn = Y.findDefinition(fn2.name);
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
    comment: 'Equate to call with definition expanded and lambdas reduced'
  },
    

  // "Reduces" a call identified by a path within a theorem. If the
  // call is an application of a lambda expression to an argument,
  // beta-reduces it.  If the target expression is a call to a named
  // function supplying one or two arguments, expands the definition
  // and applies the expansions to the argument(s).
  apply: {
    action: function(step, path) {
      path = Y.path(path, step);
      var target = step.locate(path);
      assert(target, function() {
        return 'Path ' + path + ' not found in ' + step;
      }, step);
      var equation = rules.applier(target);
      assert(equation, function() { return 'Cannot apply at ' + target; });
      var result = rules.replace(equation, step, path);
      return result.justify('apply', [step, path], [step]);
    },
    inputs: {site: 1},
    form: '',
    hint: 'Apply a function to its argument',
    comment: ('Applies a function, named or not, to one or two arguments')
  },

  /**
   * Change the name of a bound variable.  Replaces the lambda
   * subexpression in expr at path with one that binds newName, which
   * may be a string or Var, and uses it in place of any references to
   * the old bound variable.
   */
  changeVar: {
    action: function(expr, path, newVar) {
      newVar = _var(newVar);
      path = Y.path(path, expr);
      var target = expr.locate(path);
      assert(target instanceof Y.Lambda, 'Not a function: ' + target, expr);
      assert(!expr.freeNames()[newVar.name],
             'New bound variable ' + newVar.name + ' must not occur free.',
             expr);
      var changed = lambda(newVar,
                           Y.subFree(newVar, target.bound, target.body));
      var step1 = rules.eqSelf(changed);
      var step2 = rules.r(step1, expr, path);
      return step2.justify('changeVar', arguments, [expr]);
    },
    inputs: {bindingSite: 1, varName: 3},
    form: ('Rename to <input name=varName>'),
    hint: 'rename bound variable',
    comment: ('Change the name of a bound variable.  The new name '
              + 'must not occur free in the target expression.  '
              + 'Uses the fact that the original expression matches '
              + 'the one with changed bound variable.')
  },

  /**
   * From an equation, infers a similar equation with each
   * side wrapped in a binding of the given variable or variable name.
   */
  bindEqn: {
    action: function(h_eqn, v) {
      v = Y.varify(v);
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
              + ' using the bound variable of your choice.')
  },

  /**
   * Substitutes term "a" for variable "v" in equation b_c,
   * with the result a consequence of b_c.  (5209)
   * Does not support hypotheses.
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
    comment: ('Instantiates a free variable in an equation.')
  },

  eqTLemma: {
    action: function() {
      var a3 =
        rules.useDefinition(rules.axiom('axiom3'), '/right/fn');
      var identity = lambda(y, y);
      var step1a = rules.instEqn(a3, identity, f);
      var step1b = rules.instEqn(step1a, identity, g);
      var step2a = rules.eqSelf(identity);
      // Eliminate the LHS of step2a:
      var step2b = rules.r(step1b, step2a, '/');
      var step2c = rules.apply(step2b, '/right/body/left');
      var step2d = rules.apply(step2c, '/right/body/right');
      return step2d.justify('eqTLemma', arguments);
    }
  },

  // T = [B = B] (5210)
  eqT: {
    action: function(b) {
      var lemma = rules.theorem('eqTLemma');
      var step1 = rules.applyBoth(lemma, b);
      var step2 = rules.apply(step1, '/left');
      var step3 = rules.apply(step2, '/right');
      return step3.justify('eqT', arguments, []);
    },
    inputs: {term: 1},
    form: ('Term to prove equal to itself: <input name=term>'),
    hint: '(T = (A = A))',
    comment: ('Proves T = [B = B].')
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
      assert(target.fn instanceof Y.Var && target.fn.name == 'forall',
             "Must be 'forall': " + target.fn,
             h_target);
      assert(target.arg instanceof Y.Lambda,
             "Must be lambda expression: " + target.arg,
             h_target);
      var step1 = rules.useDefinition(h_target, '/main/fn');
      var step2 = rules.applyBoth(step1, expr);
      var step3 = rules.apply(step2, '/main/left');
      var step4 = rules.apply(step3, '/main/right');
      // Do not use fromTIsA, it depends on this.
      var step5 = rules.replace(step4, rules.theorem('t'), '/main');
      return step5.justify('instForall', arguments, [h_target]);
    },
    inputs: {step: 1, term: 2, condition: {1: function(target) {
      return (target instanceof Y.Call
	      && target.fn instanceof Y.Var
	      && target.fn.name == 'forall');
    }}},
    form: ('In step <input name=step> instantiate bound var'
	   + ' with term <input name=term>'),
    hint: 'instantiate "forall"',
    comment: ('In a "forall", instantiates the bound variable with'
              + ' a given term.')
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
    comment: ('From [A = B] deduce T = [A = B].')
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
      // that [A --> F] --> not A, a tautology.
      var step4 = rules.toTIsA(step3c);
      // We are going to prove the cases of: (x --> F) = (x = F)
      // First with x = F.
      var step11 = rules.definition('-->', F);
      var step12 = rules.applyBoth(step11, F);
      var step13 = rules.apply(step12, '/right');
      var step14 = rules.r(step3aa, step13, '/right');
      // Then with x = T.
      var step21 = rules.definition('-->', T);
      var step22 = rules.applyBoth(step21, F);
      var step23 = rules.apply(step22, '/right');
      var step24 = rules.r5230TF();
      var step25 = rules.rRight(step24, step23, '/right');
      // Now use the cases rule:
      var step5 = rules.equationCases(step25, step14, x);
      // Then instantiate [F = T] for x.
      var step6 = rules.instVar(step5, equal(F, T), x);
      // And use the fact that [F = T] --> F
      var step7 = rules.rRight(step4, step6, '/left');
      var step8 = rules.fromTIsA(step7);
      return step8.justify('r5230FT_alternate');
    },
    comment: ('[F = T] = F')
  },

  // [T && T] = T.  Uses no book-specific definitions.
  // Only used in 5212 and book version of 5216.
  r5211: function() {
    var step1 = rules.definition('&&', T);
    var step2 = rules.applyBoth(step1, T);
    var step3 = rules.apply(step2, '/right');
    return step3.justify('r5211');
  },

  // Book version of r5211.
  r5211Book: function() {
    var step1 = rules.instEqn(rules.axiom('axiom1'), lambda(y, T), g);
    var step2a = rules.apply(step1, '/left/left');
    var step2b = rules.apply(step2a, '/left/right');
    var step2c = rules.apply(step2b, '/right/arg/body');
    var step3a = rules.eqT(lambda(x, T));
    var step3b = rules.rRight(rules.definition('forall'), step3a, '/right/fn');
    var step4 = rules.rRight(step3b, step2c, '/right');
    return step4.justify('r5211Book');
  },

  // T && T.  Uses no book-specific definitions.
  // Used to prove equationCases.  The "cases" rule
  // and makeConjunction could treat this as a tautology.
  r5212: function() {
    var step1 = rules.rRight(rules.theorem('r5211'),
                             rules.theorem('t'),
                             '/');
    return step1.justify('r5212');
  },

  // From theorems A = B and C = D, derives theorem
  // [A = B] && [C = D].  Uses no book-specific definitions.
  // Not used (because 5216 is not used.)
  // Use toTIsEquation there instead of this.
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

  // 5216 by the book.  Not used.  Currently uses one nonbook definition.
  andTBook: function(a) {
    var step1 = rules.axiom('axiom1');
    var step2 =
      rules.instEqn(step1, lambda(x, equal(call('&&', T, x), x)), g);
    var step3 = rules.apply(step2, '/left/left');
    var step4 = rules.apply(step3, '/left/right');
    var step5 = rules.apply(step4, '/right/arg/body');
    var step6 = rules.applyBoth(rules.definition('&&', T), F);
    var step7 = rules.apply(step6, '/right');
    var step8 = rules.r5213(rules.theorem('r5211'), step7);
    var step9 = rules.r(step5, step8, '/');
    var step10 = rules.instForall(step9, a);
    return step10.justify('andTBook', arguments);
  },

  // 5216, using the definition of "true and".  Not used.
  andT: function(a) {
    var step1 = rules.applyBoth(rules.definition('&&', T), a);
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
      v = _var(v);
      var stepT1 = rules.toTIsEquation(caseT);
      var stepF1 = rules.toTIsEquation(caseF);
      var step2 = rules.replace(stepT1, rules.theorem('r5212'), '/left');
      var step3 = rules.replace(stepF1, step2, '/right');
      // Note: If a variable is not in caseT it is also not in caseF.
      var newVar = Y.genVar('w', caseT.allNames());
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
      var step1 = rules.theorem('r5230TF');
      var step2 = rules.eqT(T);
      var step3 = rules.eqnSwap(step2);
      var step4 = rules.equationCases(step3, step1, 'x');
      return step4.justify('tIsXIsX');
    },
    comment: ('[T = x] = x')
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
    comment: ('For any expression A derives [T = A] = A.')
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
    comment: ('From A derives T = A')
  },

  // also 5219.  Works with hypotheses.
  fromTIsA: {
    action: function(h_t_a) {
      var t_a = h_t_a.unHyp()
      assertEqn(t_a);
      var left = t_a.locate('/left');
      assert(left instanceof Y.Var && left.name == 'T',
             'Input should be [T = A]: ' + t_a,
             h_t_a);
      var a = t_a.locate('/right');
      var result = rules.replace(rules.r5218(a), h_t_a, '/main');
      return result.justify('fromTIsA', arguments, [h_t_a]);
    },
    inputs: {equation: 1, condition: {1: function(h_eqn) {
      var eqn = h_eqn.unHyp();
      var left = eqn.getLeft();
      return (left instanceof Y.Var && left.name == 'T');
    }}},
    form: 'Eliminate "T = " from step <input name=equation>',
    hint: 'from (T = A) to A',
    comment: ('From T = A derives A')
  },

  // Lemma helper for forallT, a pure theorem.
  // proved here by extensionality, not using 5206.
  forallVT: {
    action: function() {
      var step1 = rules.instEqn(rules.axiom('axiom3'), lambda(x, T), f);
      var step2 = rules.instEqn(step1, lambda(_var('v'), T), g);
      var step3 = rules.apply(step2, '/right/arg/body/left');
      var step4 = rules.apply(step3, '/right/arg/body/right');
      var step5 = rules.useDefinition(step4, '/right/fn');
      var step6 = rules.bindEqn(rules.eqT(T), x);
      var step7 = rules.rRight(step5, step6, '/');
      var fa = rules.definition('forall');
      var result = rules.rRight(fa, step7, '/fn');
      return result.justify('forallVT', arguments);
    },
    comment: ('(forall {v | T})')
  },

  // Helper for addForall
  // Derives (forall {v. T}) given a variable v.
  forallT: {
    action: function(v) {
      var step1 = rules.theorem('forallVT');
      var step2 = rules.changeVar(step1, '/arg', _var(v));
      return step2.justify('forallT', arguments);
    },
    inputs: {varName: 1},
    form: 'Variable to bind: <input name=varName>',
    comment: ('(forall {v. T})')
  },

  // 5220 (universal generalization).  From A deduces forall {v. A}.
  // The variable v may be given as a string, which it converts
  // internally to a variable.  Supports hypotheses.
  addForall: {
    action: function(h_a, v) {
      v = _var(v);
      assert(!(h_a.hasHyps && h_a.getLeft().hasFree(v.name)),
	     function() {
	       return v.name + ' occurs free in hypotheses of ' + h_a;
	     },
             h_a);
      var step1 = rules.toTIsA(h_a);
      var step2 = rules.forallT(v);
      var step3 = rules.replace(step1, step2, '/arg/body');
      return step3.justify('addForall', arguments, [h_a]);
    },
    inputs: {step: 1, varName: 2},
    form: ('In step <input name=step> generalize on variable '
           + '<input name=varName>'),
    hint: 'from A to (forall {x. A})',
    comment: ('Universal Generalization, wrap a theorem A in'
              + ' (forall v A) using the variable of your choice.')
  },

  // 5221 (one variable), in the given step substitute term A for
  // variable v, which may also be a string, which will be converted
  // to a variable.  Handles hypotheses, allowing substitution for a
  // variable even if free in the hypotheses.
  instVar: {
    action: function(step, a, v) {
      v = Y.varify(v);
      var map = {};
      map[v.name] = a;
      var result = rules.instMultiVars(step, map);
      return result.justify('instVar', arguments, [step]);
    },
    inputs: {step: 1, term: 2, varName: 3},
    form: ('In step <input name=step>, for variable <input name=varName> '
           + 'substitute <input name=term>'),
    hint: 'substitute for free variable',
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.')
  },

  // Same functionality as instVar, but with a site (step+path) and a
  // term as the arguments.
  instantiateVar: {
    action: function(step, path, term) {
      v = step.locate(path);
      assert(v instanceof Y.Var, 'Not a variable: ' + v);
      var map = {};
      map[v.name] = term;
      var result = rules.instMultiVars(step, map);
      return result.justify('instantiateVar', arguments, [step]);
    },
    inputs: {site: 1, term: 3},
    form: ('Substitute <input name=term> for the selected variable.'),
    hint: 'substitute for free variable',
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.')
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
      Y.Array.each(namesReversed, function(name) {
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
    hint: 'Substitute for multiple variables',
    comment: ('Substitute in B for each variable named in the map, '
              + 'its value in the map')
  },

  // Given two theorems a and b, proves a && b.
  // Handles hypotheses.
  // TODO: Move before "cases".
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
    hint: 'from A and B to (A && B)',
    comment: ('Given a and b, derive a && b')
  },

  // (5222) Given two theorems that are substitutions of T and
  // F respectively into a WFF; and a variable or variable name,
  // proves the WFF.  Works with hypotheses.
  cases: {
    action: function(caseT, caseF, v) {
      v = _var(v);
      // Note: caseF has no variables not in caseT, so no need to
      // calculate all of its names.
      var newVar = Y.genVar('v', caseT.allNames());
      var gen = caseT.unHyp().generalizeTF(caseF.unHyp(), newVar);
      var step1a = rules.axiom4(call(lambda(newVar, gen), T));
      var step1b = rules.rRight(step1a, caseT, '/main');
      var step2a = rules.axiom4(call(lambda(newVar, gen), F));
      var step2b = rules.rRight(step2a, caseF, '/main');
      var step4 = rules.makeConjunction(step1b, step2b);
      var step5 = rules.instVar(rules.axiom1(), lambda(newVar, gen), g);
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
              + ' show it with T and F.')
  },

  // Given P and P --> Q, derive Q. (5224)
  // Handles hypotheses.
  modusPonens: {
    action: function(a, b) {
      var step1 = rules.toTIsA(a);
      // Replace the "a" in "b" with T.
      var step2 = rules.rRight(step1, b, '/main/left');
      // Use the definition of -->.
      var step3 = rules.useDefinition(step2, '/main/fn');
      // From T --> x derive x.
      var step4 = rules.apply(step3, '/main');
      return step4.justify('modusPonens', arguments, arguments);
    },
    inputs: {step: 1, implication: 2},
    form: ('Modus ponens: hypothesis step <input name=step>,'
	   + ' implication in step <input name=implication>'),
    hint: 'modus ponens',
    comment: ('Modus Ponens.  Given A and A --> B derives B.')
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
    },
    comment: ('[not F] = T')
  },

  // Helper for evalBool, not in book.
  // [[F =] = not].
  falseEquals: {
    action: function() {
      return rules.eqnSwap(rules.definition('not')).justify('falseEquals');
    },
    comment: ('[F =] = not')
  },

  // Another helper for evalBool, not in book.
  // [[T =] = {x. x}].
  trueEquals: {
    action: function() {
      var step1 = rules.r5218(x);
      var step2 = rules.eqSelf(Y.parse('{x. x} x'));
      var step3 = rules.apply(step2, '/left');
      var step4 = rules.r(step3, step1, '/right');
      var step5 = rules.addForall(step4, x);
      var step6 = rules.instVar(rules.axiom('axiom3'), equal(T), f);
      var step7 = rules.instVar(step6, lambda(x, x), g);
      var step8 = rules.rRight(step7, step5, '');
      return step8.justify('trueEquals', arguments);
    },
    comment: ('[T =] = {x. x}')
  },

  // Equates the given expression to a similar one where boolean terms
  // are reduced.  (These are calls to =, &&, ||, -->, or "not", and
  // lambda expressions, with an argument of T or F.)  Reduces
  // repeatedly until no subexpression can be reduced.
  // TODO: Prove all the truth table facts and use them directly
  // here.  Can we have unnamed theorems?
  evalBool: {
    action: function(expr) {
      var boolOps = {'&&': true, '||': true, '-->': true, '=': true, not: true};
      function isReducible(expr) {
        return (expr instanceof Y.Call
                && ((expr.fn instanceof Y.Var
                     && boolOps[expr.fn.name]
                     && expr.arg instanceof Y.Var
                     && (expr.arg.name == 'T' || expr.arg.name == 'F'))
                    || expr.fn instanceof Y.Lambda));
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
        if (fn instanceof Y.Var) {
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
            // &&, ||, -->
            result = rules.useDefinition(result, '/right' + _path);
          }
        } else if (fn instanceof Y.Lambda) {
          result = rules.apply(result, '/right' + _path);
        } else {
          assert(false, 'Unexpected expression: ' + target);
        }
      }
    },
    inputs: {term: 1},
    form: 'Boolean term to simplify: <input name=term>',
    comment: ('Evaluates a boolean expression with no free variables.')
  },

  // Proves an inference that the wff is a tautology and
  // returns it.  Checks that it is indeed proven to be a
  // tautology.  (5233)
  //
  // Accepts a parseable string as the wff.
  tautology: {
    action: function(wff) {
      if (typeof wff == 'string') {
        wff = Y.parse(wff);
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
          if (Y.isVariable(name)) {
            if (wff instanceof Y.Call && wff.fn instanceof Y.Call
                && wff.fn.fn instanceof Y.Var && wff.fn.fn.name == '=') {
              // WFF is already an equation.
              var step1 = rules.tautology(Y.subFree(T, name, wff));
              var step2 = rules.tautology(Y.subFree(F, name, wff));
              var step3 = rules.equationCases(step1, step2, name);
              var result = step3.justify('tautology', arguments);
              _tautologies[key] = result;
              return result.justify('tautology', arguments);
            } else {
              var step1 = rules.tautology(equal(T, Y.subFree(T, name, wff)));
              var step2 = rules.tautology(equal(T, Y.subFree(F, name, wff)));
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
               && step11.getRight() instanceof Y.Var
               && step11.getRight().name == 'T',
               'Not a tautology: ' + step11.getLeft(),
               step11);
        var step12 = rules.rRight(step11, rules.t(), '');
        var result = step12.justify('tautology', arguments);
        _tautologies[key] = result;
        return result;
      }
    },
    inputs: {term: 1},
    form: 'Enter tautology: <input name=term>',
    hint: 'enter tautology',
    comment: ('Tautology decider.')
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
        h_tautology = Y.parse(h_tautology);
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
    comment: ('A substitution instance of a tautology is a theorem.')
  },

  // TODO: Complete this.
  simplifyBool: {
    action: function(term) {
      if (term.findSubst('not x')) {
        if (term.arg.isBoolConst()) {
          var name = term.arg.name;
          if (name == 'T') {
            return Y.tautology('not T = F');
          } else {
            return Y.tautology('not F = F');
          }
        }
      }
      var simplifiers = {
        '&&': {
          T: {
            T: 'T && T == T',
            F: 'T && F == F'
          },
          F: {
            T: 'F && T == F',
            F: 'F && F == F'
          }
        },
        '||': {
            T: 'T || T == T',
            F: 'T || F == T'
          },
          F: {
            T: 'F || T == T',
            F: 'F || F == F'
          },
        '-->': {
            T: 'T --> T == T',
            F: 'T --> F == F'
          },
          F: {
            T: 'F --> T == T',
            F: 'F --> F == T'
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
      var boolOps = {'=': true, '&&': true, '||': true, '-->': true};
      var op = term.getBinOp().name;
      if (term.isInfixCall() && boolOps.hasOwnProperty(op)) {
        var left = term.getLeft();
        var right = term.getRight();
        if (left.isBoolConst() && right.isBoolConst()) {
          return Y.tautology(simplifiers[op][left.name][right.name]);
        } else if (left.isBoolConst()) {
          return Y.tautology(leftSimplifiers[op][left.name]);
        } else {
          return Y.tautology(rightSimplifiers[op][right.name]);
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
      var step2 = rules.tautInst(Y.parse('p --> T'), {p: any});
      var step3 = rules.r(step1, step2, '/right');
      return step3.justify('anyImpliesTheorem', arguments, [theorem]);
    },
    inputs: {term: 1, step: 2},
    form: ('Derive that <input name=term> implies theorem <input name=step>'),
    hint: 'From theorem B deduce A --> B',
    comment: ('Given a theorem, derive that something implies it.')
  },

  // Given a variable v that is not free in the given wff A, and a wff B, derive
  // ((forall {v. A || B}) --> A || (forall {v. B})).  Could run even if
  // the variable is free, but would not give desired result.
  // This is Axiom Schema 5 of Andrews' first-order logic F.
  r5235: {
    action: function(v, a, b) {
      v = Y.varify(v);
      var aFree = a.freeNames();
      assert(!aFree.hasOwnProperty(v.name),
	     'r5235: variable ' + v + 'cannot occur free in ' + a);
      var map1 = {
        p: call('forall', lambda(v, call('||', T, b))),
        q: call('forall', lambda(v, b))
      };
      var step1 = rules.tautInst(implies(p, call('||', T, q)), map1);
      var step2 = rules.tautInst(implies(p, call('||', F, p)),
                                 ({p: call('forall', lambda(v, b))}));
      var step3 = rules.tautInst(equal(p, call('||', F, p)),
                                 ({p: b}));
      var step4 = rules.r(step3, step2, '/left/arg/body');

      var freeNames = Y.merge(aFree, b.freeNames());
      // Treat v as a free variable also.
      freeNames[v.name] = true;
      var p0 = Y.genVar('p', freeNames);
      var step5 = rules.cases(step1, step4, p0);
      var step6 = rules.instVar(step5, a, p0);
      return step6.justify('r5235', arguments);
    },
    inputs: {varName: 1, term: [2, 3]},
    form: ('Variable: <input name=varName> '
	   + 'wff without it free: <input name=term1> '
	   + 'other wff: <input name=term2>'),
    comment: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".')
  },

  // Given a proof step H |- A --> B and a variable v, derives
  // H |- (A --> forall {v. B}) provided that v is not free in A or H.
  // (5237)  This version implemented via 5235, so much less efficient.
  //
  // Handles hypotheses.
  implyForallBook: {
    action: function(v, h_a_b) {
      var a_b = h_a_b.unHyp();
      v = Y.varify(v);
      assert(a_b.isCall2('-->'), 'Must be an implication: ' + a_b, h_a_b);
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
      var step1 = rules.tautInst(Y.parse('(a --> b) --> not a || b'), map1);
      var step2 = rules.modusPonens(h_a_b, step1);
      var step3 = rules.addForall(step2, v);
      var step4 = rules.r5235(v, call('not', a), b);
      var step5 = rules.modusPonens(step3, step4);
      var map6 = {a: a, b: step5.locate('/main/right')};
      var step6 = rules.tautInst(Y.parse('not a || b --> (a --> b)'), map6);
      var step7 = rules.modusPonens(step5, step6);
      return step7.justify('implyForallBook', arguments, [h_a_b]);
    },
    inputs: {varName: 1, implication: 2},
    form: ('Move forall inside "implies" binding '
	   + 'variable <input name=varName> '
	   + 'implication <input name=implication>'),
    comment: ('Move "forall" inside "implies" provided the variable '
              + 'is not free in the first argument.')
  },

  // Given a variable v that is not free in the given wff A, and a wff B, derive
  // ((forall {v. A --> B}) --> (A --> forall {v. B})).  Could run even if
  // the variable is free, but would not give desired result.
  implyForallThm: {
    action: function(v, a, b) {
      v = Y.varify(v);
      var aFree = a.freeNames();
      assert(!aFree.hasOwnProperty(v.name),
	     'r5235: variable ' + v + 'cannot occur free in ' + a);
      var map1 = {
        p: call('forall', lambda(v, Y.infixCall(F, '-->', b))),
        q: call('forall', lambda(v, b))
      };
      var step1 = rules.tautInst(implies(p, Y.infixCall(F, '-->', q)), map1);
      var step2 = rules.tautInst(implies(p, Y.infixCall(T, '-->', p)),
                                 ({p: call('forall', lambda(v, b))}));
      var step3 = rules.tautInst(equal(p, Y.infixCall(T, '-->', p)),
                                 ({p: b}));
      var step4 = rules.r(step3, step2, '/left/arg/body');

      var freeNames = Y.merge(aFree, b.freeNames());
      // Treat v as a free variable also.
      freeNames[v.name] = true;
      var p0 = Y.genVar('p', freeNames);
      var step5 = rules.cases(step4, step1, p0);
      var step6 = rules.instVar(step5, a, p0);
      return step6.justify('implyForallThm', arguments);
    },
    inputs: {varName: 1, term: [2, 3]},
    form: ('Variable: <input name=varName> '
	   + 'wff without it free: <input name=term1> '
	   + 'other wff: <input name=term2>'),
    hint: 'forall {v. A --> B} --> (A --> forall {v. B}',
    comment: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".')
  },

  // Given a proof step H |- A --> B and a variable v, derives
  // H |- (A --> forall {v. B}) provided that v is not free in A or H.
  // (5237)  Implemented via implyForallThm.
  //
  // Handles hypotheses.
  implyForall: {
    action: function(v, h_a_b) {
      v = Y.varify(v);
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
              + 'is not free in the first argument.')
  },
    
  // Rule P for a single antecedent (5234).  The given tautology must
  // have the form (A --> B), where A matches the given input step and
  // B has only variables that appear in A.  For tautologies with a
  // conjunction on the LHS as shown in the book, use this with
  // makeConjunction.  Handles hypotheses by applying modus ponens to
  // the step.
  //
  // Accepts a string for the tautology.
  forwardChain: {
    action: function(step, tautology) {
      var tautology = rules.tautology(tautology);
      var substitution = Y.matchAsSchema(tautology.getLeft(), step.unHyp());
      var step2 = rules.instMultiVars(tautology, substitution);
      var step3 = rules.modusPonens(step, step2);
      return step3.justify('forwardChain', arguments, [step]);
    },
    inputs: {step: 1, term: 2},
    form: ('Match step <input name=step> with left side of implication '
           + 'in tautology <input name=term>'),
    comment: ('Match step with LHS of tautology A --> B.')
  },

  // Andrews calls his enhanced version of forward chaining "Rule P".
  // (In this implementation it is more straightforward to use
  // makeConjunction as needed, followed by forwardChain.)
  // 
  // TODO: Consider renaming all uses of this to "forwardChain".
  p: {
    action: function(step, tautology) {
      return (rules.forwardChain(step, tautology)
              .justify('p', arguments, [step]));
    },
    inputs: {step: 1, term: 2},
    form: ('Match step <input name=step> with left side of implication '
           + 'in tautology <input name=term>'),
    comment: ('Match step with LHS of tautology A --> B.')
  },

  // Proves the goal by matching it with the conclusion of the given
  // theorem and then applying the given inference rule to prove the
  // premise of the instantiated theorem.  The theorem must be an
  // implication.
  //
  // TODO: Test me.
  backwardChain: {
    action: function(goal, theorem, rule) {
      theorem.assertCall2('-->');
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
  // theorem, which must be a schema of the form a --> b.
  // Instantiates the theorem by matching the goal against the theorem
  // RHS, returning the instantiated theorem.
  subgoal: {
    action: function(goal, theorem) {
      theorem.assertCall2('-->');
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
        var v = vars[vars.length - 1];
        if (typeof v == 'string') {
          v = _var(v);
        }
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
      if (typeof v == 'string') {
        v = _var(v);
      }
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
  // a wff of the form "forall ... (A = B) --> (C = D), where D is
  // obtained like the result of applying Rule R to A = B and C.  The
  // "forall" binds free variables of A = B that are bound at the
  // replacement location in C.
  r5239: {
    action: function(equation, target, path) {
      path = Y.path(path);
      assert(equation.isCall2('='),
             'Expecting an equation, got: ' + equation,
	     equation);
      var step1 = rules.axiom('axiom2');
      var a = equation.getLeft();
      var b = equation.getRight();
      var boundNames = target.boundNames(path);
      Y.removeExcept(boundNames, equation.freeNames());
      // Is this the full set of names?
      var t = Y.genVar('t', Y.merge(target.allNames(), equation.allNames()));
      var texpr = t;
      for (var name in boundNames) {
        texpr = call(texpr, _var(name));
      }
      var aBound = a;
      var bBound = b;
      var boundNameList = [];
      for (var name in boundNames) {
        var v = _var(name);
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
        step4 = rules.apply(step4, Y.path('/right/left').concat(path));
      }
      var step5 = rules.apply(step4, '/right/right');
      var step6 = step5;
      for (var i = 0; i < boundNameList.length; i++) {
        step6 = rules.apply(step6, Y.path('/right/right').concat(path));
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
  // h_equation is an equation implied by hypotheses, i.e. H --> A = B.
  // h_c is a term implied by the same hypotheses, i.e. H --> C.
  // The path is relative to h_c, and may include a special initial
  // segment 'main', which it interprets as 'right' if h_c has
  // hypotheses, otherwise ignoring it.
  //
  // For convenience applies rule R directly if the equation is really
  // an equation and not an implication.
  replace: {
    action: function(h_equation_arg, h_c_arg, path) {
      var args = [h_equation_arg, h_c_arg, path];
      path = Y.path(path, h_c_arg);
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
      assert(h_equation.isCall2('-->') && h_equation.getRight().isCall2('='),
	     'Not an equation: ' + h_equation, h_equation_arg);
      // h_equation has the form H --> A = B

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
      Y.removeExcept(boundNames, equation.freeNames());
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
      var tautology = Y.parse('(p --> q) && (q --> r) --> (p --> r)');
      var step4 = rules.p(step3, tautology);
      var step5 = rules.makeConjunction(h_c, step4);
      var taut2 = Y.parse('(h --> p) && (h --> (p = q)) --> (h --> q)');
      var result = rules.p(step5, taut2);
      if (h_c_arg.hasHyps || h_equation_arg.hasHyps) {
        result = rules.asHypotheses(result);
      }
      return result.justify('replace', args, [h_equation_arg, h_c_arg]);
    },
    inputs: {step: 1, site: 2}, // plus constraints.
    form: ('Replace selection with right side of step <input name=step>'),
    comment: ("Replace an expression with the right side of an equation, "
              + "handling hypotheses.")
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
	  var taut = Y.parse('(h1 --> p) --> ((h1 && h2) --> p)');
	  var subst = {
	    h1: step.getLeft(),
	    h2: hypStep.getLeft(),
	    p: step.getRight()
	  };
	  var step1 = rules.tautInst(taut, subst);
	  var step2 = rules.modusPonens(step, step1);
	  // Simplify (h1 && h2) --> p
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
	  var step1 = rules.tautInst(Y.parse('p --> (h2 --> p)'), subst);
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
    hint: 'Add hypotheses to a step'
  },

  // Prefix hypotheses from the hypStep to the target step.  Often
  // used together with appendStepHyps.  If hypStep has no hypotheses,
  // the result is simply the given step.
  //
  // TODO: Combine this and appendStepHyps into one rule.  Consider a
  //   rule that derives (H --> step1rhs) && (H --> step2rhs) from
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
	  var taut = Y.parse('(h2 --> p) --> ((h1 && h2) --> p)');
	  var subst = {
	    h1: hypStep.getLeft(),
	    h2: step.getLeft(),
	    p: step.getRight()
	  };
	  var step1 = rules.tautInst(taut, subst);
	  var step2 = rules.modusPonens(step, step1);
	  // Simplify (h1 && h2) --> p
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
	  var step1 = rules.tautInst(Y.parse('p --> (h1 --> p)'), subst);
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
    hint: 'Prefix hypotheses to a step'
  },

  // Takes a proof step, a path, and a proved equation without
  // variable bindings.  If the part of the step at the given path
  // matches the LHS of the equation, replaces that part of the step
  // with the appropriate instance of the equation, otherwise return
  // the input step.  The step and equation may have hypotheses.
  rewrite: {
    action: function(step, path, equation) {
      var expr = step.locate(path);
      var map = expr.findSubst(equation.unHyp().getLeft());
      assert(map, function() {
          return 'Cannot rewrite\n' + step + '\nusing ' + equation;
        });
      var step1 = rules.instMultiVars(equation, map);
      var result = rules.replace(step1, step, path);
      return result.justify('rewrite', arguments, [step, equation]);
    },
    inputs: {site: 1, equation: 3},
    form: ('Rewrite the site using equation <input name=equation>'),
    hint: 'Instantiate an equation so its LHS equals an expression.'
  },

  // NOTE: A chain of conjuncts (or other binary operator) is an
  // expression that can be written a && b && ... && z.  An expression
  // that does not have the operator at top-level is a chain of one
  // conjunct.  A chain of two elements is of the form a && b, where a
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
        // expr is a && b
	if (a.isCall2('&&')) {
          // expr is a && b && c
	  var c = b;
	  b = a.getRight();
	  a = a.getLeft();
	  // Eqn is lhs = (a && b) && c
	  if (b.matches(c)) {
            // RHS is a && b && b
	    var simpler =
              rules.rewrite(eqn, '/right',
                            rules.tautology('a && b && b == a && b'));
	    // Keep bubbling the rightmost to the left.
	    return bubble(simpler);
	  } else if (less(c, b)) {
            // Replace the equation's RHS according using associativity.
            var assoc = rules.tautology('a && b && c == a && c && b');
            var map = expr.findSubst(assoc.getLeft());
            var assocInstance = rules.instMultiVars(assoc, map);
	    var step1 = rules.r(assocInstance, eqn, '/right');
	    // Then recursively bubble the C in A && C to its proper place.
	    var step2 = rules.bubbleLeft(step1.locate('/right/left'), less);
	    // Replace the A && C in RHS of step1 with the result.
	    var step3 = rules.r(step2, step1, '/right/left');
            // and replace the RHS of the argument with the final esult.
	    return rules.r(step3, eqn, '/right');
	  } else {
	    // C is in place.
	    return eqn;
	  }
	} else {
	  // Base case: Eqn is lhs = a && b.
	  if (a.matches(b)) {
	    return rules.rewrite(eqn, '/right',
                                 rules.tautology('a && a == a'));
	  } else if (less(b, a)) {
	    return rules.rewrite(eqn, '/right',
                                 rules.tautology('a && b == b && a'));
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
      expr.assertCall2('&&');
      var mover = (expr.getLeft().isCall2('&&')
                   ? rules.tautology('(a && b) && c == a && (c && b)')
                   : rules.tautology('a && b == b && a'));
      var result = rules.rewrite(eqn, '/right', mover);
      return result.justify('mergeRight', arguments, [eqn]);
    },
  },

  // Internal rule for mergeConjunctions, with a comparator parameter.
  mergeConj: {
    action: function(expr, less) {
      expr.assertCall2('&&');
      var eqn = rules.eqSelf(expr);
      while (eqn.getRight().getLeft().isCall2('&&')) {
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
      var result = rules.mergeConj(expr, Y.sourceStepLess);
      return result.justify('mergeConjunctions', arguments);
    },
    inputs: {term: 1},
    // Too technical to expose for most users.
    // form: ('Chains of conjunctions to merge: <input name=term>'),
    hint: 'Derives an equation to merge chains of input conjunctions'
  },    

  // Simplify the hypotheses of a step, removing duplicates.
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
      if (hyps.isCall2('&&')) {
	
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
    // combine it with ones resembling (h && h1) = (h && h1 && h) to
    // piece together larger tautologies.
    action: function(step, hyp) {
      var infix = Y.infixCall;
      assert(step.hasHyps, 'Step has no hypotheses');
      var lhs = step.getLeft().hypLocater(hyp);
      var a = Y.varify('a');
      var taut = infix(infix(lhs, '-->', a),
		       '-->',
		       infix(lhs,
			     '-->',
			     infix(Y.varify('h'), '-->', a)));
      var step1 = rules.asImplication(step);
      var step2 = rules.p(step1, taut);
      var result = rules.asHypotheses(step2);
      return result.justify('extractHypothesis', arguments, [step]);
    },
    inputs: {step: 1, term: 2},
    form: ('Extract hypothesis <input name=term> from step <input name=step>'),
    comment: 'Find and extract a hypothesis from a step.'
  },

  // Given a proof step that is an implication and a path expected to
  // refer to an element of the LHS conjunction chain, derives a step
  // of the form e --> (h' --> c) where e is the referenced element,
  // h' is the proof step's hypotheses excluding occurrences of "e",
  // and c is the impliction RHS.  Useful for simplifying hypotheses.
  isolateCondition: {
    action: function(step, path) {
      assert(step.isCall2('-->') && !step.hasHyps, 'Not an implication');
      var taut = rules.tautology(step.getLeft().hypMover(step.locate(path)));
      var step1 = rules.rewrite(step, '/left', taut);
      var taut2 = rules.tautology('a && b --> c == b --> (a --> c)');
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
      var infix = Y.infixCall;
      var tautFX = rules.tautology('F && x == F');
      // Prove that "hyps = F", where hyps is a chain of conjuncts.
      // One conjunct must be "F".
      function falsify(hyps) {
        if (hyps.isCall2('&&')) {
          if (hyps.getRight().matches(F)) {
            return rules.tautInst('p && F == F', {p: hyps.getLeft()});
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
      var map = new Y.TermMap();
      conjuncts.eachHyp(function (h) { map.addTerm(h); });
      assert(map.has(c), function() {
          return 'Must be one of the conjuncts: ' + c;
        });
      var cVar = map.get(c);
      // Make a schema for the desired theorem.
      var goalSchema = infix(buildHypSchema(conjuncts, map), '-->', cVar);
      // Make a version of the theorem with T for "c".
      var trueGoal = goalSchema.subFree(T, cVar);
      // This is a simple tautology:
      var trueCase = rules.tautInst('p --> T', {p: trueGoal.getLeft()});
      // Make a version of the theorem with F for "c".
      var falseGoal = goalSchema.subFree(F, cVar);
      // Prove that its LHS is equal to F.
      var step1 = falsify(falseGoal.getLeft());
      // This means the LHS implies F, which is the desired F case.
      var falseCase = rules.forwardChain(step1, 'p = F --> (p --> F)');
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
      var map = new Y.TermMap();
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
      Y.each(keepTermsInfo, function(info) {
          keepTerms.push(new Y.Var(info.name));
        });
      // A variable for each hypothesis to keep, in order.
      function buildConj(list) {
        var result = null;
        for (var i = 0; i < list.length; i++) {
          var term = list[i];
          result = result ? Y.infixCall(result, '&&', term) : term;
        }
        return result || T;
      }
      var rewriter =
        Y.infixCall(buildConj(allTerms), '=', buildConj(keepTerms));
      var result = rules.instMultiVars(rules.tautology(rewriter), map.subst);
      return result.justify('conjunctionDeduper', arguments);
    }
  },

  // Derives a step with hypotheses deduplicated and ordered as by
  // sourceStepComparator, including removal of occurrences of T.
  // Works with hypotheses and with plain implications.
  dedupeHyps: {
    action: function(step) {
      step.assertCall2('-->');
      var deduper =
        rules.conjunctionDeduper(step.getLeft(), Y.sourceStepComparator);
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
      var termMap = new Y.TermMap();
      var lhs = buildHypSchema(equation.getLeft(), termMap);
      var rhs = buildHypSchema(equation.getRight(), termMap);
      var taut = rules.tautology(Y.infixCall(lhs, '=', rhs));
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
      var step7 = rules.p(step6, '(p --> q) && (q --> p) --> (p = q)');
      return step7.justify('equalitySymmetric', arguments);
    },
    inputs: {},
    form: '',
    comment: 'Symmetry of equality'
  },

  equalityTransitive: {
    action: function() {
      var step1 = rules.axiom('axiom2');
      var step2 = rules.instVar(step1, Y.parse('{t. t = z}'), _var('h'));
      var step3 = rules.apply(step2, '/right/left');
      var step4 = rules.apply(step3, '/right/right');
      var step5 = rules.p(step4, '(a --> (b = c)) --> (a && c --> b)');
      return step5.justify('equalityTransitive', arguments);
    },
    inputs: {},
    form: '',
    comment: 'Transitivity of equality'
  },

  //
  // Real numbers
  // 
  // Assumptions (R x) && (R y), etc. are in the form:
  // (A1 --> (A2 --> <equation>)) to simplify introducing them from
  // the hypotheses.  This is equivalent to A1 && A2 --> <equation>.

  axiomCommutativePlus: {
    action: function() {
      return rules.assert('R x && R y --> x + y = y + x')
        .asHyps().justify('axiomCommutativePlus');
    },
    inputs: {},
    form: '',
    comment: 'Commutativity of addition'
  },

  axiomAssociativePlus: {
    action: function() {
      return rules.assert('R x && R y && R z --> x + (y + z) = (x + y) + z')
	.asHyps().justify('axiomAssociativePlus');
    },
    inputs: {},
    form: '',
    comment: 'Associativity of addition'
  },

  axiomCommutativeTimes: {
    action: function() {
      return rules.assert('R x && R y --> x * y = y * x')
	.asHyps().justify('axiomCommutativeTimes');
    },
    inputs: {},
    form: '',
    comment: 'Commutativity of multiplication'
  },

  axiomAssociativeTimes: {
    action: function() {
      return rules.assert('R x && R y && R z --> x * (y * z) = (x * y) * z')
	.asHyps().justify('axiomAssociativeTimes');
    },
    inputs: {},
    form: '',
    comment: 'Associativity of multiplication'
  },

  axiomDistributivity: {
    action: function() {
      return rules.assert('R x && R y && R z --> x * (y + z) = x * y + x * z')
	.asHyps().justify('axiomDistributivity');
    },
    inputs: {},
    form: '',
    comment: 'Distributivity of multiplication over addition'
  },

  axiomPlusZero: {
    action: function() {
      return rules.assert('R x --> x + 0 = x')
        .asHyps().justify('axiomPlusZero');
    },
    inputs: {},
    form: '',
    comment: 'Zero is the additive identity'
  },

  axiomTimesOne: {
    action: function() {
      return rules.assert('R x --> x * 1 = x')
        .asHyps().justify('axiomTimesOne');
    },
    inputs: {},
    form: '',
    comment: 'One is the multiplicative identity'
  },

  axiomTimesZero: {
    action: function() {
      return rules.assert('R x --> x * 0 = 0')
        .asHyps().justify('axiomTimesZero');
    },
    inputs: {},
    form: '',
    comment: 'x * 0 = 0'
  },

  axiomNeg: {
    action: function() {
      return rules.assert('R x --> x + neg x = 0')
        .asHyps().justify('axiomNeg');
    },
    inputs: {},
    form: '',
    comment: 'Negation is the inverse of addition'
  },

  axiomReciprocal: {
    action: function() {
      return rules.assert('R x && x != 0 --> x * recip x = 1')
        .asHyps().justify('axiomReciprocal');
    },
    inputs: {},
    form: '',
    comment: 'Reciprocal is the inverse of multiplication'
  },

  // Note: not structured as a rewrite rule.
  axiomPlusType: {
    action: function() {
      return rules.assert('R x && R y --> R (x + y)')
	.justify('axiomPlusType');
    },
    inputs: {},
    form: '',
    comment: 'Reals are closed under addition'
  },

  // Note: not structured as a rewrite rule.
  axiomTimesType: {
    action: function() {
      return rules.assert('R x && R y --> R (x * y)')
	.justify('axiomTimesType');
    },
    inputs: {},
    form: '',
    comment: 'Reals are closed under multiplication'
  },

  axiomNegType: {
    action: function() {
      return rules.assert('R x == R (neg x)')
	.justify('axiomNegType');
    },
    inputs: {},
    form: '',
    comment: 'Reals are closed under negation'
  },

  axiomReciprocalType: {
    action: function() {
      return rules.assert('R x && x != 0 == R (recip x)')
	.justify('axiomReciprocalType');
    },
    inputs: {},
    form: '',
    comment: 'Reals are (almost) closed under reciprocal'
  },

  // Evaluates arithmetic expressions with operators:
  // +, -, *, /, neg, =, >, >=, <, <=, and the type operator "R".
  // Checks that inputs are all numeric and that the result can be
  // guaranteed to be an exact integer.
  axiomArithmetic: {
    action: function(term) {
      if (term.isInfixCall()) {
	var left = Y.checkNumber(term.getLeft().value);
	var right = Y.checkNumber(term.getRight().value);
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
          var value = Y.checkRange(value);
          var rhs = new Y.Var(value.toFixed(0));
        }
        return rules.assert(Y.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else if (term instanceof Y.Call) {
        var arg = Y.checkNumber(term.arg.value);
        var op = term.fn;
        assert(op instanceof Y.Var,
               function() { return 'Unsupported operator: ' + op; });
        if (op.name == 'neg') {
          value = -arg;
          var rhs = new Y.Var(value.toFixed(0));
        } else if (op.name == 'R') {
          var rhs = T;
        } else {
          assert(false, 'Not an arithmetic expression: ' + term);
        }
        return rules.assert(Y.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else {
	assert(false, 'Not an arithmetic expression: ' + term);
      }
    },
    inputs: {term: 1},
    form: 'Term to evaluate: <input name=term>',
    comment: 'Evaluate an arithmetic expression'
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
      var infix = Y.infixCall;
      var deduper =
        rules.conjunctionDeduper(allHyps, Y.sourceStepComparator);
      var simplifier = rules.eqSelf(allHyps);
      if (deduper) {
        simplifier = rules.replace(deduper, simplifier, '/right');
      }
      // Now RHS of simplifier has no duplicate terms.
      var hypSet = new Y.TermSet();
      simplifier.getRight().eachHyp(function (hyp) { hypSet.add(hyp); });
      // Convert (R <n>) to T and (<n> != <m>) to T or F.
      hypSet.each(function(hyp) {
        var hyps = simplifier.getRight();
        if (hyp.isCall1('R') && (hyp.arg.isNumeral())) {
          var equation = rules.axiomArithmetic(hyp);
          var path = Y.path('/right' + hyps.pathTo(hyp));
          simplifier = rules.replace(equation, simplifier, path);
        } else if (hyp.isCall2('!=') &&
                   hyp.getLeft().isNumeral() &&
                   hyp.getRight().isNumeral()) {
          // Special case, also simplifies hyps like "2 != 0".
          var eqn = rules.eqSelf(hyp);
          var eqn2 = rules.arithmetic(eqn, '/right');
          var path = Y.path('/right' + hyps.pathTo(hyp));
          simplifier = rules.r(eqn2, simplifier, path);
        }
      });
      // Remove occurrences of T.
      deduper =
        rules.conjunctionDeduper(simplifier.getRight(), Y.sourceStepComparator);
      if (deduper) {
        simplifier = rules.replace(deduper, simplifier, '/right');
      }
      // Prove types of complex expressions by breaking them down and
      // proving the parts..
      hypSet = new Y.TermSet();
      simplifier.getRight().eachHyp(function(hyp) { hypSet.add(hyp); });
      hypSet.each(function(hyp) {
          var hyps = simplifier.getRight();
          if (hyp.isCall1('R') && hyp.arg instanceof Y.Call) {
            var otherHyps = hypsExcept(hyps, new Y.TermSet(hyp));
            var goal = infix(otherHyps, '-->', hyp);
            // Proved that hyp is a consequence of the others.
            // TODO: Prove the hyp from just the relevant set hypotheses,
            //   then use rules.conjunctsImplyConjunct and
            //   rules.makeConjunction to prove those hyps from the
            //   full set of hyps.
            var proved = rules.justifyNumericType(goal);
            if (proved) {
              var taut = rules.tautology('(a --> b) == (a && b == a)');
              // otherHyps && hyp == otherHyps:
              var subsumption = rules.rewrite(proved, '', taut);
              var ab = subsumption.getLeft();
              // hyps = otherHyps && hyp:
              var step1 = rules.equalConjunctions(infix(hyps, '=', ab));
              // So hyps = otherHyps:
              var step2 = rules.r(subsumption, step1, '/right');
              // So now allHyps = otherHyps:
              simplifier = rules.replace(step2, simplifier, '/right');
            }
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
      var infix = Y.infixCall;
      step.assertCall2('-->');
      var equation = rules.numericTypesSimplifier(step.getLeft());
      var result = rules.r(equation, step, '/left');
      return result.justify('simplifyNumericTypes', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    comment: 'Remove redundant type hypotheses in a step'
  },

  // Prove a goal statement of the form "hyps --> R (l <binop> r)" in
  // preparation for removing the term on the RHS from the full set of
  // hypotheses of some proof step.
  justifyNumericType: {
    action: function(goal) {
      // TODO: Break down the proof using only the required conjuncts
      //   to prove the RHS, then prove that the full set of conjuncts
      //   implies the required ones.  Create a new
      //   rules.conjunctsImplyConjunct to make this fast.
      var infix = Y.infixCall;
      var subst = goal.matchSchema('h --> (R e)');
      assert(subst, 'Bad input to justifyNumericType: ' + goal);
      var hyps = subst.h;
      var expr = subst.e;
      var map = new Y.TermMap();
      var schema = buildHypSchema(hyps, map);
      var result;
      if (expr.isNumeral()) {
        var step1 = rules.axiomArithmetic(goal.getRight());
        var step2 = rules.eqnSwap(step1);
        var step3 = rules.fromTIsA(step2);
        result = rules.anyImpliesTheorem(hyps, step3);
      } else if (map.has(goal.getRight())) {
        var taut =
          rules.tautology(infix(schema, '-->', map.get(goal.getRight())));
        result = rules.instantiate(taut, '', goal);
      } else if (expr.isCall2()) {
        var op = expr.getBinOp();
        var theorems = {'+': rules.axiomPlusType(), '*': rules.axiomTimesType()};
        assert(subst && op instanceof Y.Var && theorems[op.name]);
        var theorem = theorems[op.name];
        var implication = rules.subgoal(goal.getRight(), theorem);
        var subst2 = implication.matchSchema('h1 && h2 --> p');
        // Solve the two simplified problems:
        var thm1 = rules.justifyNumericType(infix(hyps, '-->', subst2.h1));
        var thm2 = rules.justifyNumericType(infix(hyps, '-->', subst2.h2));
        // Show that the conjunction of the simpler numeric type terms
        // is a consequence of the hypotheses.
        var conj = rules.makeConjunction(thm1, thm2);
        var taut = '(h --> a) && (h --> b) --> (h --> a && b)';
        var step1 = rules.forwardChain(conj, taut);
        var instance = rules.instantiate(theorem, '/left', step1.getRight());
        var step2 = rules.makeConjunction(step1, instance);
        result =
          rules.forwardChain(step2, '(h --> a) && (a --> b) --> (h --> b)');
      } else if (expr.isCall1('neg')) {
        var subgoal = infix(hyps, '-->', call('R', expr.arg));
        var step1 = rules.justifyNumericType(subgoal);
        var rewriter = rules.axiomNegType();
        result = rules.rewrite(step1, '/right', rewriter);
      } else if (expr.isCall1('recip')) {
        var subgoal1 = infix(hyps, '-->', call('R', expr.arg));
        var step1 = rules.justifyNumericType(subgoal1);
        // Justify this term as a consequence of either arithmetic or
        // the hypotheses:
        var term = infix(expr.arg, '!=', new Y.Var('0'));
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
          var subgoal2 = infix(hyps, '-->', term);
          var taut2 = rules.tautology(infix(schema, '-->', map.get(term)));
          var step2 = rules.instantiate(taut2, '', subgoal2);
        }
        if (arith) {
          var step1b = rules.fromTIsA(arith);
          var step2 = rules.anyImpliesTheorem(hyps, step1b);
        }
        // h --> term is now proved.
        var conj = rules.makeConjunction(step1, step2);
        var taut = rules.tautology('(h --> a) && (h --> b) --> (h --> a && b)');
        var step3 = rules.forwardChain(conj, taut);
        var result = rules.rewrite(step3, '/right', rules.axiomReciprocalType());
      } else {
        var map = new Y.TermMap();
        var lhs = buildHypSchema(goal.getLeft(), map);
        var rhs = buildHypSchema(goal.getRight(), map);
        var taut = infix(lhs, '-->', rhs);
        try {
          result = rules.tautInst(taut, map.subst);
        } catch(e) {
          return null;
        }
      }
      return result.justify('justifyNumericType', arguments);
    },
    inputs: {term: 1},
    form: 'Goal wff: <input name=term>',
    comment: 'Derive H --> R (<left> <binop> <right>).'
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
    comment: ('Consider a subexpression for transformation')
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
    axiom: 'axiomCommutativePlus'
  },
  commuteTimes: {
    axiom: 'axiomCommutativeTimes'
  },
  associatePlusToLeft: {
    axiom: 'axiomAssociativePlus'
  },
  associatePlusToRight: {
    axiom: 'axiomAssociativePlus',
    input: 'right'
  },
  associateTimesToLeft: {
    axiom: 'axiomAssociativeTimes'
  },
  associateTimesToRight: {
    axiom: 'axiomAssociativeTimes',
    input: 'right'
  },
  distribute: {
    axiom: 'axiomDistributivity'
  },
  group: {
    axiom: 'axiomDistributivity',
    input: 'right'
  },
  plusZeroElim: {
    axiom: 'axiomPlusZero'
  },
  plusZeroIntro: {
    axiom: 'axiomPlusZero',
    input: 'right'
  },
  timesOneElim: {
    axiom: 'axiomTimesOne'
  },
  timesOneIntro: {
    axiom: 'axiomTimesOne',
    input: 'right'
  },
  timesZeroElim: {
    axiom: 'axiomTimesZero'
  },
  plusNegElim: {
    axiom: 'axiomNeg'
  },
  timesRecipElim: {
    axiom: 'axiomReciprocal'
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
    } else if (input == 'right') {
      var comment = 'Rewrite back using ' + info.axiom;
    } else {
      var comment = 'Rewrite using ' + info.axiom;
    }
    // Add this info to ruleInfo:
    ruleInfo[name] = {
      // Add the axiom and the rule name to all calls to the action
      // function.
      action: Y.rbind(generators[input], null, info.axiom, name),
      inputs: {site: 1},
      form: '',
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
    // Remember ALL of the info as well, redundantly.  See the "to do"
    // above.
    var info = ruleInfo[key];
    if (!info.inputs) {
      info.inputs = {};
    }
    var fn = (typeof info == 'function') ? info : info.action;
    // Each function in rules has its action function as
    // the value of its innerFn property.
    rules[key] = fn;
    rules[key].info = info;
  }
}

// Actual rule functions to call from other code.
createRules(ruleInfo);

var identity = lambda(x, x);
var allT = lambda(x, T);

// Put definitions into their database:
Y.define('not', equal(F));
Y.define('!=', '{x. {y. not (x = y)}}');
Y.define('forall', equal(lambda(x, T)));
Y.define('exists', '{x. F} !=');
Y.defineCases('&&', identity, lambda(x, F));
Y.defineCases('||', allT, identity);
Y.defineCases('-->', identity, allT);

Y.define('-', '{x. {y. x + neg y}}');
Y.define('/', '{x. {y. x * recip y}}');

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
  var value = _theoremsByName[name];
  if (value == true) {
    value = _theoremsByName[name] = rules[name]();
  }
  return value;
}

// Add the axioms and theorems to the "database".  This can only
// include ones that are not "axiom schemas", i.e. not parameterized.
// Most of these axioms really have type parameters.  Ideally axiom
// and theorem schemas will be able to stay, but the details remain
// to be determined.

var axiomNames = ['axiom1', 'axiom2', 'axiom3', 'axiom5', 'axiomPNeqNotP'];

var theoremNames =
  (axiomNames.concat(['defFFromBook',
                      'defAnd', 'tIsXIsX', 'forallVT', 'eqTLemma',
                      'r5211', 't', 'r5212', 'r5230TF', 'r5230FT',
                      'r5231T', 'r5231F', 'falseEquals', 'trueEquals']));

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
        schema = schema ? Y.infixCall(schema, '&&', v) : v;
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
        result = result ? Y.infixCall(result, '&&', hyp) : hyp;
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

Y.rules = rules;

// A settable variable, export right here:
Y.autoAssert = false;

Y.axiomNames = axiomNames;
Y.theoremNames = theoremNames;
Y.addTheorem = addTheorem;
Y.getTheorem = getTheorem;
Y.findHyp = findHyp;

// For testing.
Y.ruleInfo = ruleInfo;
Y._tautologies = _tautologies;
Y._buildHypSchema = buildHypSchema;

}, '0.1', {requires: ['array-extras', 'expr', 'proof']});
