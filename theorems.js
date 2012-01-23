// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('theorems', function(Y) {


//// THEOREMS AND RULES

// Use the application's "assert" rather than YUI's.
var assert = Y.assertTrue;
// And make assertEqn convenient too.
var assertEqn = Y.assertEqn;

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

var identity = lambda(x, x);

var allT = lambda(x, T);

// Map from tautology string representation to tautology,
// for proved tautologies.  Private to the tautology rule.
var _tautologies = {};

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
// comment: comment to become the title of mentions of the rule name
//   in proof displays.
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
    hint: 'WFF to assert (possibly to prove later)'
  },

  /**
   * Suppose the given expression to be true.  This is the standard
   * way to introduce hypotheses into proofs.  If given a string,
   * parses it and uses the result.
   */
  assume: {
    action: function(assumption) {
      if (typeof assumption == 'string') {
	assumption = Y.parse(assumption);
      }
      // Flag the step as one with hypotheses, and record this step as
      // the source of the assumption.
      var step = call('-->', assumption, assumption).justify('assume', arguments);
      step.hasHyps = true;
      assumption.sourceStep = step;
      return step;
    },
    inputs: {term: 1},
    form: ('Assume <input name=term>'),
    hint: 'Hypothesis to assume'
  },

  /**
   * Converts a wff with hypotheses to an implication.  If there are
   * no hypotheses, returns its input unchanged.
   */
  asImplication: {
    action: function(wff) {
      if (!wff.hasHyps) {
        return wff;
      } else {
        var step1 = wff.justify('asImplication', arguments, [wff]);
        step1.hasHyps = false;
        return step1;
      }
    },
    inputs: {step: 1},
    form: ('Convert hypotheses to explicit implication in step '
           + '<input name=step>'),
    hint: 'Convert hypotheses to an explicit implication'
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
      // The derivations are computed in advance, and have
      // the name or name and true/false as the argument(s).
      return Y.getDefinition(name, tOrF).justify('definition', arguments);
    },
    inputs: {string: 1, optString: 2},
    form: ('Definition of <input name=string> '
           + 'if by cases enter T or F <input name=optString>'),
    hint: 'access a definition'
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
      assert(equation.isCall2('='),
	     'Rule R requires equation: ' + equation, equation);
      function replacer(expr) {
	if (expr.matches(equation.getLeft())) {
	  return equation.getRight();
	} else {
	  assert(false, 'Rule R: subexpression ' + expr +
                 '\n of ' + target +
                 '\n must match ' + equation.getLeft(), target);
	}
      }
      // Auto-justify input steps.
      if (!equation.ruleName) {
	equation.assert();
      }
      if (!target.ruleName) {
	target.assert();
      }
      var result = target.replace(path, replacer);
      var lvars = equation.getLeft().freeVars();
      // If the right side has any free vars not in the left side,
      // the result may have constraints not met by the target, so
      // typecheck it.
      var rvars = equation.getRight().freeVars();
      for (var name in rvars) {
	if (!(name in lvars)) {
	  Y.findType(result);
	  break;
	}
      }
      return result.justify('r', arguments, [target, equation]);
    },
    // inputs: {equation: 1, site: 2},
    // form: ('Replace selection with right side of step <input name=equation>'),
    comment: ('Replaces an occurrence of an expression with something'
              + ' it is equal to.'),
    hint: 'replace term with equal term'
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
    comment: ('Replaces an occurrence of an expression with something'
              + ' equal to it, replacing right side with left side.')
  },

  axiom1: {
    action: function() {
      // var result = Y.parse('g T && g F = forall {x : g x}');
      var result =  equal(call('&&', call(g, T), call(g, F)),
			  call('forall', lambda(x, call(g, x))));
      return result.justify('axiom1');
    },
    inputs: {},
    form: '',
    comment: ('T and F are all of the booleans')
  },

  axiom2: {
    action: function() {
      var result = Y.parse('x = y --> h x = h y');
      return result.justify('axiom2');
    },
    inputs: {},
    form: '',
    comment: ('equal inputs yield equal outputs.')
  },

  axiom3: {
    action: function() {
      var result = Y.parse('(f = g) = forall {x : f x = g x}');
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
      assert(call instanceof Y.Call && call.fn instanceof Y.Lambda,
	     'Axiom 4 needs ({X : B} A), got: ' + call.toString());
      var lambdaExpr = call.fn;
      var result =
        equal(call, Y.subFree(call.arg, lambdaExpr.bound, lambdaExpr.body));
      // Always make sure the call has a type.  It came from elsewhere.
      Y.findType(call);
      return result.justify('axiom4', arguments);
    },
    inputs: {term: 1},  // Specifically a Call to a Lambda.
    form: 'Enter {v : body} expr <input name=term>',
    hint: 'apply a function to its argument',
    comment: ('')
  },

  axiom5: {
    action: function() {
      var result = Y.parse('(the (= y)) = y');
      return result.justify('axiom5');
    },
    inputs: {},
    form: '',
    comment: ('axiom of description.')
  },

  // Added by Cris instead of definition of F in book.
  // not [T = F] (thus F = [T = F]).
  // Alternatively, add (forall {x : not (x = (not x))}) below,
  // shortening the proof of [F = [F = T]].
  axiomTIsNotF: {
    action: function() {
      var result = call('not', equal(T, F));
      return result.justify('axiomTIsNotF');
    },
    comment: ('')
  },

  // Generalizes axiomTIsNotF.
  // Rewrite to (forall p : F = [p = [not p]]), instantiate, expand "not":
  // 1. F = [F = [F = F]], so 2. F = [F = T] (r5230FT)
  // 3. F = [T = [F = T]], so F = [T = F] (r5230TF) by
  // Rule R on r5230FT and step 3.
  axiomPNeqNotP: {
    action: function() {
      var result =
        call('forall', lambda(p, call('not', equal(p, call('not', p)))));
      return result.justify('axiomPNeqNotP');
    },
    inputs: {},
    form: '',
    hint: '(forall {p : not (p = not p)})',
    comment: ('')
  },

  defForall: function() {
    var result = equal('forall', equal(lambda(x, T)));
    return result.justify('defForall');
  },

  // Definition of F, for book-style proofs.
  defFFromBook: function() {
    return equal(F, call('forall', lambda(x, x))).justify('defFFromBook');
  },

  defNot: function() {
    return equal('not', equal(F)).justify('defNot');
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
    hint: 'from A = B to B = A',
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
    hint: 'from F = G to (F A) = (G A)',
    comment: 'Given f = g, derive (f A) = (g A)'
  },

  // r5201f.  Works with hypotheses.
  applyToBoth: {
    action: function(a, h_bc) {
      var bc = h_bc.unHyp();
      var abab = rules.eqSelf(call(a, bc.getLeft()));
      var abac = rules.replace(h_bc, abab, '/right/arg');
      return abac.justify('applyToBoth', arguments, [h_bc]);
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
      path = Y.path(path, a);
      var target = a.locate(path);
      if (target instanceof Y.Var) {
        var result = rules.replace(rules.definition(target.name), a, path);
        return result.justify('useDefinition', arguments, [a]);
      } else {
        assert(target instanceof Y.Call && target.arg instanceof Y.Var,
                 'Target of useDefinition not suitable: ' + target);
        var arg = target.arg;
        assert(arg.name == 'T' || arg.name == 'F',
                 'Target of useDefinition not suitable: ' + target);
        var result =
	  rules.replace(rules.definition(target.fn.name, arg), a, path);
        return result.justify('useDefinition', arguments, [a]);
      }
    },
    inputs: {site: 1},
    form: '',
    hint: 'replace name with its definition',
    comment: ('')
  },

  /**
   * Beta-reduce an application of a lambda expression to an argument,
   * with the subexpression identified by a path (within a theorem).
   * Rule Replace packaged for convenience.
   */
  apply: {
    action: function(step, path) {
      path = Y.path(path, step);
      var target = step.locate(path);
      assert(target, 'Path ' + path + ' not found in ' + step, step);
      assert(target instanceof Y.Call && target.fn instanceof Y.Lambda,
             'Reduce needs a call to a lambda, got: ' + target, step);
      var equation = rules.axiom4(target);
      var result = rules.replace(equation, step, path);
      return result.justify('apply', arguments, [step]);
    },
    inputs: {reducible: 1},
    form: '',
    hint: 'apply a function to its argument',
    comment: ('Substitutes an actual argument for the formal variable'
              + ' in one function call of a WFF.')
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
      var eqn = h_eqn.unHyp();
      if (typeof v == 'string') {
        v = new Y.Var(v);
      }
      assert(eqn.isBinOp() && eqn.getBinOp() == '=',
             'Not an equation: ' + eqn,
             h_eqn);
      assert(v instanceof Y.Var, 'Not a variable: ' + v, h_eqn);
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

  // T = [B = B] (5210)
  eqT: {
    action: function(b) {
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
      // TODO: Make the steps to here a lemma.
      // TODO: Make the following steps a simple rule of inference.
      var step3 = rules.applyBoth(step2d, b);
      var step4a = rules.apply(step3, '/left');
      var step4b = rules.apply(step4a, '/right');
      return step4b.justify('eqT', arguments, []);
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

  // Target is forall {x : B}, expr is A, which will replace
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
    var step3b = rules.rRight(rules.defForall(), step3a, '/right/fn');
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
    inputs: {equation: [1, 2], name: 3},
    form: ('Cases: true case step <input name=equation1>'
	   + ' false case step <input name=equation2>,'
	   + ' use variable <input name=varName>'),
    hint: 'proof by cases, for equations',
    comment: ('Given a function expression of the form {v | A = B},'
              + ' infers (forall {x | A = B}) assuming A = B is proven'
              + ' for the substitutions with v = T and v = F.')
  },

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
  // Derives (forall {v : T}) given a variable v.
  forallT: {
    action: function(v) {
      var step1 = rules.theorem('forallVT');
      var step2 = rules.changeVar(step1, '/arg', _var(v));
      return step2.justify('forallT', arguments);
    },
    inputs: {varName: 1},
    form: 'Variable to bind: <input name=varName>',
    comment: ('(forall {v : T})')
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
    form: ('In step <input name=step> generalize on variable <input name=varName>'),
    hint: 'from A to (forall {x : A})',
    comment: ('Universal Generalization, wrap a theorem A in'
              + ' (forall v A) using the variable of your choice.')
  },

  // 5221 (one variable), in the given step substitute term A for
  // variable v, which may also be a string, which will be converted
  // to a variable.  Handles hypotheses.
  instVar: {
    action: function(step, a, v) {
      // Note that addForall checks that v is not free in the step.
      var step1 = rules.addForall(step, v);
      var step2 = rules.instForall(step1, a);
      return step2.justify('instVar', arguments, [step]);
    },
    inputs: {step: 1, term: 2, varName: 3},
    form: ('In step <input name=step> substitute <input name=term>'
	   + 'for variable <input name=varName> '),
    hint: 'substitute for free variable',
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.')
  },

  // More like the book's 5221.  For each name in the map (a string),
  // substitutes the expression associated with it in the map, using
  // simultaneous substitution.  Handles hypotheses.
  instMultiVars: {
    action: function(b, map) {
      var namesReversed = [];
      var step = b;
      for (var name in map) {
	// Note that addForall checks that the name is not free.
	step = rules.addForall(step, name);
	namesReversed.unshift(name);
      }
      // Then substitute for the renamed variables.
      Y.Array.each(namesReversed, function(name) {
        step = rules.instForall(step, map[name]);
      });
      return step.justify('instMultiVars', arguments, [b]);
    },
    inputs: {step: 1},
    // TODO: form: ...
    comment: ('Substitute in B for each variable named in the map, '
              + 'its value in the map')
  },

  // (5222) Given two theorems that are substitutions of T and
  // F respectively into a WFF; and a variable or variable name,
  // proves the WFF.
  // TODO: Handle hypotheses.
  cases: {
    action: function(caseT, caseF, v) {
      v = _var(v);
      // Note: caseF has no variables not in caseT, so no need to
      // calculate all of its names.
      var newVar = Y.genVar('v', caseT.allNames());
      var gen = caseT.generalizeTF(caseF, newVar);
      var step1a = rules.axiom4(call(lambda(newVar, gen), T));
      var step1b = rules.rRight(step1a, caseT, '');
      var step1c = rules.toTIsA(step1b);
      var step2a = rules.axiom4(call(lambda(newVar, gen), F));
      var step2b = rules.rRight(step2a, caseF, '');
      var step2c = rules.toTIsA(step2b);
      var step3 = rules.theorem('r5212');
      var step4a = rules.replace(step1c, step3, '/left');
      var step4b = rules.replace(step2c, step4a, '/right');
      var step5 = rules.instVar(rules.axiom1(), lambda(newVar, gen), g);
      var step6 = rules.replace(step5, step4b, '/');
      var step7a = rules.instForall(step6, v);
      var step7b = rules.apply(step7a, '/');
      return step7b.justify('cases', arguments, [caseT, caseF]);
    },
    inputs: {step: [1, 2], name: 3},
    form: ('Cases: true case step <input name=step1>,'
	   + ' false case <input name=step2>,'
	   + ' use variable name <input name=name>'),
    hint: 'proof by cases',
    comment: ('Prove a theorem by cases given two theorems that'
              + ' show it with T and F.')
  },

  // 5224
  // Given P and P --> Q, derive Q.
  // TODO: Handle hypotheses.
  modusPonens: {
    action: function(a, b) {
      var step1 = rules.toTIsA(a);
      var step2 = rules.rRight(step1, b, '/left');
      var step3 = rules.useDefinition(step2, '/fn');
      var step4 = rules.apply(step3, '');
      return step4.justify('modusPonens', arguments, arguments);
    },
    inputs: {step: 1, implication: 2},
    form: ('Modus ponens: hypothesis step <input name=step>,'
	   + ' implication in step <input name=implication>'),
    hint: 'modus ponens',
    comment: ('Modus Ponens.  Given A and A --> B derives B.')
  },

  // Prove [T = F] = F (same as 5217)
  r5230TF_alternate: {
    action: function() {
      var step1 = rules.axiom('axiomTIsNotF');
      var step2 = rules.useDefinition(step1, '/fn');
      var step3 = rules.eqnSwap(step2);
      return step3.justify('r5230TF');
    },
    comment: ('[T = F] = F')
  },

  // Prove [F = T] = F
  // Simpler proof when axiomPNeqNotP rather than axiomTIsNotF (above).
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
      var step24 = rules.r(rules.definition('not'),
                           rules.axiom('axiomTIsNotF'),
                           '/fn');
      var step25 = rules.r(step24, step23, '/right');
      // Now use the cases rule:
      var step5 = rules.cases(equal(call('-->', T, F), equal(T, F)),
                              equal(call('-->', F, F), equal(F, F)),
                              x);
      // Then instantiate [F = T] for x.
      var step6 = rules.instVar(step5, equal(F, T), x);
      // And use the fact that [F = T] --> F
      var step7 = rules.rRight(step4, step6, '/left');
      var step8 = rules.fromTIsA(step7);
      return step8.justify('r5230FT');
    },
    comment: ('[F = T] = F')
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
      return rules.eqnSwap(rules.defNot()).justify('falseEquals');
    },
    comment: ('[F =] = not')
  },

  // Another helper for evalBool, not in book.
  // [[T =] = {x : x}].
  trueEquals: {
    action: function() {
      var step1 = rules.r5218(x);
      var step2 = rules.eqSelf(x);
      var step3 = rules.applyToBoth(lambda(x, x), step2);
      var step4 = rules.apply(step3, '/left');
      var step5 = rules.r(step4, step1, '/right');
      var step6 = rules.addForall(step5, x);
      var step7 = rules.instVar(rules.axiom('axiom3'), equal(T), f);
      var step8 = rules.instVar(step7, lambda(x, x), g);
      var step9 = rules.rRight(step8, step6, '');
      return step9.justify('trueEquals', arguments);
    },
    comment: ('[T =] = {x | x}')
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
    comment: ('Evaluates a boolean expression with no free variables.')
  },

  // Proves an inference that the wff is a tautology and
  // returns it.  Checks that it is indeed proven to be a
  // tautology.  5233
  tautology: {
    action: function(wff) {
      var key = wff + '';
      var taut = _tautologies[key];
      if (taut) {
        return taut;
      } else {
        var names = wff.freeNames();
        // Not really a loop, just works with the first free (variable!)
        // name returned.
        for (var name in names) {
          if (!Y.isConstant(name) && !Y.isDefined(name)) {
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

  // Given two theorems a and b, proves a && b.
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
    hint: 'from A and B to (A && B)',
    comment: ('Given a and b, derive a && b')
  },

  // Any instance of a tautology is a theorem.  This is part
  // of the book's Rule P.
  //
  // Given a tautology or tautology with arbitrary hypotheses and a
  // substitution, derives an instantiation of the tautology.  If the
  // input has a hypothesis, that passes through to the result.
  // TODO: handle hypotheses.
  tautInst: {
    action: function(h_tautology, map) {
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

  // Given a theorem and an arbitrary boolean term, proves that the
  // term implies the theorem.
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
  // ((forall {v : A || B}) --> A || (forall {v : B})).  Could run even if
  // the variable is free, but would not give desired result.
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

  // Given an implication A --> B and a variable v, produces a theorem
  // (A --> B) --> (A --> forall {v : B}).  (5237)
  // TODO: Accept hypotheses.  Currently buggy.
  implyForall: {
    action: function(v, h_a_b) {
      var a_b = h_a_b.unHyp();
      v = Y.varify(v);
      assert(a_b.isCall2('-->'), 'Must be an implication: ' + a_b, h_a_b);
      var a = a_b.getLeft();
      var b = a_b.getRight();
      // Restriction to ensure the desired result.
      assert(!a.hasFreeName(v.name),
	     'implyForall: variable ' + v + 'cannot occur free in ' + a, h_a_b);
      var step1 = rules.r5235(v, call('not', a), b);
      var h_taut = equal(call('||', call('not', p), q), implies(p, q));
      if (h_a_b.hasHyps) {
	var h = h_a_b.getLeft();
	assert(!h.hasFreeName(v.name),
	       'implyForall: variable ' + v + 'cannot occur free in ' + h,
	       h_a_b);
	h_taut = Y.infixCall(h, '-->', h_taut);
	h_taut.hasHyps = true;
      }
      var step2 = rules.tautInst(h_taut, {p: a, q: b});
      var step3 = rules.replace(step2, step1, '/left/arg/body');
      var map4 = {
        p: a,
        q: step1.locate('/right/right')
      };
      var step4 = rules.tautInst(h_taut, map4);
      var step5 = rules.replace(step4, step3, '/right');
      var step6 = rules.addForall(a_b, v);
      var step7 = rules.modusPonens(step6, step5);
      return step7.justify('implyForall', arguments, [a_b]);
    },
    inputs: {varName: 1, implication: 2},
    form: ('Move forall inside "implies" binding '
	   + 'variable <input name=varName> '
	   + 'implication <input name=implication>'),
    comment: ('Move "forall" inside "implies" provided the variable '
              + 'is not free in the first argument.')
  },
    
  // Rule P (without hypotheses).  This handles two antecedents.  The
  // given tautology must match ((a1 && a2) --> b.  To use more than
  // two antecedents, use this with a1 as one antecedent and combine
  // the rest with makeConjunction.
  //
  // (5234)  TODO: Handle hypotheses.
  p: {
    action: function(a1, a2, b, tautology) {
      var step2 = rules.makeConjunction(a1, a2);
      var step1 = rules.tautology(tautology);
      var tautologous = implies(step2, b);
      var substitution = Y.matchAsSchema(tautology, tautologous);
      var step3 = rules.instMultiVars(step1, substitution);
      var step4 = rules.modusPonens(step2, step3);
      return step4.justify('p', arguments, [a1, a2]);
    },
    // TODO: inputs ... ?
    comment: ('Simplified form of Rule P without hypotheses.')
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
  //
  // TODO: Consider renaming bound variables in C as needed so this
  // rule can always be applied.
  replace: {
    action: function(h_equation_arg, h_c_arg, path) {
      path = Y.path(path, h_c_arg);
      var h_c = h_c_arg;
      var h_equation = h_equation_arg;
      if (h_equation.isCall2('=')) {
	assert(!(h_c.hasHyps && path.isLeft()),
	       'Cannot apply the Replace rule to hypotheses',
	       h_c_arg);
        // Allow "replace" to be used for situations where "r" is
        // applicable.  The case with hypotheses in h_c can be
        // considered as rule RR (5202).
        var result = rules.r(h_equation, h_c, path);
	if (h_c.hasHyps) {
	  result.hasHyps = true;
	}
	return result;
      }
      assert(h_equation.isCall2('-->') && h_equation.getRight().isCall2('='),
	     'Not an equation: ' + h_equation, h_equation_arg);
      // h_equation has the form H --> A = B

      // Give the two WFFs the same hypotheses.
      h_c = rules.appendStepHyps(h_c, h_equation);
      h_equation = rules.prependStepHyps(h_equation, h_c_arg);

      // h_c can be given as an implication, but without hypotheses,
      // which is OK, but in the end it must be an implication.
      assert(h_c.isCall2('-->'), 'Not an implication: ' + h_c, h_c);
      // Now both wffs are implications.  Record the hypotheses as
      // "h".  (LHS of any implication is also OK.)
      var h = h_equation.getLeft();
      if (!h_c.hasHyps) {
	// If there are no hypotheses, we do not attempt to make the
	// LHS of the two input steps match.
	assert(h_c.getLeft().matches(h),
	       'LHS mismatch in "replace" rule',
	       h_c_arg, h_c_arg);
      }

      // From here on work with implications directly, not hypotheses.
      h_equation = h_equation.dup();
      h_c = h_c.dup();

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
      var tautology = Y.parse('(p --> q) && (q --> r) --> (p --> r)');
      var step3 = rules.p(step1,
                          step2,
                          implies(step1.getLeft(), step2.getRight()),
                          tautology);
      var taut2 = Y.parse('(h --> p) && (h --> (p = q)) --> (h --> q)');
      var step4 = rules.p(h_c,
                          step3,
                          implies(h, step3.getRight().getRight()),
                          taut2);
      // TODO: Consider setting "hasHyps" systematically, probably in "justify".
      step4.hasHyps = h_c_arg.hasHyps || h_equation_arg.hasHyps;
      return step4.justify('replace', arguments, [h_equation_arg, h_c_arg]);
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
        var step = rules.asImplication(target);
	if (target.hasHyps) {
	  if (step.getLeft().matches(hypStep.getLeft())) {
	    // Hyps are the same, so no change to the given step.
	    return step;
	  }
	  var taut = Y.parse('(h1 --> p) --> ((h1 && h2) --> p)');
	  var subst = {
	    h1: step.getLeft(),
	    h2: hypStep.getLeft(),
	    p: step.getRight()
	  };
	  var step1 = rules.tautInst(taut, subst);
	  var step2 = rules.modusPonens(step, step1);
	  var result = step2.justify('appendStepHyps', arguments, [target]);
	  result.hasHyps = true;
	  return result;
	} else {
	  var subst = {
	    p: step,
	    h2: hypStep.getLeft()
	  };
	  var step1 = rules.tautInst(Y.parse('p --> (h2 --> p)'), subst);
	  var step2 = rules.modusPonens(step, step1);
	  var result = step2.justify('appendStepHyps', arguments, [target]);
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
  prependStepHyps: {
    action: function(target, hypStep) {
      if (hypStep.hasHyps) {
        var step = rules.asImplication(target);
	if (target.hasHyps) {
	  if (step.getLeft().matches(hypStep.getLeft())) {
	    // Hyps are the same, so no change to the given step.
	    return step;
	  }
	  if (step.getLeft().matches(hypStep.getLeft())) {
	    // Don't display the inference step.
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
	  var result = step2.justify('prependStepHyps', arguments, [target]);
	  result.hasHyps = true;
	  return result;
	} else {
	  var subst = {
	    p: step,
	    h1: hypStep.getLeft()
	  };
	  var step1 = rules.tautInst(Y.parse('p --> (h1 --> p)'), subst);
	  var step2 = rules.modusPonens(step, step1);
	  var result = step2.justify('prependStepHyps', arguments, [target]);
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
    form: ('Simplify the hypotheses of step <input name=step>'),
    hint: 'Simplify the hypotheses'
  },


  //
  // OPTIONAL/UNUSED
  // 

  // Experiment with Andrews' definition of "and".
  funWithAnd: function() {
    var fa = rules.defForall();
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


// Actual rule functions to call from other code.
Y.createRules(ruleInfo);

// Set up access to the "rules" object defined in proof.js.
var rules = Y.rules;

// Put definitions into their database:
Y.define('not', equal(F))
Y.define('forall', equal(lambda(x, T)));
Y.defineCases('&&', identity, lambda(x, F));
Y.defineCases('||', allT, identity);
Y.defineCases('-->', identity, allT);

// Add the axioms and theorems to the "database".  This can only
// include ones that are not "axiom schemas", i.e. not parameterized.
// Most of these axioms really have type parameters.  Ideally axiom
// and theorem schemas will be able to stay, but the details remain
// to be determined.

var axiomNames = ['axiom1', 'axiom2', 'axiom3', 'axiom5', 'axiomPNeqNotP'];

var theoremNames =
  (axiomNames.concat(['defForall', 'defFFromBook', 'axiomTIsNotF',
                      'defNot', 'defAnd', 'tIsXIsX', 'forallVT',
                      'r5211', 't', 'r5212', 'r5230TF', 'r5230FT',
                      'r5231T', 'r5231F', 'falseEquals', 'trueEquals']));

for (var i = 0; i < theoremNames.length; i++) {
  Y.addTheorem(theoremNames[i]);
}


//// Export public names.

Y.axiomNames = axiomNames;
Y.theoremNames = theoremNames;

// For testing.
Y.ruleInfo = ruleInfo;
Y._tautologies = _tautologies;

}, '0.1', {requires: ['array-extras', 'expr', 'proof']});
