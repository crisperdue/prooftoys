// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('theorems', function(Y) {


//// THEOREMS AND RULES

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

var identity = lambda(x, x);

var allT = lambda(x, T);

// List of rules that work with hypotheses.
//
// This covers rules that precede the deduction theorem (5240).
//
// All of the equality rules (5201 parts), by R and/or Replace
//   depending on the situation.
// Universal instantiation (5215) - by rule R.
// Rule T (5219) - by rule RR.
// uGen (5220) - by rule Replace.
// sub and subAll (5221) - uses uGen.
// cases (5222) - uses Replace.
// modusPonens (5224) - uses Replace.
// tautInst (Rule P, 5234) - uses modusPonens.
// impliesForall (5237) - uses Replace and tautInst.


// Map from inference rule name to a JavaScript function that
// implements it.  The functions may use a global variable
// named "rules" that should have all of these functions in it,
// wrapped with code that manages the inference stack for
// Y.makeInference.
var ruleInfo = {

  /**
   * The name "given" is used in Inferences to indicate that
   * the result of the inference is an assumption.
   */
  given: function(assumption) {
    return assumption;
  },

  /**
   * Refer to a theorem by looking it up in the database rather
   * than proving it all over again.
   */
  theorem: function(name) {
    return Y.getTheorem(name).result;
  },

  /**
   * Refer to a definition in the definitions database.  If the
   * definition is by cases, takes a second argument of T or F
   * as desired.  Throws an exception if not found.
   */
  definition: function(name, tOrF) {
    return Y.getDefinition(name, tOrF);
  },

  /**
   * Refer to an axiom in the theorems database.  Affects the
   * display of the proof step, but otherwise the same as "theorem".
   * Currently also used for definitions.
   */
  axiom: function(name) {
    return Y.getTheorem(name).result;
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
      if (equation.isCall2('=')) {
        function replacer(expr) {
          if (expr.matches(equation.getLeft())) {
            return equation.getRight().copy();
          } else {
            Y.assert(false, 'Rule R: subexpression ' + expr +
                     '\n of ' + target +
                     '\n must match ' + equation.getLeft());
          }
        }
        var result = target.replace(path, replacer);
        return result;
      } else if (equation.isCall2('-->') || equation.isCall2('|-')) {
        rules.replace(equation, target, path);
      } else {
        throw new Error('Rule R requires equation: ' + equation);
      }
    },
    inputs: [{secondary: 'equation'}, {primary: 'location'}],
    comment: ('Replaces an occurrence of an expression with something'
              + ' it is equal to.')
  },

  /**
   * Same as Rule R, but replaces an occurrence in target of the right
   * side of the equation with its left side.
   */
  rRight: {
    action: function(equation, target, path) {
      path = Y.path(path);
      var rev = rules.eqnSwap(equation);
      return rules.r(rev, target, path);
    },
    inputs: [{secondary: 'equation'}, {primary: 'location'}],
    comment: ('Replaces an occurrence of an expression with something'
              + ' equal to it, replacing right side with left side.')
  },

  axiom1: {
    action: function() {
      return equal(call('&&', call(g, T), call(g, F)),
                   call('forall', lambda(x, call(g, x))));
    },
    comment: ('')
  },

  // (--> (= x y) (= (h x) (h y)))
  axiom2: {
    action: function() {
      return call('-->', equal(x, y), equal(call(h, x), call(h, y)));
    },
    comment: ('')
  },

  // (= (= f g) (= {x : T} {x : (= (f x) (g x))}))
  axiom3: {
    action: function() {
      return equal(equal(f, g),
                   call('forall',
                        lambda(x, equal(call(f, x), call(g, x)))));
    },
    comment: ('')
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: {
    action: function(call) {
      if (call instanceof Y.Call && call.fn instanceof Y.Lambda) {
        var lambdaExpr = call.fn;
        return equal(call,
                     Y.subFree(call.arg, lambdaExpr.bound, lambdaExpr.body));
      } else {
        throw new Error('Axiom 4 needs ({X : B} A), got: ' + call.toString());
      }
    },
    comment: ('')
  },

  axiom5: {
    action: function() {
      return equal(call('the', equal(y)), y);
    },
    comment: ('')
  },

  // Added by Cris instead of definition of F in book.
  // not [T = F] (thus F = [T = F]).
  // Alternatively, add (forall {x : not (x = (not x))}) below,
  // shortening the proof of [F = [F = T]].
  axiomTIsNotF: {
    action: function() {
      return call('not', equal(T, F));
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
      return call('forall', lambda(p, call('not', equal(p, call('not', p)))));
    },
    comment: ('')
  },

  defForall: function() {
    return equal('forall', equal(lambda(x, T)));
  },

  // Definition of F, for book-style proofs.
  defFFromBook: function() {
    return equal(F, call('forall', lambda(x, x)));
  },

  defNot: function() {
    return equal('not', equal(F));
  },

  // Book only.
  defAnd: function() {
    return equal('&&', lambda(x, lambda(y, equal(lambda(g, call(g, T, T)),
                                                 lambda(g, call(g, x, y))))));
  },

  axioms: {
    action: function() {
      rules.axiom('axiom1');
      rules.axiom('axiom2');
      rules.axiom('axiom3');
      rules.axiom('axiom5');
      return rules.axiom('axiomPNeqNotP');
    },
    comment: ('Really just a list of axioms not including axiom 4,'
              + ' which is a schema with many instances.')
  },

  definitions: {
    action: function() {
      rules.definition('not');
      rules.definition('forall');
      rules.definition('&&', T);
      rules.definition('&&', F);
      rules.definition('||', T);
      rules.definition('||', F);
      rules.definition('-->', T);
      return rules.definition('-->', F);
    },
    comment: ('Really just a list of definitions.')
  },

  //
  // Theorems and rules of inference.
  //

  // Takes an arbitrary expression A, concluding that it is equal
  // to itself. (5200)
  eqSelf: {
    action: function(a) {
      var step1 = rules.axiom4(call(lambda(x, x), a));
      return rules.r(step1, step1, '/left');
    },
    inputs: [{term: 'any'}],
    comment: 'Derives A = A.'
  },

  // r5201a, not used
  replaceWhole: function(a, ab) {
    var aa = rules.eqSelf(a);
    var b = ab.getRight();
    var result = rules.r(ab, a, '/');
    return result;
  },

  // r5201b
  eqnSwap: {
    action: function(ab) {
      var aa = rules.eqSelf(ab.getLeft());
      var ba = rules.r(ab, aa, '/left');
      return ba;
    },
    inputs: [{primary: 'equation'}],
    comment: 'From A = B derives B = A'
  },

  // r5201c
  eqnChain: {
    action: function(ab, bc) {
      var ac = rules.r(bc, ab, '/right');
      return ac;
    },
    comment: 'From A = B and B = C derives A = C'
  },

  // r5201d, not used
  applyBySides: function(ab, cd) {
    var a = ab.getLeft();
    var b = ab.getRight();
    var c = cd.getLeft();
    var d = cd.getRight();
    var ac = call(a, c);
    var acac = rules.eqSelf(ac);
    var acbc = rules.r(ab, acac, '/right/fn');
    var acbd = rules.r(cd, acbc, '/right/arg');
    return acbd;
  },

  // r5201e
  applyBoth: {
    action: function(eqn, a) {
      var step1 = rules.eqSelf(call(eqn.locate('/left'), a));
      var step2 = rules.r(eqn, step1, '/right/fn');
      return step2;
    },
    inputs: {or: [{primary: 'equation', secondary: {term: 'any'}},
                  ({primary: {term: 'any'}, secondary: 'equation'})]},
    comment: 'Given f = g, derive (f A) = (g A)'
  },

  // r5201f
  applyToBoth: {
    action: function(a, bc) {
      var abab = rules.eqSelf(call(a, bc.getLeft()));
      var abac = rules.r(bc, abab, '/right/arg');
      return(abac);
    },
    inputs: {or: [{primary: 'equation', secondary: {term: 'any'}},
                  ({primary: {term: 'any'}, secondary: 'equation'})]},
    comment: 'Given B = C derives (f B) = (f C)'
  },

  // Use the definition of the given name at the given location
  // in WFF A.  If the definition is by cases the location should
  // be a call to the named function, with T or F as the argument.
  useDefinition: {
    // TODO: Modify to just take a wff and path.  Probably reduce
    // the result automatically.
    action: function(defName, a, path) {
      var target = a.locate(path);
      if (target instanceof Y.Var) {
        return rules.r(rules.definition(defName), a, path);
      } else {
        Y.assert(target instanceof Y.Call && target.arg instanceof Y.Var,
                 'Target of useDefinition not suitable');
        var arg = target.arg;
        Y.assert(arg.name == 'T' || arg.name == 'F',
                 'Target of useDefinition not suitable');
        return rules.r(rules.definition(target.fn.name, arg), a, path);
      }
    },
    comment: ('')
  },

  /**
   * Beta-reduce an application of a lambda expression to an argument,
   * with the subexpression identified by a path (within a theorem).
   * Rule R packaged for convenience.
   */
  reduce: {
    action: function(expr, path) {
      path = Y.path(path);
      var target = expr.locate(path);
      Y.assert(target, 'Path ' + path + ' not found in ' + target);
      Y.assert(target instanceof Y.Call && target.fn instanceof Y.Lambda,
               'Reduce needs a call to a lambda, got: ' + target);
      var equation = rules.axiom4(target);
      var result = rules.r(equation, expr, path);
      return result;
    },
    inputs: [{primary: 'location'}],
    comment: ('Substitutes an actual argument for the formal variable'
              + ' in one function call of a WFF.')
  },

  /**
   * Change the name of a bound variable.  Replaces the lambda
   * subexpression in expr at path with one that binds newName, which
   * may be a string or Var.
   */
  changeVar: {
    action: function(expr, path, newVar) {
      if (typeof newVar == 'string') {
        newVar = new Y.Var(newVar);
      }
      var target = expr.locate(path);
      Y.assert(target instanceof Y.Lambda, 'Not a function: ' + target);
      Y.assert(!expr.freeNames()[newVar.name],
               'New bound variable ' + newVar.name + ' must not occur free.');
      var changed = lambda(newVar,
                           Y.subFree(newVar, target.bound, target.body));
      var step1 = rules.eqSelf(changed);
      var step2 = rules.r(step1, expr, path);
      return step2;
    },
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
    action: function(eqn, v) {
      if (typeof v == 'string') {
        v = new Y.Var(v);
      }
      Y.assert(eqn.isBinOp() && eqn.getBinOp() == '=',
               'Not an equation: ' + eqn);
      Y.assert(v instanceof Y.Var, 'Not a variable: ' + v);
      var step1 = rules.eqSelf(lambda(v, eqn.getLeft()));
      var step2 = rules.r(eqn, step1, '/right/body');
      return step2;
    },
    comment: ('Wraps each side of an equation in a function'
              + ' using the bound variable of your choice.')
  },

  /**
   * Substitutes term "a" for variable "v" in equation b_c,
   * with the result a consequence of b_c.  (5209)
   */
  instEqn: {
    action: function(b_c, a, v) {
      var bound = rules.bindEqn(b_c, v);
      var step2 = rules.applyBoth(bound, a);
      var step3 = rules.reduce(step2, '/left');
      var step4 = rules.reduce(step3, '/right');
      return step4;
    },
    comment: ('Instantiates a free variable in an equation.')
  },

  // thm: T = [B = B] (5210)
  eqT: {
    action: function(b) {
      var a3 =
        rules.useDefinition('forall', rules.axiom('axiom3'), '/right/fn');
      var identity = lambda(y, y);
      var step1a = rules.instEqn(a3, identity, f);
      var step1b = rules.instEqn(step1a, identity, g);
      var step2a = rules.eqSelf(identity);
      // Eliminate the LHS of step2a:
      var step2b = rules.r(step1b, step2a, '/');
      var step2c = rules.reduce(step2b, '/right/body/left');
      var step2d = rules.reduce(step2c, '/right/body/right');
      // TODO: Make the steps to here a lemma.
      // TODO: Make the following steps a simple rule of inference.
      var step3 = rules.applyBoth(step2d, b);
      var step4a = rules.reduce(step3, '/left');
      var step4b = rules.reduce(step4a, '/right');
      return step4b;
    },
    comment: ('Proves T = [B = B].')
  },

  /**
   * "T" is a theorem.  In the book, T is defined as an instance of
   * eqT.
   */
  t: function() {
    var step1 = rules.eqSelf(T);
    var step2 = rules.eqT(T);
    var step3 = rules.rRight(step2, step1, '');
    return step3;
  },

  // From [A = B] deduce T = [A = B].
  toTIsEquation: {
    action: function(a_b) {
      Y.assertEqn(a_b);
      var step1 = rules.eqT(a_b.locate('/left'));
      var step2 = rules.r(a_b, step1, '/right/right');
      return step2;
    },
    comment: ('From [A = B] deduce T = [A = B].')
  },

  // Prove [F = T] = F.  Number reflects dependencies in the book
  // proof, but this proof needs only simple rules and axiomPNeqNotP.
  r5230FT: {
    action: function() {
      var step1 = rules.axiom('axiomPNeqNotP');
      var step2 = rules.forallInst(step1, F);
      var step3 = rules.useDefinition('not', step2, '/fn');
      var step4 = rules.useDefinition('not', step3, '/arg/right/fn');
      var step5 = rules.rRight(rules.eqT(F), step4, '/right/right');
      var step6 = rules.eqnSwap(step5);
      return step6;
    },
    comment: ('[F = T] = F')
  },

  // Prove [T = F] = F.  Number reflects dependencies in the book
  // proof, but this proof needs only simple rules and axiomPNeqNotP.
  r5230TF: {
    action: function() {
      var step1 = rules.axiom('axiomPNeqNotP');
      var step2 = rules.forallInst(step1, T);
      var step3 = rules.useDefinition('not', step2, '/fn');
      var step4 = rules.useDefinition('not', step3, '/arg/right/fn');
      var step5 = rules.r(rules.r5230FT(), step4, '/right/right');
      var step6 = rules.eqnSwap(step5);
      return step6;
    },
    comment: ('[T = F] = F')
  },

  // [T && T] = T.  Uses no book-specific definitions.
  // Only used in 5212 and book version of 5216.
  r5211: function() {
    var step1 = rules.definition('&&', T);
    var step2 = rules.applyBoth(step1, T);
    var step3 = rules.reduce(step2, '/right');
    return step3;
  },

  // Book version of r5211.
  r5211Book: function() {
    var step1 = rules.instEqn(rules.axiom('axiom1'), lambda(y, T), g);
    var step2a = rules.reduce(step1, '/left/left');
    var step2b = rules.reduce(step2a, '/left/right');
    var step2c = rules.reduce(step2b, '/right/arg/body');
    var step3a = rules.eqT(lambda(x, T));
    var step3b = rules.rRight(rules.defForall(), step3a, '/right/fn');
    var step4 = rules.rRight(step3b, step2c, '/right');
    return step4;
  },

  // T && T.  Uses no book-specific definitions.
  // Used to prove the Cases rule.
  r5212: function() {
    var step1 = rules.rRight(rules.theorem('r5211'),
                             rules.theorem('t'),
                             '/');
    return step1;
  },

  // From theorems A = B and C = D, derives theorem
  // [A = B] && [C = D].  Uses no book-specific definitions.
  // Not used (because 5216 is not used.)
  // Use toTIsEquation there instead of this.
  r5213: function(a_b, c_d) {
    Y.assertEqn(a_b);
    var a = a_b.locate('/left');
    var b = a_b.locate('/right');
    Y.assertEqn(c_d);
    var c = c_d.locate('/left');
    var d = c_d.locate('/right');
    var step1 = rules.eqT(a);
    var step2 = rules.r(a_b, step1, '/right/right');
    var step3 = rules.eqT(c);
    var step4 = rules.r(c_d, step3, '/right/right');
    var step5 = rules.r(step2, rules.theorem('r5212'), '/left');
    var step6 = rules.r(step4, step5, '/right');
    return step6;
  },

  // Target is forall {x : B}, expr is A, which will replace
  // all occurrences of x.  Uses no book-specific definitions,
  // and relies only on theorem "T" and 5200.
  // This is 5215.
  forallInst: {
    action: function(target, expr) {
      Y.assert(target.fn instanceof Y.Var && target.fn.name == 'forall',
               "Must be 'forall': " + target.fn);
      Y.assert(target.arg instanceof Y.Lambda,
               "Must be lambda expression: " + target.arg);
      var step1 = rules.useDefinition('forall', target, '/fn');
      var step2 = rules.applyBoth(step1, expr);
      var step3 = rules.reduce(step2, '/left');
      var step4 = rules.reduce(step3, '/right');
      // Do not use fromTIsA, it depends on this.
      var step5 = rules.r(step4, rules.theorem('t'), '/');
      return step5;
    },
    comment: ('In a "forall", instantiates the bound variable with'
              + ' a given term.')
  },

  // 5216 by the book.  Not used.  Currently uses one nonbook definition.
  andTBook: function(a) {
    var step1 = rules.axiom('axiom1');
    var step2 =
      rules.instEqn(step1, lambda(x, equal(call('&&', T, x), x)), g);
    var step3 = rules.reduce(step2, '/left/left');
    var step4 = rules.reduce(step3, '/left/right');
    var step5 = rules.reduce(step4, '/right/arg/body');
    var step6 = rules.applyBoth(rules.definition('&&', T), F);
    var step7 = rules.reduce(step6, '/right');
    var step8 = rules.r5213(rules.theorem('r5211'), step7);
    var step9 = rules.r(step5, step8, '/');
    var step10 = rules.forallInst(step9, a);
    return step10;
  },

  // 5216, using the definition of "true and".  Not used.
  andT: function(a) {
    var step1 = rules.applyBoth(rules.definition('&&', T), a);
    var step2 = rules.reduce(step1, '/right');
    return step2;
  },

  // Book only.  We use axiomPNeqNotP instead of defining F.
  r5217Book: function() {
    var step1 = rules.instEqn(rules.axiom('axiom1'),
                              lambda(x, equal(T, x)), g);
    var step2a = rules.reduce(step1, '/left/left');
    var step2b = rules.reduce(step2a, '/left/right');
    var step2c = rules.reduce(step2b, '/right/arg/body');
    var step3 = rules.rRight(rules.eqT(T), step2c, '/left/left');
    var step4a = rules.andT(equal(T, F));
    var step4b = rules.r(step4a, step3, '/left');
    var step5a = rules.instEqn(rules.axiom('axiom3'), lambda(x, T), f);
    var step5b = rules.instEqn(step5a, lambda(x, x), g);
    var step6a = rules.reduce(step5b, '/right/arg/body/left');
    var step6b = rules.reduce(step6a, '/right/arg/body/right');
    var step6c = rules.useDefinition('forall',
                                     rules.defFFromBook(),
                                     '/right/fn');
    var step6d = rules.rRight(step6c, step6b, '/left');
    var step7 = rules.rRight(step6d, step4b, '/right');
    return step7;
  },

  // 5217 is the same as 5230TF.
  // [T = F] = F
  // Not used, though previously used in 5218.

  // Given "subFree(T, v, [A = B])" and "subFree(F, v, [A = B])",
  // proves [A = B].  The argument is {v | [A = B]}.
  equationCases: {
    action: function(lexpr) {
      // These first two steps are not really deductions, they
      // just generate the expressions for the cases.
      Y.assert(lexpr instanceof Y.Lambda,
               'equationCases requires anonymous function argument.');
      var caseT = Y.subFree(T, lexpr.bound, lexpr.body);
      var stepT1 = rules.toTIsEquation(caseT);
      var caseF = Y.subFree(F, lexpr.bound, lexpr.body);
      var stepF1 = rules.toTIsEquation(caseF);
      var step2 = rules.r(stepT1, rules.theorem('r5212'), '/left');
      var step3 = rules.r(stepF1, step2, '/right');
      var step4 = rules.instEqn(rules.axiom('axiom1'), lexpr, g);
      var step5 = rules.reduce(step4, '/right/arg/body');
      var step6 = rules.reduce(step5, '/left/right');
      var step7 = rules.reduce(step6, '/left/left');
      var step8 = rules.r(step7, step3, '');
      var step9 = rules.forallInst(step8, lexpr.bound);
      return step9;
    },
    comment: ('Given a function expression of the form {v | A = B},'
              + ' infers (forall {x | A = B}) assuming A = B is proven'
              + ' for the substitutions with v = T and v = F.')
  },

  // 5218: [T = A] = A
  // Stepping stone to universal generalization.
  r5218: {
    action: function(a) {
      var step1 = rules.theorem('r5230TF');
      var step2 = rules.eqT(T);
      var step3 = rules.eqnSwap(step2);
      var step4 = rules.equationCases(lambda(x, equal(equal(T, x), x)));
      var step5 = rules.instEqn(step4, a, x);
      return step5;
    },
    comment: ('For any expression A derives [T = A] = A.')
  },

  // 5219
  toTIsA: {
    action: function(a) {
      var step1 = rules.r5218(a);
      var step2 = rules.rRight(step1, a, '/');
      return step2;
    },
    comment: ('From A derives T = A')
  },

  // also 5219
  fromTIsA: {
    action: function(t_a) {
      Y.assertEqn(t_a);
      var left = t_a.locate('/left');
      Y.assert(left instanceof Y.Var && left.name == 'T',
               'Input should be [T = A]: ' + t_a);
      var a = t_a.locate('/right');
      var step2 = rules.r(rules.r5218(a), t_a, '/');
      return step2;
    },
    comment: ('From T = A derives A')
  },

  // Helper for uGen
  // Derives (forall {v : T}) given a variable v.
  // proved here by extensionality, not using 5206.
  forallT: {
    action: function(v) {
      var step1 = rules.instEqn(rules.axiom('axiom3'), lambda(x, T), f);
      var step2 = rules.instEqn(step1, lambda(v, T), g);
      var step3 = rules.reduce(step2, '/right/arg/body/left');
      var step4 = rules.reduce(step3, '/right/arg/body/right');
      var step5 = rules.useDefinition('forall', step4, '/right/fn');
      var step6 = rules.bindEqn(rules.eqT(T), x);
      var step7 = rules.rRight(step5, step6, '/');
      var fa = rules.definition('forall');
      var step8 = rules.rRight(fa, step7, '/fn');
      return step8;
    },
    comment: ('(forall {v | T}) for any variable v.'
              + ' (Special case of renaming a bound variable.)')
  },

  // 5220.  The variable may be given as a name string, which it
  // converts internally to a variable.
  uGen: {
    action: function(a, v) {
      if (typeof v == 'string') {
        v = new Y.Var(v);
      }
      var step1 = rules.toTIsA(a);
      var step2 = rules.forallT(v);
      var step3 = rules.r(step1, step2, '/arg/body');
      return step3;
    },
    comment: ('Universal Generalization, wrap a theorem A in'
              + ' (forall v A) using the variable of your choice.')
  },

  // 5221 (one variable), in wff B substitute term A for variable v,
  // which may also be a string, which will be converted to a variable.
  sub: {
    action: function(b, a, v) {
      var step1 = rules.uGen(b, v);
      var step2 = rules.forallInst(step1, a);
      return step2;
    },
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.')
  },

  // More like the book's 5221.  For each name in the map (a string),
  // substitutes the expression associated with it in the map, using
  // simultaneous substitution.
  subAll: {
    action: function(b, map) {
      // Collect all the free names in B and in all of the values
      // to be substituted.
      var allNames = b.allNames();
      for (var key in map) {
        var moreFree = map[key].allNames();
        for (var k2 in moreFree) {
          allNames[k2] = true;
        }
      }
      // First change the names of all the variables to be
      // substituted.
      var wff = b;
      var map2 = {};
      for (var name in map) {
        var v = Y.genVar('v', allNames);
        wff = rules.sub(wff, v, name);
        map2[v.name] = map[name];
      }
      // Then substitute for the renamed variables.
      for (var name in map2) {
        wff = rules.sub(wff, map2[name], name);
      }
      return wff;
    },
    comment: ('Substitute in B for each variable named in the map, '
              + 'its value in the map')
  },

  // 5222: Given a variable and WFF, deduce the WFF.  User must prove
  // theorems where T replaces v in A and where F replaces v in A.
  // TODO: Make a version of this that uses equationCases, rename
  //   this to casesBook.
  cases: {
    action: function(v, a) {
      var hyp1 = Y.subFree(T, v, a);
      var step1a = rules.axiom4(call(lambda(v, a), T));
      var step1b = rules.rRight(step1a, hyp1, '');
      var step1c = rules.toTIsA(step1b);
      var hyp2 = Y.subFree(F, v, a);
      var step2a = rules.axiom4(call(lambda(v, a), F));
      var step2b = rules.rRight(step2a, hyp2, '');
      var step2c = rules.toTIsA(step2b);
      // TODO: prove T && T inline.
      var step3 = rules.theorem('r5212');
      var step4a = rules.r(step1c, step3, '/left');
      var step4b = rules.r(step2c, step4a, '/right');
      var step5 = rules.sub(rules.axiom('axiom1'), lambda(v, a), g);
      var step6 = rules.r(step5, step4b, '/');
      var step7a = rules.forallInst(step6, v);
      var step7b = rules.reduce(step7a, '/');
      return step7b;
    },
    comment: ('Prove a theorem by cases given two theorems that'
              + ' show it with T and F.')
  },

  // 5224
  // Given P and P --> Q, derive Q.
  modusPonens: {
    action: function(a, b) {
      var step1 = rules.toTIsA(a);
      var step2 = rules.rRight(step1, b, '/left');
      var step3 = rules.useDefinition('-->', step2, '/fn');
      var step4 = rules.reduce(step3, '');
      return step4;
    },
    comment: ('Modus Ponens.  Given A and A --> B derives B.')
  },

  // Prove [T = F] = F (same as 5217)
  r5230TF_alternate: {
    action: function() {
      var step1 = rules.axiom('axiomTIsNotF');
      var step2 = rules.useDefinition('not', step1, '/fn');
      var step3 = rules.eqnSwap(step2);
      return step3;
    },
    comment: ('[T = F] = F')
  },

  // Prove [F = T] = F
  // Simpler proof when axiomPNeqNotP rather than axiomTIsNotF (above).
  // TODO: Is there a more elegant proof of this?
  r5230FT_alternate: {
    action: function() {
      var step1a = rules.sub(rules.axiom('axiom2'), F, x);
      var step1b = rules.sub(step1a, T, y);
      var step1c = rules.sub(step1b, lambda(x, equal(x, F)), h);
      var step2a = rules.reduce(step1c, '/right/left');
      var step2b = rules.reduce(step2a, '/right/right');
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
      var step13 = rules.reduce(step12, '/right');
      var step14 = rules.r(step3aa, step13, '/right');
      // Then with x = T.
      var step21 = rules.definition('-->', T);
      var step22 = rules.applyBoth(step21, F);
      var step23 = rules.reduce(step22, '/right');
      var step24 = rules.r(rules.definition('not'),
                           rules.axiom('axiomTIsNotF'),
                           '/fn');
      var step25 = rules.r(step24, step23, '/right');
      // Now use the cases rule:
      var step5 = rules.cases(x, equal(call('-->', x, F), equal(x, F)));
      // Then instantiate [F = T] for x.
      var step6 = rules.sub(step5, equal(F, T), x);
      // And use the fact that [F = T] --> F
      var step7 = rules.rRight(step4, step6, '/left');
      var step8 = rules.fromTIsA(step7);
      return step8;
    },
    comment: ('[F = T] = F')
  },

  // [not T] = F
  r5231T: {
    action: function() {
      var step1 = rules.eqSelf(call('not', T));
      var step2 = rules.r(rules.definition('not'), step1, '/right/fn');
      var step3 = rules.r(rules.theorem('r5230FT'), step2, '/right');
      return step3;
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
      return step4;
    },
    comment: ('[not F] = T')
  },

  // Helper for evalBool, not in book.
  // [[F =] = not].
  falseEquals: {
    action: function() {
      return rules.eqnSwap(rules.defNot());
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
      var step4 = rules.reduce(step3, '/left');
      var step5 = rules.r(step4, step1, '/right');
      var step6 = rules.uGen(step5, x);
      var step7 = rules.sub(rules.axiom('axiom3'), equal(T), f);
      var step8 = rules.sub(step7, lambda(x, x), g);
      var step9 = rules.rRight(step8, step6, '');
      return step9;
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
          return result;
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
            result = rules.useDefinition(fn.name, result, '/right' + _path);
          }
        } else if (fn instanceof Y.Lambda) {
          result = rules.reduce(result, '/right' + _path);
        } else {
          Y.assert(false, 'Unexpected expression: ' + target);
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
      var names = wff.freeNames();
      // Not really a loop, just works with the first free (variable!)
      // name returned.
      for (var name in names) {
        if (!Y.isConstant(name)) {
          if (wff instanceof Y.Call && wff.fn instanceof Y.Call
              && wff.fn.fn instanceof Y.Var && wff.fn.fn.name == '=') {
            // WFF is already an equation.
            var step1 = rules.tautology(Y.subFree(T, name, wff));
            var step2 = rules.tautology(Y.subFree(F, name, wff));
            var step3 = rules.equationCases(lambda(new Y.Var(name), wff));
            return step3;
          } else {
            var step1 = rules.tautology(equal(T, Y.subFree(T, name, wff)));
            var step2 = rules.tautology(equal(T, Y.subFree(F, name, wff)));
            var step3 =
              rules.equationCases(lambda(new Y.Var(name), equal(T, wff)));
            return rules.fromTIsA(step3);
          }
        }
      }
      // There are no free variables, evaluate the expression.
      var result = rules.evalBool(wff);
      Y.assert(result.isCall2('=')
               && result.getRight() instanceof Y.Var
               && result.getRight().name == 'T',
               'Not a tautology: ' + result.getLeft());
      return rules.rRight(result, rules.t(), '');
    },
    comment: ('Tautology decider.')
  },

  // Given two statements a and b, proves a && b.
  makeConjunction: {
    action: function(a, b) {
      var stepa = rules.toTIsA(a);
      var stepb = rules.toTIsA(b);
      var step1 = rules.theorem('r5212');
      var step2 = rules.r(stepa, step1, '/left');
      var step3 = rules.r(stepb, step2, '/right');
      return step3;
    },
    comment: ('Given a and b, derive a && b')
  },

  // Any instance of a tautology is a theorem.  This is part
  // of the book's Rule P.
  tautInst: {
    action: function(tautology, map) {
      var step1 = rules.tautology(tautology);
      var step2 = rules.subAll(step1, map);
      return step2;
    },
    comment: ('A substitution instance of a tautology is a theorem.')
  },
  
  // Given a variable v that is not free in wff A, and a wff B, derive
  // ((forall {v | A || B}) --> A || (forall {v | B})).
  r5235: {
    action: function(v, a, b) {
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

      var freeNames = Y.merge(a.freeNames(), b.freeNames());
      freeNames[v.name] = true;
      var p0 = Y.genVar('p', freeNames);
      var wff = implies(call('forall', lambda(v, call('||', p0, b))),
                        call('||', p0, call('forall', lambda(v, b))));
      var step9 = rules.cases(p0, wff);
      var step10 = rules.sub(step9, a, p0);
      return step10;
    },
    comment: ('Move "forall" inside an "or" when variable not free '
              + 'in the left argument of the "or".')
  },

  // 5237
  implyForall: {
    action: function(v, a, b) {
      var step1 = rules.r5235(v, call('not', a), b);
      var taut = equal(call('||', call('not', p), q), implies(p, q));
      var step2 = rules.tautInst(taut, {p: a, q: b});
      var step3 = rules.r(step2, step1, '/left/arg/body');
      var map4 = {
        p: a,
        q: step1.locate('/right/right')
      };
      var step4 = rules.tautInst(taut, map4);
      var step5 = rules.r(step4, step3, '/right');
      return step5;
    },
    comment: ('Move "forall" inside "implies" provided the variable '
              + 'is not free in the first argument.')
  },
    
  // Rule P (without hypotheses).
  // This handles two antecedents.  If there are more than two,
  // use repeated applications.  The given tautology must match
  // ((A1 && A2) --> B, where B is the desired conclusion.
  // To use more than two antecedents, use this with a1 as one antecedent
  // and combine the rest with makeConjunction.
  // the rest.
  //
  // 5234
  p: {
    action: function(a1, a2, b, tautology) {
      var step2 = rules.makeConjunction(a1, a2);
      var step1 = rules.tautology(tautology);
      var tautologous = implies(step2, b);
      var substitution = Y.matchAsSchema(tautology, tautologous);
      var step3 = rules.subAll(step1, substitution);
      var step4 = rules.modusPonens(step2, step3);
      return step4;
    },
    comment: ('Simplified form of Rule P without hypotheses.')
  },

  r5238a: {
    action: function(v, a, b) {
      if (typeof v == 'string') {
        v = _var(v);
      }
      var step1 = rules.axiom('axiom3');
      var step2 = rules.changeVar(step1, '/right/arg', v);
      var step3 = rules.subAll(step2,
                               ({f: lambda(v, a),
                                 g: lambda(v, b)}));
      var step4 = rules.reduce(step3, '/right/arg/body/left');
      var step5 = rules.reduce(step4, '/right/arg/body/right');
      return step5;
    },
    comment: ('')
  },

  r5238: {
    action: function(vars, a, b) {
      Y.assert(vars.concat, 'Variables must be an array');
      if (vars.length == 0) {
        return rules.eqSelf(equal(a, b));
      } else if (vars.length == 1) {
        return rules.r5238a(vars[0], a, b);
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
        return step3;
      }
    },
    comment: ('Equal functions equate to equal expression values.')
  },

  // 5239, closely following the description and names in the book.
  r5239: {
    action: function(equation, target, path) {
      path = Y.path(path);
      if (!equation.isCall2('=')) {
        throw new Error('Expecting an equation, got: ' + equation);
      }
      var step1 = rules.axiom('axiom2');
      var a = equation.getLeft();
      var b = equation.getRight();
      // Should we subtract out the ones not free in A = B?
      var boundNames = target.boundNames(path);
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
      var step2 = rules.subAll(step1,
                               ({x: aBound, y: bBound, h: lambda(t, g)}));
      var step3 = rules.reduce(step2, '/right/left');
      var step4 = step3;
      for (var i = 0; i < boundNameList.length; i++) {
        step4 = rules.reduce(step4, '/right/left/body/right');
      }
      var step5 = rules.reduce(step4, '/right/right');
      var step6 = step5;
      for (var i = 0; i < boundNameList.length; i++) {
        step6 = rules.reduce(step6, '/right/right/body/right');
      }
      if (boundNameList.length == 0) {
        return step6;
      }
      var step7 = rules.r5238(boundNameList, a, b);
      var step8 = rules.r(step7, step6, '/left');
      return step8;
    },
    comment: ('Analog to Rule R, expressed as an implication.')
  },

  // Like Rule R', based on 5240 (the Deduction Theorem).  The path is
  // relative to the right side of C (the right side of h_c).  The
  // proof here is a subset of the proof of 5240.
  //
  // For convenience applies rule R directly if the equation is really
  // an equation and not an implication.
  replace: {
    action: function(h_equation, h_c, path) {
      var assert = Y.assert;
      if (h_equation.isCall2('=')) {
        // Allow "replace" to be used for situations where "r"
        // is applicable.
        return rules.r(h_equation, h_c, path);
      }
      assert(h_c.isCall2('-->') || h_c.isCall2('|-'),
              'Not an implication: ' + h_c);
      assert(h_equation.isCall2('-->'), 'Not an implication: ' + h_equation);
      var h = h_c.getLeft();
      assert(h.matches(h_equation.getLeft()), 'Differing hypotheses: ' + h);
      var equation = h_equation.getRight();
      assert(equation.isCall2('='), 'Expecting an equation, got: ' + equation);
      var c = h_c.getRight();
      var a = equation.getLeft();
      var b = equation.getRight();
      // Should we subtract out the ones not free in A = B?
      var boundNames = c.boundNames(path);
      var hypFreeNames = h.freeNames();
      // Check ahead of time that the variables are OK.
      // TODO: Do appropriate checking in 5235 and impliesForall as well.
      for (var name in boundNames) {
        if (hypFreeNames[name]) {
          throw new Error('Variable ' + name + ' cannot be free in ' + h);
        }
      }
      var step1 = h_equation;
      for (var name in boundNames) {
        step1 = rules.implyForall(name, h, equation);
      }
      var step2 = rules.r5239(equation, c, path);
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
      return step4;
    },
    comment: ("Analog to the deduction theorem, replacing an equation "
              + "that is true conditionally.")
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
    var step2a = rules.reduce(step1, '/right');
    var step2b = rules.applyBoth(step2a, F);
    var step2c = rules.reduce(step2b, '/right');
    var step3 = rules.instEqn(a3, step2c.locate('/right/left'), f);
    var step4 = rules.instEqn(step3, step2c.locate('/right/right'), g);
    var step5 = rules.reduce(step4, '/right/arg/body/left');
    var step6 = rules.reduce(step5, '/right/arg/body/right');
    var step7 = rules.applyBoth(fa, step6.locate('/right/arg'));
    var step8 = rules.instEqn(a3, step7.locate('/right/left'), f);
    var step9 = rules.instEqn(step8, step7.locate('/right/right'), g);
    var step10 = rules.reduce(step9, '/right/arg/body/left');
    var step11 = rules.reduce(step10, '/right/arg/body/right');
    var step12 = rules.r5218(step11.locate('/right/arg/body/right'));
    var step13 = rules.r(step12, step11, '/right/arg/body');
    return step13;
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
// Derivation from hypotheses
Y.define('|-', _var('-->'));

// Add the axioms and theorems to the "database".  This can only
// include ones that are not "axiom schemas", i.e. not parameterized.
// Most of these axioms really have type parameters.  Ideally axiom
// and theorem schemas will be able to stay, but the details remain
// to be determined.

var axiomNames = ['axiom1', 'axiom2', 'axiom3', 'axiom5', 'axiomPNeqNotP'];

var theoremNames =
  (axiomNames.concat(['defForall', 'defFFromBook', 'axiomTIsNotF',
                      'defNot', 'defAnd',
                      'boolFnsEqual',
                      'r5211', 't', 'r5212', 'r5223', 'r5230TF', 'r5230FT',
                      'r5231T', 'r5231F', 'falseEquals', 'trueEquals',
                      'rulePTautology', 'rulePTautology2']));

for (var i = 0; i < theoremNames.length; i++) {
  Y.addTheorem(theoremNames[i]);
}


//// Export public names.

Y.axiomNames = axiomNames;
Y.theoremNames = theoremNames;

// For testing.
Y.ruleInfo = ruleInfo;

}, '0.1', {requires: ['array-extras', 'expr', 'proof']});
