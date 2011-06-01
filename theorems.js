// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('theorems', function(Y) {


//// THEOREMS AND RULES

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

var identity = lambda(x, x);

var allT = lambda(x, T);

// Map from inference rule name to a JavaScript function that
// implements it.  The functions may use a global variable
// named "rules" that should have all of these functions in it,
// wrapped with code that manages the inference stack for
// Y.makeInference.
//
// TODO: Extend this information to include more than the name and
// function, for example a brief caption, a schema for WFF produced.
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
   * the equation's LHS.
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
      } else {
        throw new Error('Rule R requires equation: ' + equation);
      }
    },
    comment: ('Replace an occurrence of an expression with something'
              + ' always equal to it.')
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
    comment: ('Replace an occurrence of an expression with something'
              + ' always equal to it, but replace the right side'
              + ' of the equation with its left side.')
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
    action: function(app) {
      if (app instanceof Y.Call && app.fn instanceof Y.Lambda) {
        var lambdaExpr = app.fn;
        return equal(app,
                     Y.subFree(app.arg, lambdaExpr.bound, lambdaExpr.body));
      } else {
        throw new Error('Axiom 4 needs ({X : B} A), got: ' + app.toString());
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

  defForall: function() {
    return equal('forall', equal(lambda(x, T)));
  },

  // Definition of F, for book-style proofs.
  defFFromBook: function() {
    return equal(F, call('forall', lambda(x, x)));
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

  /*
  // Generalizes axiomTIsNotF.
  // Rewrite to F = [p = [not p]], instantiate p, expand "not":
  // 1. F = [F = [F = F]], so 2. F = [F = T] (r5230FT)
  // 3. F = [T = [F = T]], so F = [T = F] (r5230TF) by
  // Rule R on r5230FT and step 3.
  axiomPNeqNotP: {
    action: function() {
      return call('forall', lambda(p, call('not', equal(p, call('not', p)))));
    },
    comment: ('')
  },
  */

  defNot: function() {
    return equal('not', equal(F));
  },

  // Book only.
  defAnd: function() {
    return equal('&&', lambda(x, lambda(y, equal(lambda(g, call(g, T, T)),
                                                 lambda(g, call(g, x, y))))));
  },

  axioms: function() {
    rules.axiom('axiom1');
    rules.axiom('axiom2');
    rules.axiom('axiom3');
    return rules.axiom('axiom5');
  },

  definitions: function() {
    rules.definition('not');
    rules.definition('forall');
    rules.definition('&&', T);
    rules.definition('&&', F);
    rules.definition('||', T);
    rules.definition('||', F);
    rules.definition('-->', T);
    return rules.definition('-->', F);
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
    comment: 'A thing is always equal to itself.'
  },

  // r5201a
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

  // r5201d
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
    comment: 'Given f = g, derive (f A) = (g A)'
  },

  // r5201f
  applyToBoth: {
    action: function(a, bc) {
      var abab = rules.eqSelf(call(a, bc.getLeft()));
      var abac = rules.r(bc, abab, '/right/arg');
      return(abac);
    },
    comment: 'Given B = C derives (f B) = (f C)'
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
    comment: ('Substitutes an actual argument for the formal variable'
              + ' in one function call of a WFF.')
  },

  /**
   * From an equation, infers a similar equation with each
   * side wrapped in a binding of the given variable.
   */
  bindEqn: {
    action: function(eqn, v) {
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
    comment: ('In an equation, instantiates the free variable'
              + ' of your choice with an expression.')
  },

  // thm: T = [B = B] (5210)
  eqT: {
    action: function(b) {
      var a3 = rules.r(rules.defForall(), rules.axiom('axiom3'), '/right/fn');
      var identity = lambda(y, y);
      var step1a = rules.instEqn(a3, identity, f);
      var step1b = rules.instEqn(step1a, identity, g);
      var step2a = rules.eqSelf(identity);
      // Eliminate the LHS of step2a:
      var step2b = rules.r(step1b, step2a, '/');
      var step2c = rules.reduce(step2b, '/right/body/left');
      var step2d = rules.reduce(step2c, '/right/body/right');
      var step3 = rules.applyBoth(step2d, b);
      var step4a = rules.reduce(step3, '/left');
      var step4b = rules.reduce(step4a, '/right');
      return step4b;
    },
    comment: ('Given any expression B, proves T = [B = B].')
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

  // Target is forall {x : B}, expr is A, which will replace
  // all occurrences of x.  Uses no book-specific definitions,
  // and relies only on rule "T" and 5200.
  // This is 5215.
  forallInst: {
    action: function(target, expr) {
      Y.assert(target.fn instanceof Y.Var && target.fn.name == 'forall',
               "Must be 'forall': " + target.fn);
      Y.assert(target.arg instanceof Y.Lambda,
               "Must be lambda expression: " + target.arg);
      var step1 = rules.r(rules.defForall(), target, '/fn');
      var step2 = rules.applyBoth(step1, expr);
      var step3 = rules.reduce(step2, '/left');
      var step4 = rules.reduce(step3, '/right');
      var step5 = rules.r(step4, rules.t(), '/');
      return step5;
    },
    comment: ('In a "forall", instantiates the bound variable with'
              + 'the term of your choice.')
  },

  // [T && T] = T.  Uses no book-specific definitions.
  // TODO: Consider proving this from the definition of "true and".
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

  // From [A = B] deduce T = [A = B].  Use instead of 5213.
  eqnIsTrue: {
    action: function(a_b) {
      Y.assertEqn(a_b);
      var step1 = rules.eqT(a_b.locate('/left'));
      var step2 = rules.r(a_b, step1, '/right/right');
      return step2;
    },
    comment: ('From [A = B] deduce T = [A = B].')
  },

  // From theorems A = B and C = D, derives theorem
  // [A = B] = [C = D].  Uses no book-specific definitions.
  // Only used in 5218 (5216  is not used.)
  // Use eqnIsTrue there instead of this.
  // TODO: remove.
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
    // TODO: Use eqnIsTrue instead.
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
    var step6c = rules.r(rules.definition('forall'),
                         rules.defFFromBook(),
                         '/right/fn');
    var step6d = rules.rRight(step6c, step6b, '/left');
    var step7 = rules.rRight(step6d, step4b, '/right');
    return step7;
  },

  // 5217 is the same as 5230TF.

  // [T = F] = F
  // Not used, though previously used in 5218.


  // 5218: [T = A] = A
  // Stepping stone to universal generalization.
  r5218: {
    action: function(a) {
      var step1 = rules.instEqn(rules.axiom('axiom1'),
                                lambda(x, equal(equal(T, x), x)),
                                g);
      var step2 = rules.reduce(step1, '/left/left');
      var step3 = rules.reduce(step2, '/left/right');
      var step4 = rules.reduce(step3, '/right/arg/body');
      var step5a = rules.eqT(T);
      var step5 = rules.eqnSwap(step5a);
      var step6a = rules.r(rules.definition('not'),
                           rules.axiom('axiomTIsNotF'),
                           '/fn');
      var step6 = rules.eqnSwap(step6a);
      // TODO: Use eqnIsTrue instead of 5213.
      var step7 = rules.r5213(step5, step6);
      var step8 = rules.r(step4, step7, '/');
      var step9 = rules.forallInst(step8, a);
      return step9;
    },
    comment: ('For any expression A, [T = A] = A.'
              + ' Stepping stone to universal generalization.')
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

  // 5220, proved here by extensionality, not using 5206.
  uGen: {
    action: function(a, v) {
      var step1 = rules.bindEqn(rules.eqT(T), x);
      var step2 = rules.instEqn(rules.axiom('axiom3'), lambda(v, T), g);
      var step3 = rules.instEqn(step2, lambda(x, T), f);
      var step4 = rules.reduce(step3, '/right/arg/body/left');
      var step5 = rules.reduce(step4, '/right/arg/body/right');
      var step6 = rules.r(rules.definition('forall'), step5, '/right/fn');
      var step7 = rules.rRight(step6, step1, '/');
      var step8 = rules.rRight(rules.definition('forall'), step7, '/fn');
      var step9 = rules.toTIsA(a);
      var step10 = rules.r(step9, step8, '/arg/body');
      return step10;
    },
    comment: ('Universal Generalization, wrap a theorem A in'
              + ' (forall v A) using the variable of your choice.')
  },

  // 5221 (one variable), in B substitute A for v.
  sub: {
    action: function(b, a, v) {
      var step1 = rules.uGen(b, v);
      var step2 = rules.forallInst(step1, a);
      return step2;
    },
    comment: ('In a theorem substitute an expression for'
              + ' all occurrences of a free variable.')
  },

  // 5222: Given a variable and WFF, deduce the WFF.  User must prove
  // theorems where T replaces v in A and where F replaces v in A.
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

  // [[T --> x] --> x].  Only used in Modus Ponens.
  r5223: function() {
    var step1 = rules.applyBoth(rules.definition('-->', T), x);
    var step2 = rules.reduce(step1, '/right');
    return step2;
  },

  // 5224
  modusPonens: {
    action: function(a, b) {
      var step2a = rules.toTIsA(a);
      var step2b = rules.eqnSwap(step2a);
      var step3 = rules.r(step2b, call('-->', a, b), '/left');
      var step4a = rules.sub(rules.theorem('r5223'), b, x);
      var step4b = rules.r(step4a, step3, '/');
      return step4b;
    },
    comment: ('Modus Ponens.  Given A and A --> B derives B.')
  },

  // Prove [T = F] = F (same as 5217)
  r5230TF: {
    action: function() {
      var step1 = rules.axiom('axiomTIsNotF');
      var step2 = rules.r(rules.definition('not'), step1, '/fn');
      var step3 = rules.eqnSwap(step2);
      return step3;
    },
    comment: ('[T = F] = F')
  },

  // Prove [F = T] = F
  // TODO: Is there a more elegant proof of this?
  r5230FT: {
    action: function() {
      var step1a = rules.sub(rules.axiom('axiom2'), F, x);
      var step1b = rules.sub(step1a, T, y);
      var step1c = rules.sub(step1b, lambda(x, equal(x, F)), h);
      var step2a = rules.reduce(step1c, '/right/left');
      var step2b = rules.reduce(step2a, '/right/right');
      var step3a = rules.r(rules.eqnSwap(rules.eqT(F)), step2b, '/right/left');
      var step3b = rules.r(rules.r5218(F), step3a, '/right/right');
      var step3c = rules.r(rules.r5218(F), step3b, '/right');
      var step4 = rules.toTIsA(step3c);
      // We are going to prove the cases of: (x --> F) = (x = F)
      // First with x = F.
      var step11 = rules.definition('-->', F);
      var step12 = rules.applyBoth(step11, F);
      var step13 = rules.reduce(step12, '/right');
      var step14 = rules.eqT(F);
      var step15 = rules.r(step14, step13, '/right');
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
  evalBool: {
    action: function(expr) {
      var boolOps = {'&&': true, '||': true, '-->': true, '=': true, not: true};
      function isReducible(expr) {
        return ((expr instanceof Y.Call && expr.arg instanceof Y.Var)
                && (expr.arg.name == 'T' || expr.arg.name == 'F')
                && (expr.fn instanceof Y.Lambda
                    || (expr.fn instanceof Y.Var && boolOps[expr.fn.name])));
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
          } else if (fn.name == '=') {
            defn = rules.theorem(target.arg.name == 'T'
                                 ? 'trueEquals'
                                 : 'falseEquals');
          } else {
            defn = rules.definition(fn.name, target.arg.name);
          }
          result = rules.r(defn, result, '/right' + _path);
        } else if (fn instanceof Y.Lambda) {
          result = rules.reduce(result, '/right' + _path);
        } else {
          Y.assert(false, 'Unexpected expression: ' + target);
        }
      }
    },
    comment: ('Evaluates a boolean expression with no free variables.')
  },

  // Not in book.  Applies both sides of a function definition to an
  // expression, then reduce the RHS of the result (expected to be a
  // call to a lambda).  A bit like Lisp "apply".  Not used (yet).
  applyFunc: {
    action: function(defn, expr) {
      var step1 = rules.applyBoth(defn, expr);
      var step2 = rules.reduce(step1, '/right');
      return step2;
    },
    comment: ('')
  },

  // Proves an inference that the wff is a tautology and
  // returns it.  Checks that it is indeed proven to be a
  // tautology.  5233
  tautology: {
    action: function(wff) {
      var names = wff.freeNames();
      var constants = {T: true, F: true, not: true, '=': true,
                       '&&': true, '||': true, '-->': true};
      // Not really a loop, just works with the first free (variable!)
      // name returned.
      for (var name in names) {
        if (!constants[name]) {
          var step1 = rules.tautology(Y.subFree(T, name, wff));
          var step2 = rules.tautology(Y.subFree(F, name, wff));
          return rules.cases(new Y.Var(name), wff);
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

};  // End of theorems


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

var theoremNames = ['axiom1', 'axiom2', 'axiom3', 'axiom5',
                    'defForall', 'defFFromBook', 'axiomTIsNotF',
                    /* 'axiomPNeqNotP', */ 'defNot', 'defAnd',
                    'r5211', 't', 'r5212', 'r5223', 'r5230TF', 'r5230FT',
                    'r5231T', 'r5231F', 'falseEquals', 'trueEquals'];

for (var i = 0; i < theoremNames.length; i++) {
  Y.addTheorem(theoremNames[i], Y.makeInference(theoremNames[i]));
}


//// Export public names.

// For testing.
Y.ruleInfo = ruleInfo;
Y.theorems = theoremNames;

}, '0.1', {use: ['array-extras', 'expr', 'proof']});
