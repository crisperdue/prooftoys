// Copyright 2011 Crispin Perdue.  All rights reserved.

YUI.add('proof', function(Y) {

// Import the generally-useful names from "expr" into
// this environment.
Y.Expr.utils.import();

var identity = lambda(x, x);

var allT = lambda(x, T);

/// Rules (public)

// Map from inference rule name to a JavaScript procedure that
// implements it.
var ruleFns = {

  /**
   * The name "TBD" is used in Inferences to indicate that
   * the result of the inference is to be proven.
   */
  TBD: function(assumption) {
    return assumption;
  },

  /**
   * Replace the subexpression of the target at the path with the
   * equation's RHS.  This is rule R.  The subexpression must match
   * the equation's LHS.
   */
  r: function(equation, target, path) {
    path = Y.path(path);
    if (equation.isCall2('=')) {
      function replacer(expr) {
        if (expr.matches(equation.getLeft())) {
          return equation.getRight().copy();
        } else {
          assert(false, 'Rule R: subexpression ' + expr +
                        '\n of ' + target +
                        '\n must match ' + equation.getLeft());
        }
      }
      var result = target.replace(path, replacer);
      return result;
    } else {
      throw new Error('Must be an equation: ' + equation);
    }
  },

  /**
   * Same as Rule R, but replaces an occurrence in target of the right
   * side of the equation with its left side.
   */
  rRight: function(equation, target, path) {
    path = Y.path(path);
    var rev = rules.eqnSwap(equation);
    return rules.r(rev, target, path);
  },

  axiom1: function() {
    return equal(call('&&', call(g, T), call(g, F)),
                 call('forall', lambda(x, call(g, x))));
  },

  // (--> (= x y) (= (h x) (h y)))
  axiom2: function() {
    return call('-->', equal(x, y), equal(call(h, x), call(h, y)));
  },

  // (= (= f g) (= {x : T} {x : (= (f x) (g x))}))
  axiom3: function() {
    return equal(equal(f, g),
                 call('forall',
                      lambda(x, equal(call(f, x), call(g, x)))));
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: function(app) {
    if (app instanceof Y.Call && app.fn instanceof Y.Lambda) {
      var lambdaExpr = app.fn;
      return equal(app,
                   Y.subFree(app.arg, lambdaExpr.bound, lambdaExpr.body));
    } else {
      throw new Error('Axiom 4 needs ({X : B} A), got: ' + app.toString());
    }
  },

  axiom5: function() {
    return equal(call('the', equal(y)), y);
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
  axiomTIsNotF: function() {
    return call('not', equal(T, F));
  },

  /*
  // Can replace axiomTIsNotF; generalization of it.
  // Can we simplify this to omit the "forall"?  Specifically,
  // can we instantiate it without using universal generalization?
  // See 5218, which depends on this.
  axiomPNeqNotP: function() {
    return call('forall', lambda(p, call('not', equal(p, call('not', p)))));
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

  // These definitions by cases need to have the RHS be
  // a Lambda or somehow by further reducible by evalBool
  // for evalBool to work as intended.

  // Note this can be proved like 5211.
  defTrueAnd: function() {
    return equal(call('&&', T), identity);
  },

  defFalseAnd: function() {
    return equal(call('&&', F), lambda(x, F));
  },

  defTrueOr: function() {
    return equal(call('||', T), allT);
  },

  defFalseOr: function() {
    return equal(call('||', F), identity);
  },

  defTrueImplies: function() {
    return equal(call('-->', T), identity);
  },

  defFalseImplies: function() {
    return equal(call('-->', F), allT);
  },

  //
  // Theorems and rules of inference.
  //

  // Takes an arbitrary expression A, concluding that it is equal
  // to itself. (5200)
  eqSelf: function(a) {
    var step1 = rules.axiom4(call(lambda(x, x), a));
    return rules.r(step1, step1, '/left');
  },

  // r5201a
  replaceWhole: function(a, ab) {
    var aa = rules.eqSelf(a);
    var b = ab.getRight();
    var result = rules.r(ab, a, '/');
    return result;
  },

  // r5201b
  eqnSwap: function(ab) {
    var a = ab.getLeft();
    var aa = rules.eqSelf(a);
    var ba = rules.r(ab, aa, '/left');
    return ba;
  },

  // r5201c
  eqnChain: function(ab, bc) {
    var ac = rules.r(bc, ab, '/right');
    return ac;
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
  applyBoth: function(eqn, a) {
    var step1 = rules.eqSelf(call(eqn.locate('/left'), a));
    var step2 = rules.r(eqn, step1, '/right/fn');
    return step2;
  },

  // r5201f
  applyToBoth: function(a, bc) {
    var abab = rules.eqSelf(call(a, bc.getLeft()));
    var abac = rules.r(bc, abab, '/right/arg');
    return(abac);
  },

  /**
   * Beta-reduce an application of a lambda expression to an argument,
   * with the subexpression identified by a path (within a theorem).
   * Rule R packaged for convenience.
   */
  reduce: function(expr, path) {
    path = Y.path(path);
    var target = expr.locate(path);
    assert(target, 'Path ' + path + ' not found in ' + target);
    assert(target instanceof Y.Call && target.fn instanceof Y.Lambda,
           'Reduce needs a call to a lambda, got: ' + target);
    var equation = rules.axiom4(target);
    var result = rules.r(equation, expr, path);
    return result;
  },

  /**
   * From an equation, infers a similar equation with each
   * side wrapped in a binding of the given variable.
   */
  bindEqn: function(eqn, v) {
    assert(eqn.isBinOp() && eqn.getBinOp() == '=',
           'Not an equation: ' + eqn);
    assert(v instanceof Y.Var, 'Not a variable: ' + v);
    var step1 = rules.eqSelf(lambda(v, eqn.getLeft()));
    var step2 = rules.r(eqn, step1, '/right/body');
    return step2;
  },

  /**
   * Substitutes term "a" for variable "v" in equation b_c,
   * with the result a consequence of b_c.  (5209)
   * TODO: Should this use bindEqn?
   */
  instEqn: function(b_c, a, v) {
    var b = b_c.getLeft();
    var c = b_c.getRight();
    var ba_ba = rules.eqSelf(call(lambda(v, b), a));
    var ba_ca = rules.r(b_c, ba_ba, '/right/fn/body');
    var ba_sab = rules.axiom4(call(lambda(v, b), a));
    var ca_sac = rules.axiom4(call(lambda(v, c), a));
    var step5a = rules.r(ba_sab, ba_ca, '/left');
    var step5b = rules.r(ca_sac, step5a, '/right');
    return step5b;
  },

  // thm: T = [B = B] (5210)
  eqT: function(b) {
    var a3 = rules.r(rules.defForall(), rules.axiom3(), '/right/fn');
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

  /**
   * "T" is a theorem.  In the book, T is defined as an instance of
   * eqT.
   */
  t: function() {
    var step1 = rules.eqSelf(T);
    var step2 = rules.eqT(T);
    var step3 = rules.rRight(step2, step1, '/');
    return step3;
  },

  // Target is forall {x : B}, expr is A, which will replace
  // all occurrences of x.  Uses no book-specific definitions,
  // and relies only on rule "T" and 5200.
  // This is 5215.
  forallInst: function(target, expr) {
    assert(target.fn instanceof Y.Var && target.fn.name == 'forall',
           "Must be 'forall': " + target.fn);
    assert(target.arg instanceof Y.Lambda,
           "Must be lambda expression: " + target.arg);
    var step1 = rules.r(rules.defForall(), target, '/fn');
    var step2 = rules.applyBoth(step1, expr);
    var step3 = rules.reduce(step2, '/left');
    var step4 = rules.reduce(step3, '/right');
    var step5 = rules.r(step4, rules.t(), '/');
    return step5;
  },

  // [T && T] = T.  Uses no book-specific definitions.
  // TODO: Consider proving this from defTrueAnd.
  // Only used in 5212 and book version of 5216.
  r5211: function() {
    var step1 = rules.instEqn(rules.axiom1(), lambda(y, T), g);
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
    var step1 = rules.rRight(rules.r5211(), rules.t(), '/');
    return step1;
  },

  // From [A = B] deduce T = [A = B].  Use instead of 5213.
  eqnIsTrue: function(a_b) {
    assertEqn(a_b);
    var step1 = rules.eqT(a_b.locate('/left'));
    var step2 = rules.r(a_b, step1, '/right/right');
    return step2;
  },

  // From theorems A = B and C = D, derives theorem
  // [A = B] = [C = D].  Uses no book-specific definitions.
  // Only used in 5218 (5216  is not used.)
  // Use eqnIsTrue there instead of this.
  // TODO: remove.
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
    var step5 = rules.r(step2, rules.r5212(), '/left');
    var step6 = rules.r(step4, step5, '/right');
    return step6;
  },

  // 5216 by the book.  Not used.
  andTBook: function(a) {
    var step1 = rules.axiom1();
    var step2 =
      rules.instEqn(step1, lambda(x, equal(call('&&', T, x), x)), g);
    var step3 = rules.reduce(step2, '/left/left');
    var step4 = rules.reduce(step3, '/left/right');
    var step5 = rules.reduce(step4, '/right/arg/body');
    var step6 = rules.applyBoth(rules.defTrueAnd(), F);
    var step7 = rules.reduce(step6, '/right');
    // TODO: Use eqnIsTrue instead.
    var step8 = rules.r5213(rules.r5211(), step7);
    var step9 = rules.r(step5, step8, '/');
    var step10 = rules.forallInst(step9, a);
    return step10;
  },

  // 5216, using defTrueAnd.  Not used.
  andT: function(a) {
    var step1 = rules.applyBoth(rules.defTrueAnd(), a);
    var step2 = rules.reduce(step1, '/right');
    return step2;
  },

  // Book only.  We use axiomPNeqNotP instead of defining F.
  r5217Book: function() {
    var step1 = rules.instEqn(rules.axiom1(), lambda(x, equal(T, x)), g);
    var step2a = rules.reduce(step1, '/left/left');
    var step2b = rules.reduce(step2a, '/left/right');
    var step2c = rules.reduce(step2b, '/right/arg/body');
    var step3 = rules.rRight(rules.eqT(T), step2c, '/left/left');
    var step4a = rules.andT(equal(T, F));
    var step4b = rules.r(step4a, step3, '/left');
    var step5a = rules.instEqn(rules.axiom3(), lambda(x, T), f);
    var step5b = rules.instEqn(step5a, lambda(x, x), g);
    var step6a = rules.reduce(step5b, '/right/arg/body/left');
    var step6b = rules.reduce(step6a, '/right/arg/body/right');
    var step6c = rules.r(rules.defForall(), rules.defFFromBook(), '/right/fn');
    var step6d = rules.rRight(step6c, step6b, '/left');
    var step7 = rules.rRight(step6d, step4b, '/right');
    return step7;
  },

  // 5217 is the same as 5230TF.

  // [T = F] = F
  // Not used, though previously used in 5218.


  // 5218: [T = A] = A
  // Stepping stone to universal generalization.
  r5218: function(a) {
    var step1 = rules.instEqn(rules.axiom1(),
                              lambda(x, equal(equal(T, x), x)),
                              g);
    var step2 = rules.reduce(step1, '/left/left');
    var step3 = rules.reduce(step2, '/left/right');
    var step4 = rules.reduce(step3, '/right/arg/body');
    var step5a = rules.eqT(T);
    var step5 = rules.eqnSwap(step5a);
    var step6a = rules.r(rules.defNot(), rules.axiomTIsNotF(), '/fn');
    var step6 = rules.eqnSwap(step6a);
    // TODO: Use eqnIsTrue instead of 5213.
    var step7 = rules.r5213(step5, step6);
    var step8 = rules.r(step4, step7, '/');
    var step9 = rules.forallInst(step8, a);
    return step9;
  },

  // 5219
  toTIsA: function(a) {
    var step1 = rules.r5218(a);
    var step2 = rules.rRight(step1, a, '/');
    return step2;
  },

  // also 5219
  fromTIsA: function(t_a) {
    assertEqn(t_a);
    var left = t_a.locate('/left');
    assert(left instanceof Y.Var && left.name == 'T',
           'Input should be [T = A]: ' + t_a);
    var a = t_a.locate('/right');
    var step2 = rules.r(rules.r5218(a), t_a, '/');
    return step2;
  },

  // 5220, proved here by extensionality, not using 5206.
  uGen: function(a, v) {
    var step1 = rules.bindEqn(rules.eqT(T), x);
    var step2 = rules.instEqn(rules.axiom3(), lambda(v, T), g);
    var step3 = rules.instEqn(step2, lambda(x, T), f);
    var step4 = rules.reduce(step3, '/right/arg/body/left');
    var step5 = rules.reduce(step4, '/right/arg/body/right');
    var step6 = rules.r(rules.defForall(), step5, '/right/fn');
    var step7 = rules.rRight(step6, step1, '/');
    var step8 = rules.rRight(rules.defForall(), step7, '/fn');
    var step9 = rules.toTIsA(a);
    var step10 = rules.r(step9, step8, '/arg/body');
    return step10;
  },

  // 5221 (one variable), in B substitute A for v.
  sub: function(b, a, v) {
    var step1 = rules.uGen(b, v);
    var step2 = rules.forallInst(step1, a);
    return step2;
  },

  // 5222: Given a variable and WFF, deduce the WFF.  User must prove
  // theorems where T replaces v in A and where F replaces v in A.
  cases: function(v, a) {
    var hyp1 = Y.subFree(T, v, a);
    var step1a = rules.axiom4(call(lambda(v, a), T));
    var step1b = rules.rRight(step1a, hyp1, '');
    var step1c = rules.toTIsA(step1b);
    var hyp2 = Y.subFree(F, v, a);
    var step2a = rules.axiom4(call(lambda(v, a), F));
    var step2b = rules.rRight(step2a, hyp2, '');
    var step2c = rules.toTIsA(step2b);
    // TODO: prove T && T inline.
    var step3 = rules.r5212();
    var step4a = rules.r(step1c, step3, '/left');
    var step4b = rules.r(step2c, step4a, '/right');
    var step5 = rules.sub(rules.axiom1(), lambda(v, a), g);
    var step6 = rules.r(step5, step4b, '/');
    var step7a = rules.forallInst(step6, v);
    var step7b = rules.reduce(step7a, '/');
    return step7b;
  },

  // [[T --> x] --> x].  Only used in Modus Ponens.
  r5223: function() {
    var step1 = rules.applyBoth(rules.defTrueImplies(), x);
    var step2 = rules.reduce(step1, '/right');
    return step2;
  },

  // 5224
  modusPonens: function(a, b) {
    var step2a = rules.toTIsA(a);
    var step2b = rules.eqnSwap(step2a);
    var step3 = rules.r(step2b, call('-->', a, b), '/left');
    var step4a = rules.sub(rules.r5223(), b, x);
    var step4b = rules.r(step4a, step3, '/');
    return step4b;
  },

  // Prove [T = F] = F (same as 5217)
  r5230TF: function() {
    var step1 = rules.axiomTIsNotF();
    var step2 = rules.r(rules.defNot(), step1, '/fn');
    var step3 = rules.eqnSwap(step2);
    return step3;
  },

  // Prove [F = T] = F
  // TODO: Is there a more elegant proof of this?
  r5230FT: function() {
    var step1a = rules.sub(rules.axiom2(), F, x);
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
    var step11 = rules.defFalseImplies();
    var step12 = rules.applyBoth(step11, F);
    var step13 = rules.reduce(step12, '/right');
    var step14 = rules.eqT(F);
    var step15 = rules.r(step14, step13, '/right');
    // Then with x = T.
    var step21 = rules.defTrueImplies();
    var step22 = rules.applyBoth(step21, F);
    var step23 = rules.reduce(step22, '/right');
    var step24 = rules.r(rules.defNot(), rules.axiomTIsNotF(), '/fn');
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

  // [not T] = F
  r5231T: function() {
    var step1 = rules.eqSelf(call('not', T));
    var step2 = rules.r(rules.defNot(), step1, '/right/fn');
    var step3 = rules.r(rules.r5230FT(), step2, '/right');
    return step3;
  },

  // [not F] = T
  r5231F: function() {
    var step1 = rules.eqSelf(call('not', F));
    var step2 = rules.r(rules.defNot(), step1, '/right/fn');
    var step3 = rules.eqT(F);
    var step4 = rules.rRight(step3, step2, '/right');
    return step4;
  },

  // Helper for evalBool, not in book.
  // [[= F] = not].
  falseEquals: function() {
    return rules.eqnSwap(rules.defNot());
  },

  // Another helper for evalBool, not in book.
  // [[= T] = {x : x}].
  trueEquals: function() {
    var step1 = rules.r5218(x);
    var step2 = rules.eqSelf(x);
    var step3 = rules.applyToBoth(lambda(x, x), step2);
    var step4 = rules.reduce(step3, '/left');
    var step5 = rules.r(step4, step1, '/right');
    var step6 = rules.uGen(step5, x);
    var step7 = rules.sub(rules.axiom3(), equal(T), f);
    var step8 = rules.sub(step7, lambda(x, x), g);
    var step9 = rules.rRight(step8, step6, '');
    return step9;
  },

  // Equates the given expression to a similar one where boolean terms
  // are reduced.  (These are calls to =, &&, ||, -->, or "not", and
  // lambda expressions, with an argument of T or F.)  Reduces
  // repeatedly until no subexpression can be reduced.
  evalBool: function(expr) {
    var boolDefs = {
      '&&': {T: 'defTrueAnd', F: 'defFalseAnd'},
      '||': {T: 'defTrueOr', F: 'defFalseOr'},
      '-->': {T: 'defTrueImplies', F: 'defFalseImplies'},
      '=': {T: 'trueEquals', F: 'falseEquals'},
      not: {T: 'r5231T', F: 'r5231F'}
    };
    function isReducible(expr) {
      return ((expr instanceof Y.Call && expr.arg instanceof Y.Var)
              && (expr.arg.name == 'T' || expr.arg.name == 'F')
              && (expr.fn instanceof Y.Lambda
                  || (expr.fn instanceof Y.Var && boolDefs[expr.fn.name])));
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
        var ruleName = boolDefs[fn.name][target.arg.name];
        result = rules.r(rules[ruleName](), result, '/right' + _path);
      } else if (fn instanceof Y.Lambda) {
        result = rules.reduce(result, '/right' + _path);
      } else {
        assert(false, 'Unexpected expression: ' + target);
      }
    }
  },

  // Not in book.  Applies both sides of a function definition to an
  // expression, then reduce the RHS of the result (expected to be a
  // call to a lambda).  A bit like Lisp "apply".  Not used (yet).
  applyFunc: function(defn, expr) {
    var step1 = rules.applyBoth(defn, expr);
    var step2 = rules.reduce(step1, '/right');
    return step2;
  },

  // Proves an inference that the wff is a tautology and
  // returns it.  Checks that it is indeed proven to be a
  // tautology.  5233
  tautology: function(wff) {
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
    assert(result.isCall2('=')
           && result.getRight() instanceof Y.Var
           && result.getRight().name == 'T',
           'Not a tautology: ' + result.getLeft());
    return rules.rRight(result, rules.t(), '');
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

};

//// Inferences

/**
 * Inference object: Immutable record of an inference step, either
 * primitive or composite.  The constructor is private; use
 * makeInference to create inferences in client code.
 */
function Inference(name, arguments, result, details) {
  // Rule name
  this.name = name;
  // Arguments: a list of expressions or inference steps with result
  // expressions used by this step.  For composite inferences this
  // should be null.
  this.arguments = arguments;
  // The conclusion Expr of the inference..
  this.result = result;
  // List of component steps (Inferences), empty if not composite.
  this.details = details;
}

Inference.prototype.getStepNode = function() {
  return this.result.node.get('parentNode');
}

Inference.prototype.toString = function() {
  var result = debugString(this);
  if (result.length <= 200) {
    return result;
  } else {
    function detailer(details) {
      result = '[';
      for (var i = 0; i < details.length; i++) {
        if (i > 0) {
          result += ', ';
        }
        result += details[i].name;
      }
      return result + ']';
    }
    return debugString(this, {details: detailer});
  }
}

/**
 * Returns a string showing the top-level properties
 * of an object, and their values.
 */
function debugString(o, specials) {
  if (typeof o == 'object') {
    var result = '{';
    for (var key in o) {
      if (o.hasOwnProperty(key)) {
        result += key + ': ';
        var value = o[key];
        var f = specials && specials[key];
        if (f) {
          result += f(value);
        } else if (typeof value == 'string') {
          result += '"' + o[key] + '"';
        } else if (value && value.concat) {
          vString = o[key].toString();
          if (vString.length > 40) {
            result += '[\n';
            for (var i = 0; i < value.length; i++) {
              result += value[i] + '\n';
            }
            result += ']\n';
          } else {
            result += '[' + o[key] + ']';
          }
        } else {
          result += '' + o[key];
        }
        result += ' ';
      }
    }
    return result + '}';
  } else {
    return o.toString();
  }
}

/**
 * Returns a set of printable strings of terms this inference relies
 * on to be true in order to produce its result.
 */
Inference.prototype.assumptions = function() {
  // Databases of input and output expressions of applications of
  // primitive rules, indexed by value as string.
  var inputs  = {};
  var outputs = {};
  // Accumulates the inputs and outputs of this inference.
  function accumulate(inference) {
    // For axioms, definitions, and rule R the result is an output.
    if (inference.name.match(/^axiom|^def[A-Z]/)) {
      outputs[inference.result.asString()] = inference.result;
    }
    if (inference.name == 'r') {
      outputs[inference.result.toString()] = inference.result;
      var args = inference.arguments;
      inputs[args[0].asString()] = true;
      inputs[args[1].asString()] = true;
    } else {
      var details = inference.details;
      for (var i = 0; i < details.length; i++) {
        accumulate(details[i]);
      }
    }
  }
  accumulate(this);
  for (var key in outputs) {
    delete inputs[key];
  }
  return inputs;
};

function renderSteps(inference, node) {
  if (node == null) {
    node = new Y.Node(document.body)
      .appendChild('<div style="margin: 1em; font-family: monospace"></div>');
  }
  node.appendChild('<div style="margin: .5em"><b>'
                   + inference.name + '</b></div>');
  
  var details = inference.details;
  // Map to inference from its result as string.  Each result will
  // be annotated with links into the DOM.
  var allSteps = {};
  for (var i = 0; i < details.length; i++) {
    var inf = details[i];
    var stepNode = node.appendChild('<div class="proofStep"></div>');
    // See appendSpan in expr.js.
    var wffNode = stepNode.appendChild('<span class=expr></span>');
    // Record the annotated expression as the inference result.
    inf.result = inf.result.render(wffNode);
    // Add the name to the display.
    stepNode.appendChild('&nbsp;&nbsp;' + inf.name);
    // Map to inference, from its result expression as string.
    // Represents steps depended on by the inference.
    inf.deps = {};
    var assumptions = inf.assumptions();
    // Remember dependencies between inference steps as we go.
    for (var aString in assumptions) {
      var step = allSteps[aString];
      if (step) {
        inf.deps[aString] = step;
      } else {
        Y.log('No prior step: ' + aString);
      }
    }
    stepNode.on('hover',
                Y.rbind(hover, stepNode, inf, 'in'),
                Y.rbind(hover, stepNode, inf, 'out'));
    allSteps[inf.result.asString()] = inf;
  }
}

/**
 * Event handler for "hover" events.
 */
function hover(event, inference, direction) {
  var op = direction == 'in' ? 'addClass' : 'removeClass';
  var deps = inference.deps;
  var handler = hoverHandlers[inference.name];
  if (handler) {
    handler(inference, op);
  } else {
    this[op]('hover');
    for (var key in deps) {
      deps[key].result.node[op]('dep');
    }
  }
}

var hoverHandlers = {
  r: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var eqn = deps[args[0].asString()].result;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    target.node[op]('hover');
    target.locate(path).node[op]('old');
    inf.getStepNode()[op]('hover');
    inf.result.locate(path).node[op]('new');
    eqn.getLeft().node[op]('old');
    eqn.getRight().node[op]('new');
  },
  rRight: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var eqn = deps[args[0].asString()].result;
    var target = deps[args[1].asString()].result;
    var path = args[2];
    target.node[op]('hover');
    target.locate(path).node[op]('old');
    inf.getStepNode()[op]('hover');
    inf.result.locate(path).node[op]('new');
    eqn.getRight().node[op]('old');
    eqn.getLeft().node[op]('new');
  },
  reduce: function(inf, op) {
    var deps = inf.deps;
    var args = inf.arguments;
    var target = deps[args[0].asString()].result;
    var path = args[1];
    target.node[op]('hover');
    target.locate(path).node[op]('new');
    inf.getStepNode()[op]('hover');
    inf.result.locate(path).node[op]('new');
  }
};

/**
 * Applies the rule with the given name to the arguments,
 * pushing a record of its inference onto the given stack (array),
 * and returning the result of the Inference, an expression.
 * If there no such rule, returns null and has no effect.
 */
function applyRule(name, arguments, stack) {
  // In Java probably implement this with Callables and a method
  // to get the arguments of each.  Each item in rules becomes
  // a Callable.
  //
  // Each rule runs with a new list available for any steps within it.
  assert(typeof name == 'string', 'Name must be a string: ' + name);
  var rule = ruleFns[name];
  assert(rule, 'No such rule: ' + name);
  stack.push([]);
  var result = rule.apply(null, arguments);
  var step = new Inference(name, arguments, result, stack.pop());
  stack[stack.length - 1].push(step);
  return result;
}

/**
 * Makes and returns an inference by running the named rule with the
 * given arguments.
 */
function makeInference(name, arguments) {
  arguments = arguments || [];
  inferenceStack.push([]);
  applyRule(name, arguments, inferenceStack);
  var inf = inferenceStack.pop().pop();
  return inf;
}

// Maybe each set of rules could have its own inference stack???
var inferenceStack = [[]];

// Actual rule functions to call from other code.
var rules = {};

for (var key in ruleFns) {
  (function(k) {
    rules[k] = function() {
      return applyRule(k, arguments, inferenceStack);
    }
  })(key);
};


/// Proof

function Proof() {
  this.steps = [];
}

Proof.prototype.insert = function(step, index) {
  step.index = index;
  var steps = this.steps;
  for (var i = index; i < steps.length; i++) {
    steps[i].index = index;
  }
  steps.splice(index, 0, step);
};


// ProofStep

function ProofStep(proof) {
  this.proof = proof;
  this.index = null;
  this.tactic = null;
  this.inference = null;
  this.deps = [];
}

/**
 * Sets the inference of this step.  The dependencies are a list of
 * ProofSteps this claims to depend on.  The results of those steps
 * should match the assumptions of the new inference, or else this
 * method inserts new steps that make the needed assertions.
 * Making new steps is a policy decision that could change.
 */
ProofStep.prototype.setInference = function(inference, dependencies) {
  this.inference = inference;
  if (inference.name == 'TBD') {
    if (dependencies && dependencies.length > 0) {
      assert(false, 'TBD inference cannot have dependencies');
    }
    return;
  }
  // This will be a set of the dependencies, indexed by the printed
  // string of the result of each one's inference.
  fromDeps = {};
  for (var i = 0; i < dependencies.length; i++) {
    var dep = dependencies[i];
    var result = dep.inference.result;
    fromDeps[result.toString()] = dep;
  }
  this.deps = [];
  var assumptions = inference.assumptions();
  // Connect the inputs needed by this step to other proof steps
  for (var str in assumptions) {
    var assumption = assumptions[str];
    var provided = fromDeps[str];
    if (provided) {
      this.deps.push(dep);
    } else {
      var step = new ProofStep(this.proof);
      step.setInference(new Inference('TBD', [], assumption), []);
      this.proof.insert(step, this.index);
    }
  }
};


//// Internal utility functions

function assert(condition, message) {
  if (!condition) {
    if (typeof message == 'function') {
      message = message();
    }
    console.log(message);
    break_here();
  }
}

function assertEqn(expr) {
  assert(expr instanceof Y.Call
         && expr.fn instanceof Y.Call
         && expr.fn.fn instanceof Y.Var
         && expr.fn.fn.name == '=',
         'Must be an equation: ' + expr);
}


//// Export public names.

Y.rules = rules;
Y.ruleFns = ruleFns;
Y.inferenceStack = inferenceStack;
Y.makeInference = makeInference;
Y.renderSteps = renderSteps;

}, '0.1', {use: ['array-extras', 'expr']});
