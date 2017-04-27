// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

// Set all of this up immediately upon load, but avoiding changes
// to the global environment (except through the "Toy" namespace).
(function() {

//// THEOREMS AND RULES

var rules = Toy.rules;

var assert = Toy.assertTrue;
var check = Toy.check;
var memo = Toy.memo;

//  Make some useful names available here.
var assertEqn = Toy.assertEqn;
var err = Toy.err;
var varify = Toy.varify;
var constify = Toy.constify;
var termify = Toy.termify;
var call = Toy.call;
var equal = Toy.equal;
var implies = Toy.implies;
var lambda = Toy.lambda;

var Expr = Toy.Expr;
var Call = Toy.Call;
var Lambda = Toy.lambda;

// Predefine some common constants.
var T = constify('T');
var F = constify('F');

var convert = Toy.convert;
var applyToVisible = Toy.applyToVisible;

//// Utility functions

/**
 * A simplification function that does nothing, useful as the
 * auto-simplifier for rules that want to suppress simplification.
 */
function noSimplify(step) {
  return step;
}

// Interactive testing in context of this file.
window.Numtest = function(x) {
  setTimeout(function() { console.log(window.Tval = eval(x)); });
};

/**
 * Returns a truthy value iff the term has the form of an arithmetic
 * expression suitable for rules.axiomArithmetic.  This does not do
 * range checks on the values of numeric inputs.  On the other hand it
 * is faster and does not use exceptions.
 */
function isArithmetic(term) {
  if (term.isInfixCall()) {
    var left = term.getLeft();
    var right = term.getRight();
    if (!left.isNumeral() ||
        !right.isNumeral()) {
      return false;
    }
    var op = term.getBinOp().name;
    switch(op) {
    case '+':
    case '*':
    case '-':
    case '=':
    case '!=':
    case '>':
    case '>=':
    case '<':
    case '<=':
      return true;
    case '/':
      if (right === 0) {
        return false;
      }
      var value = left / right;
      // abs(value) <= abs(left) since abs(right) >= 1 so the
      // magnitude is not a problem.  The fractional part of a
      // result must have denominator no greater than MAX_INT,
      // so it should be distinguishable from an integer.
      return value === Math.floor(value);
    default:
      return false;
    }
  } else if (term instanceof Toy.Call) {
    return (term.fn.isConst() && term.arg.isNumeral() &&
            (term.fn.name == 'neg' || term.fn.name == 'R'));
  }
}

/**
 * Has the effect of trying the axiom of arithmetic on the term,
 * returning a falsy value if it does not apply.
 */
function tryArithmetic(term) {
  if (isArithmetic(term)) {
    return Toy.normalReturn(rules.axiomArithmetic, term);
  }
  // Implicit falsy return.
}

/**
 * If the given term (with possible multiplication operator) has
 * a variable "all the way to the right", returns the variable,
 * otherwise null.  Also works with a term of the form (neg <v>).
 *
 * TODO: Consider supporting a term with a denominator.
 */
function termGetRightVariable(term) {
  var s;
  return (term.isVariable()
          ? term
          : (s = term.matchSchema('neg v')) && s.v.isVariable()
          ? s.v
          : ((s = term.matchSchema('f a v')) && 
           s.f.isConst('*') &&
             s.v.isVariable())
          ? s.v
          : null);
}

/**
 * Returns a plain object with a property for each variable name
 * occurring in the given multiplicative term.  The value of each
 * property is the number of occurrences of the variable with that
 * name.  The term must consist entirely of multiplication and
 * negation of variables and constants.  If any other kind of
 * expression occurs in the term, the result is null.
 */
function varFactorCounts(term) {
  var info = {};
  function mustBeVariable(expr, revPath) {
    if (expr.isVariable()) {
      var value = info[expr.name] || 0;
      info[expr.name] = value + 1;
    } else if (!expr.isConst()) {
      throw new Toy.Result(false);
    }
  }
  function addCounts(expr, revPath) {
    expr.walkPatterns([
      {match: 'a * b', a: addCounts, b: addCounts},
      {match: 'neg a', a: addCounts},
      {match: 'a', a: mustBeVariable}
    ]);
    return true;
  }
  return (Toy.catchResult(addCounts, term, null)
          ? info
          : null);
}

/**
 * Returns true iff the multiplicative term e1 belongs strictly to the
 * left of term e2.  Each term must have varFactorCounts, and one must
 * have more of some variable than the other.  This compares variable
 * counts in lexical order by name, stopping at the first count that
 * differs.
 */
function termLeftThan(e1, e2) {
  var counts1 = varFactorCounts(e1);
  var counts2 = varFactorCounts(e2);
  var allKeys =
    Object.keys(jQuery.extend({}, counts1 || {}, counts2 || {})).sort();
  // If either expression does not have clear counts, don't require
  // the terms to be ordered.
  if (counts1 && counts2) {
    for (var i = 0; i < allKeys.length; i++) {
      var key = allKeys[i];
      var count1 = counts1[key] || 0;
      var count2 = counts2[key] || 0;
      if (count1 > count2) {
        return true;
      }
      if (count2 > count1) {
        return false;
      }
    }
  }
  return false;
}


////
//// Inference rules
////

var numbersInfo = {
  //
  // Real numbers
  // 
  // Assumptions (R x) & (R y), etc. are in the form:
  // (A1 => (A2 => <equation>)) to simplify introducing them from
  // the hypotheses.  This is equivalent to A1 & A2 => <equation>.

  axiomCommutativePlus: {
    statement: '@R x & R y => x + y = y + x',
    proof: function() {
      return (rules.assert('R x & R y => x + y = y + x')
              .andThen('asHypotheses'));
    },
    description: 'commutativity'
  },

  axiomAssociativePlus: {
    statement: '@R x & R y & R z => x + (y + z) = (x + y) + z',
    proof: function() {
      return (rules.assert('R x & R y & R z => x + (y + z) = (x + y) + z')
              .andThen('asHypotheses'));
    },
    description: 'associativity'
  },

  axiomCommutativeTimes: {
    statement: '@R x & R y => x * y = y * x',
    proof: function() {
      return (rules.assert('R x & R y => x * y = y * x')
              .andThen('asHypotheses'));
    },
    description: 'commutativity'
  },

  axiomAssociativeTimes: {
    statement: '@R x & R y & R z => x * (y * z) = (x * y) * z',
    proof: function() {
      return (rules.assert('R x & R y & R z => x * (y * z) = (x * y) * z')
              .andThen('asHypotheses'));
    },
    description: 'associativity'
  },

  axiomDistributivity: {
    statement: '@R x & R y & R z => x * (y + z) = x * y + x * z',
    proof: function() {
      return (rules.assert('R x & R y & R z => x * (y + z) = x * y + x * z')
              .andThen('asHypotheses'));
    },
    description: 'distributive law'
  },

  axiomPlusZero: {
    statement: '@R x => x + 0 = x',
    proof: function() {
      return (rules.assert('R x => x + 0 = x')
              .andThen('asHypotheses'));
    },
    tooltip: 'x + 0 = x',
    description: 'additive identity'
  },

  axiomTimesOne: {
    statement: '@R x => x * 1 = x',
    proof: function() {
      return (rules.assert('R x => x * 1 = x')
              .andThen('asHypotheses'));
    },
    tooltip: 'x * 1 = x',
    description: 'multiplicative identity'
  },

  axiomTimesZero: {
    statement: '@R x => x * 0 = 0',
    proof: function() {
      return (rules.assert('R x => x * 0 = 0')
              .andThen('asHypotheses'));
    },
    tooltip: 'x * 0 = 0',
    description: 'multiplication by 0'
  },

  axiomNeg: {
    statement: '@neg x = -1 * x',
    proof: function() {
      return rules.assert('neg x = -1 * x');
    },
    tooltip: 'neg x = -1 * x',
    description: 'definition of negation'
  },

  axiomReciprocal: {
    statement: '@R x & x != 0 => x * recip x = 1',
    proof: function() {
      return (rules.assert('R x & x != 0 => x * recip x = 1')
              .andThen('asHypotheses'));
    },
    tooltip: 'x * recip x = 1 if x is not 0',
    description: 'recip is inverse to multiplication'
  },

  // TODO: Prove this as a theorem.
  axiomReciprocal2: {
    statement: '@R (recip x) & recip x != 0 == R x & x != 0',
    proof: function() {
      return rules.assert('R (recip x) & recip x != 0 == R x & x != 0');
    },
    description: 'reciprocals are nonzero'
  },

  // This implies that 0 ** 0 = 1.  It is also legitimate to define
  // that 0 ** 0 is undefined.
  // TODO: Eventually prove these laws of powers as theorems.
  axiomPower0: {
    statement: '@R x => x ** 0 = 1',
    proof: function() {
        return (rules.assert('R x => x ** 0 = 1')
                .andThen('asHypotheses'));
    },
    description: 'real number to the zeroth power is 1'
  },

  // TODO: Eventually prove these laws of powers as theorems.
  axiomNextPower: {
    statement: '@x ** (y + 1) = (x ** y) * x',
    proof: function() {
      // TODO: Add conditions R x & R y.
      return rules.assert('x ** (y + 1) = (x ** y) * x');
    },
    description: 'real number to the next power'
  },

  // TODO: Prove this as a consequnce of completeness.
  factNonzeroProduct: {
    statement: '@R x & R y => (x * y != 0) = (x != 0 & y != 0)',
    proof: function() {
      return (rules.assert('R x & R y => (x * y != 0) = (x != 0 & y != 0)')
              .andThen('asHypotheses'));
    }
  },

  // Type-related axioms

  // This axiom applies to all normal objects, not just reals.
  axiomRealNotNull: {
    statement: '@not (R none)',
    proof: function() {
      return rules.assert('not (R none)');
    }
  },

  axiomPlusType: {
    statement: '@R x & R y == R (x + y)',
    proof: function() {
      return rules.assert('R x & R y == R (x + y)');
    }
  },

  axiomTimesType: {
    statement: '@R x & R y == R (x * y)',
    proof: function() {
      return rules.assert('R x & R y == R (x * y)');
    }
  },

  axiomNegType: {
    statement: '@R x == R (neg x)',
    proof: function() {
      return rules.assert('R x == R (neg x)');
    }
  },

  axiomReciprocalType: {
    statement: '@R x & x != 0 == R (recip x)',
    proof: function() {
      return rules.assert('R x & x != 0 == R (recip x)');
    }
  },

  // Evaluates arithmetic expressions with operators: +, -, *, /, div,
  // mod, neg, =, !=, >, >=, <, <=, and the type operator "R".  Checks
  // that inputs are all numeric and that the result can be guaranteed
  // to be an exact integer.
  //
  // Result is always an equation (or biconditional) with the given
  // term as the LHS.  Throws an error if it cannot obey these
  // specifications.
  //
  // TODO: Include facts that a / b = c is false for integers
  //   a, b, and c unless b divides a exactly.
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
          // TODO: Consider evaluating these to the null value.
          check(right !== 0, 'Cannot divide by zero');
          value = left / right;
          // abs(value) <= abs(left) since abs(right) >= 1 so the
          // magnitude is not a problem.  The fractional part of a
          // result must have denominator no greater than MAX_INT,
          // so it should be distinguishable from an integer.
          check(value === Math.floor(value), 'Inexact division');
          break;
        case 'div': value = Toy.div(left, right); break;
        case 'mod': value = Toy.mod(left, right); break;
        case '=': value = left === right; break;
        case '!=': value = left !== right; break;
        case '>': value = left > right; break;
        case '>=': value = left >= right; break;
        case '<': value = left < right; break;
        case '<=': value = left <= right; break;
        default:
          err('Unsupported operator: ' + op);
	}
        if (typeof value == 'boolean') {
          var rhs = value ? T : F;
        } else {
          var rhs = Toy.numify(value);
        }
        return rules.assert(Toy.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else if (term instanceof Toy.Call) {
        var op = term.fn;
        check(op.isConst(),
               function() { return 'Unsupported operator: ' + op; });
        var arg = term.arg.getNumValue();
        if (op.name == 'neg') {
          value = -arg;
          var rhs = Toy.numify(value);
        } else if (op.name == 'R') {
          var rhs = T;
        } else {
          err('Not an arithmetic expression: ' + term);
        }
        return rules.assert(Toy.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else {
	err('Not an arithmetic expression: ' + term);
      }
    },
    inputs: {term: 1},
    form: 'Term to evaluate: <input name=term>',
    tooltip: 'evaluate arithmetic expression',
    description: 'axiom of arithmetic',
    autoSimplify: noSimplify,
    labels: 'basic'
  },

  subtractionType: {
    statement: '@R x & R y == R (x - y)',
    proof: function() {
      var step1 = rules.axiomPlusType();
      var step2 = rules.instVar(step1, Toy.parse('neg y'), 'y');
      var step3 = rules.axiomNegType();
      var step4 = rules.instVar(step3, 'y', 'x');
      var step5 = rules.rRight(step4, step2, '/left/right');
      var step6 = rules.eqSelf(Toy.parse('x - y'));
      var step7 = rules.apply(step6, '/left');
      return rules.rplace(step7, step5, '/main/right/arg');
    },
    form: '',
    menu: 'theorem R (x - y)',
    tooltip: 'difference of real numbers is real',
    description: 'difference of real numbers is real',
    labels: 'uncommon'
  },

  divisionType: {
    statement: '@R x & R y & y != 0 == R (x / y)',
    proof: function() {
      var step1 = rules.axiomTimesType();
      var step2 = rules.instVar(step1, Toy.parse('recip y'), 'y');
      var step3 = rules.axiomReciprocalType();
      var step4 = rules.instVar(step3, 'y', 'x');
      var step5 = rules.rRight(step4, step2, '/left/right');
      var step6 = rules.eqSelf(Toy.parse('x / y'));
      var step7 = rules.apply(step6, '/left');
      var step8 = rules.rplace(step7, step5, '/main/right/arg')
      // TODO: Normalize the assumptions automatically, not by hand.
      return rules.rewriteOnly(step8, '/left',
                               rules.tautology('a & (b & c) == a & b & c'));
    },
    form: '',
    menu: 'theorem R (x / y)',
    tooltip: 'quotient of real numbers is real',
    description: 'quotient of real numbers is real',
    labels: 'uncommon'
  },

  //
  // Inference rules for real numbers
  //

  // Rewrites a simple arithmetic expression to its value.
  arithmetic: {
    action: function(step, path) {
      var term = step.get(path);
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
          assert(false, 'Not an arithmetic expression: {1}', term);
        }
      }
      return result.justify('arithmetic', arguments, [step]);
    },
    isRewriter: true,
    inputs: {site: 1},
    toOffer: 'return Toy.isArithmetic(term);',
    form: '',
    tooltip: 'arithmetic',
    labels: 'algebra'
  }

};

equationOpsInfo = {

  // Add the given term to the equation in the step at the given path,
  // typically /right/right.
  addToBoth: {
    action: function(step, eqnPath, term_arg) {
      var fact = rules.fact('a = b == a + c = b + c');
      var c1 = step.wff.freshVar('c');
      // Since the input step has no free occurrences of c1, the
      // rewrite will have free occurrences of it exactly where
      // it occurs in this fact, which is the desired situation.
      // Note that if c1 is the same as c, the instVar is a no-op.
      var fact2 = rules.instVar(fact, term_arg, c1);
      return (rules.rewrite(step, eqnPath, fact2)
              .andThen('instVar', term_arg, c1)
              .justify('addToBoth', arguments, [step]));
    },
    inputs: {site: 1, term: 3},
    autoSimplify: function(step) {
      return simplifyAddSubBoth(step, step.ruleArgs[1]);
    },
    toOffer: 'return term.isCall2("=");',
    form: ('Add <input name=term> to both sides of the equation'),
    menu: 'algebra: add to both sides',
    tooltip: ('add to both sides'),
    description: 'add {term} to both sides;; {in step siteStep}',
    labels: 'algebra'
  },

  subtractFromBoth: {
    action: function(step, eqnPath, term_arg) {
      var fact = rules.fact('a = b == a - c = b - c');
      var c1 = step.wff.freshVar('c');
      // See addToBoth.
      var fact2 = rules.instVar(fact, term_arg, c1);
      return (rules.rewrite(step, eqnPath, fact2)
              .andThen('instVar', term_arg, c1)
              .justify('subtractFromBoth', arguments, [step]));
    },
    inputs: {site: 1, term: 3},
    autoSimplify: function(step) {
      return simplifyAddSubBoth(step, step.ruleArgs[1]);
    },
    toOffer: 'return term.isCall2("=");',
    form: ('Subtract <input name=term> from both sides of the equation'),
    menu: 'algebra: subtract from both sides',
    tooltip: ('subtract from both sides'),
    description: 'subtract {term} from both sides;; {in step siteStep}',
    labels: 'algebra'
  },

  multiplyBoth: {
    action: function(step, eqnPath, term_arg) {
      var fact = rules.fact('c != 0 => (a = b == a * c = b * c)');
      var c1 = step.wff.freshVar('c');
      // See addToBoth.
      var fact2 = rules.instVar(fact, term_arg, c1);
      return (rules.rewrite(step, eqnPath, fact2)
              .andThen('instVar', term_arg, c1)
              .justify('multiplyBoth', arguments, [step]));
    },
    inputs: {site: 1, term: 3},
    autoSimplify: function(step) {
      return simplifyMulDivBoth(step, step.ruleArgs[1]);
    },
    toOffer: 'return term.isCall2("=");',
    form: ('Multiply both sides of the equation by <input name=term>'),
    menu: 'algebra: multiply both sides',
    tooltip: ('multiply both sides'),
    description: 'multiply both sides by {term};; {in step siteStep}',
    labels: 'algebra'
  },

  divideBoth: {
    action: function(step, eqnPath, term_arg) {
      var fact = rules.fact('c != 0 => (a = b == a / c = b / c)');
      var c1 = step.wff.freshVar('c');
      // See addToBoth.
      var fact2 = rules.instVar(fact, term_arg, c1);
      return (rules.rewrite(step, eqnPath, fact2)
              .andThen('instVar', term_arg, c1)
              .justify('divideBoth', arguments, [step]));
    },
    inputs: {site: 1, term: 3},
    autoSimplify: function(step) {
      return simplifyMulDivBoth(step, step.ruleArgs[1]);
    },
    toOffer: 'return term.isCall2("=");',
    form: ('Divide both sides of the equation by <input name=term>'),
    menu: 'algebra: divide both sides',
    tooltip: ('divide both sides'),
    description: 'divide both sides by {term};; {in step equation}',
    labels: 'algebra'
  },

  // Add the term at the given site to both sides of the (innermost)
  // equation containing it.
  addThisToBoth: {
    action: function(step, path) {
      var eqnPath = step.wff.parentEqn(path);
      assert(eqnPath, 'No equation found in {1}', step.wff);
      return (rules.addToBoth(step, eqnPath, step.wff.get(path))
              .justify('addThisToBoth', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: function(step) {
      var path = step.ruleArgs[1];
      return simplifyAddSubBoth(step, step.wff.parentEqn(path)); 
    },
    toOffer: 'return term.isReal();',
    form: '',
    menu: ' &hellip; + {term} = &hellip; + {term} (add to both sides)',
    description: 'add {site};; {in step siteStep}',
    labels: 'algebra'
  },

  subtractThisFromBoth: {
    action: function(step, path) {
      var eqnPath = step.wff.parentEqn(path);
      assert(eqnPath, 'No equation found in {1}', step.wff);
      return (rules.subtractFromBoth(step, eqnPath, step.wff.get(path))
              .justify('subtractThisFromBoth', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: function(step) {
      var path = step.ruleArgs[1];
      return simplifyAddSubBoth(step, step.wff.parentEqn(path));
    },
    toOffer: 'return term.isReal();',
    form: '',
    menu: (' &hellip; &minus; {term} = &hellip; &minus; {term}' +
           ' (subtract from both sides)'),
    description: 'subtract {site};; {in step siteStep}',
    labels: 'algebra'
  },

  multiplyBothByThis: {
    action: function(step, path) {
      var eqnPath = step.wff.parentEqn(path);
      assert(eqnPath, 'No equation found in {1}', step.wff);
      return (rules.multiplyBoth(step, eqnPath, step.wff.get(path))
              .justify('multiplyBothByThis', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: function(step) {
      var path = step.ruleArgs[1];
      return simplifyMulDivBoth(step, step.wff.parentEqn(path));
    },
    toOffer: 'return term.isReal();',
    form: '',
    menu: (' &hellip; &sdot; {term} = &hellip; &sdot; {term}' +
           ' (multiply both sides)'),
    description: 'multiply by {site};; {in step siteStep}',
    labels: 'algebra'
  },

  divideBothByThis: {
    action: function(step, path) {
      var eqnPath = step.wff.parentEqn(path);
      assert(eqnPath, 'No equation found in {1}', step.wff);
      return (rules.divideBoth(step, eqnPath, step.wff.get(path))
              .justify('divideBothByThis', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: function(step) {
      var path = step.ruleArgs[1];
      return simplifyMulDivBoth(step, step.wff.parentEqn(path));
    },
    toOffer: 'return term.isReal();',
    form: '',
    menu: (' &hellip; \u2215 {term} = &hellip; \u2215 {term}' +
           ' (divide both sides)'),
    description: 'divide by {site};; {in step siteStep}',
    labels: 'algebra'
  },

  addEquationToThis: {
    action: function(eqn1, eqn2) {
      var lhs = eqn2.getMain().getLeft();
      var step1 = rules.applyToBothWith(eqn1, '+', lhs);
      var step3 = rules.replaceEither(step1, '/main/right/right', eqn2);
      return step3.justify('addEquationToThis', arguments, arguments);
    },
    inputs: {equation: [1, 2]},
    // toOffer: 'return step.getMain().getLeft().isReal()',
    form: ('To step <input name=equation1> add the sides' +
           ' of step <input name=equation2>'),
    menu: 'algebra: add the sides of an equation to this',
    description: 'add the sides of steps {equation1} and {equation2}',
    labels: 'algebra'
  },

  subtractEquationFromThis: {
    action: function(eqn1, eqn2) {
      var lhs = eqn2.getMain().getLeft();
      var step1 = rules.applyToBothWith(eqn1, '-', lhs);
      var step3 = rules.replaceEither(step1, '/main/right/right', eqn2);
      return step3.justify('subtractEquationFromThis', arguments, arguments);
    },
    inputs: {equation: [1, 2]},
    // toOffer: 'return step.getMain().getLeft().isReal()',
    form: ('From step <input name=equation1> subtract the sides' +
           ' of step <input name=equation2>'),
    menu: 'algebra: subtract an equation from this',
    description: 'from step {equation1} subtract the sides of step {equation2}',
    labels: 'algebra'
  }

};

//// Support code for the equation operations rules above.

// Facts that regroup an add/subtract or multiply/divide term
// out of their standard order.
var regroupingFacts = [
  'a + b + c = a + (b + c)',
  'a + b - c = a + (b - c)',
  'a - b + c = a - (b - c)',
  'a - b - c = a - (b + c)',
  'a * b * c = a * (b * c)',
  'a * b / c = a * (b / c)',
  'a / b * c = a * (c / b)',
  'a / b / c = a / (b * c)'
];

/**
 * Arrange the terms on each side of the equation input.  Also
 * appropriate when dividing.
 */
function simplifyMulDivBoth(step, eqnPath) {
  var rightSimpler = rules.arrangeTerm(step, eqnPath.concat('/right'));
  var leftSimpler = rules.arrangeTerm(rightSimpler, eqnPath.concat('/left'));
  return rules.simplifyStep(leftSimpler);
}

/**
 * After add/subtract both sides, this tries regrouping and then
 * possible simplification.
 *
 * TODO: Move the functionality into one or two rules.
 */
function simplifyAddSubBoth(step, eqnPath) {
  var applyFactsOnce = Toy.applyFactsOnce;
  // Simplify the right side by regrouping and simplifying the result.
  var right = step;
  var right1 = applyFactsOnce(step, eqnPath.concat('/right'), regroupingFacts);
  if (right1 !== step) {
    right = rules.simplifySite(right1, eqnPath.concat('/right'));
    if (right == right1) {
      // Don't bother regrouping if the result cannot be simplified.
      right = step;
    }
  }
  // Simplify the left side by regrouping and simplifying the result.
  var left = right;
  var left1 = applyFactsOnce(right, eqnPath.concat('/left'), regroupingFacts);
  if (left1 !== right) {
    left = rules.simplifySite(left1, eqnPath.concat('/left'));
    if (left == left1) {
      // Don't bother regrouping if the result cannot be simplified.
      left = right;
    }
  }
  return left;
}

var simplifiersInfo = {

  // Managing numeric type hypotheses

  // Given a step that is a conditional, proves a version with the
  // assumptions simplified.  Reduces assumptions about "R" type of
  // expressions with arithmetic operators to assumptions about "R"
  // type of variables; removes assumptions that specific numerals are
  // real or nonzero; simplifies assumptions about products being
  // nonzero into assertions that both operands are real; removes
  // duplicate terms and occurrences of T.
  simplifyAssumptions: {
    action: function(step_arg) {
      var step = step_arg;
      if (!step.wff.isCall2('=>')) {
        // Shortcut inline return.
        return step;
      }
      // From a conditional a => b, prove a => (b == T), with a as
      // hypothesis.  Returns a memoized function that yields the
      // proved result.
      function proveIsT(stmt) {
        return memo(function() {
            return (stmt.andThen('asHypotheses')
                    .andThen('rewriteOnly', '/right', 'p == (p == T)'));
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
      var adder = proveIsT(rules.axiomPlusType());
      var multiplier = proveIsT(rules.axiomTimesType());
      var subtracter = proveIsT(rules.subtractionType());
      var divider = proveIsT(rules.divisionType());
      var negger = memo(function() {
          return rules.axiomNegType().andThen('eqnSwap');
        });
      // x != 0 => (R (recip x) == R x)
      var reciper = memo(function() {
          var step = rules.axiomReciprocalType();
          var schema = rules.tautology('(a & b == c) => (b => (c == a))');
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
      // form h => (R <expr>) = <expr2> with h as hypotheses, or just
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
          var result = tryArithmetic(expr);
          if (result) {
            return function() { return result; };
          }
          if (expr.matchSchema('x * y != 0')) {
            // Simplify statements about nonzero products.
            return memo(function() { return rules.factNonzeroProduct(); });
          }
          if (expr.matchSchema('recip x != 0')) {
            // Simplify statements about nonzero reciprocals.
            return proveIsT(rules.fact('@R a & a != 0 => recip a != 0'));
          }
        }
        return null;
      }
      // Finds and returns a path to a conjunct in the given term that
      // passes the test, or returns null.
      function scanConjuncts(term, test) {
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
        if (!stepArg.isCall2('=>')) {
          return stepArg;
        }
        var step = stepArg;
        // Repeatedly replace assumptions that match some rule
        // from getArithOp until there is none.
        while (true) {
          var hyps = step.getLeft();
          var hypsPath = scanConjuncts(hyps, getArithOp);
          if (!hypsPath) {
            return step;
          }
          var path = new Toy.Path('left', hypsPath);
          var expr = step.get(path);
          var fact = getArithOp(expr)(expr);
          // If no facts appearing here were conditionals, the recursion
          // would be unnecessary.  But see reciper, above.
          var simpleFact =
            simplifyHyps(rules.instantiate(fact, '/main/left', expr));
          // Replaces an assumption, potentially adding additional assumptions
          // to the result, as in case of recip or nonzero assumptions.
          // Result with added assumptions is still equivalent to the original
          // provided that all new ones are duplicates of existing.
          // TODO: Use rules.r with tautologies instead of rules.rplace, and
          //   remove the special-purpose code put there to handle this case.
          step = rules.rplace(simpleFact, step, path);
        }
      }
      return (simplifyHyps(step)
              .andThen('arrangeAsms')
              .justify('simplifyAssumptions', arguments, [step]));
    },
    inputs: {step: 1},
    form: 'Step to simplify: <input name=step>',
    tooltip: 'simplify assumptions in a step',
    menu: 'simplify assumptions',
    labels: 'uncommon'
  },

  // Simplifies repeatedly using basicSimpFacts.  If the visible part
  // of the step is an equation, simplify each side, otherwise the
  // entire expression.
  //
  // TODO: Refactor this so the rule itself is not dependent on
  //   different possible renderings.
  simplifyStep: {
    action: function(step) {
      var visPath = step.pathToVisiblePart();
      if (step.get(visPath).isCall2('=')) {
        var step1 = rules.simplifySite(step, visPath.concat('/right'))
        var result = rules.simplifySite(step1, visPath.concat('/left'))
      } else {
        var result = rules._simplifySite(step, visPath);
      }
      return result.justify('simplifyStep', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Simplify step <input name=step>'),
    menu: 'algebra: simplify',
    offerExample: true,
    description: 'simplify;; {step step}',
    labels: 'algebra'
  },

  // Like simplifySite, but if any simplification result is the same
  // as the content of the site in refStep, this returns its input
  // step, thereby doing nothing.  So if the site in refStep was
  // already simplified, this will not revert to it.  (If the site
  // was not already simplified, a de-simplification step may
  // still be re-simplified.)
  //
  // An alternative, slightly simpler approach would be to suppress
  // auto-simplification of the result of a rewrite if it is the
  // inverse of a simplification.
  autoSimplifySite: {
    action: function(step, path, refStep) {
      var _path = Toy.path;
      var term = step.get(path);
      if (!term) {
        // In some situations the path may need adjustment.  This is
        // a workaround for cases where the path is totally wrong.
        // TODO: Improve on this.
        return step;
      }
      var eqn1 = rules.consider(term);
      var ref = refStep.get(path);
      var abort = false;
      var simpler = Toy.whileChanges(eqn1, function(eqn) {
        var next = rules._simplifyMath1(eqn, _path('/main/right', eqn));
        if (next.getMain().getRight().sameAs(ref)) {
          abort = true;
          // Returning the input causes simplification to stop.
          return eqn;
        } else {
          return next;
        }
      });
      return abort
        ? step
        : (rules.rplace(simpler, step, path)
           .justify('autoSimplifySite', arguments, [step]));
    },
    inputs: {site: 1, step: 3},
    form: 'Simplify w.r.t. step <input name=step>',
    menu: 'algebra: auto-simplify {term}',
    description: 'simplify;; {in siteStep}',
    labels: 'uncommon'
  },

  // Applies simplification repeatedly within the part of the given
  // step at the given path using basicSimpFacts until no more
  // simplifications are found.
  simplifySite: {
    action: function(step, path) {
      var result = rules._simplifySite(step, path);
      return result.justify('simplifySite', arguments, [step]);
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: simplify {term}',
    offerExample: true,
    description: 'simplify;; {in step siteStep}',
    labels: 'algebra'
  },
    
  // Inline version of simplifySite.
  _simplifySite: {
    action: function(step, path) {
      var _path = Toy.path;
      var eqn = rules.consider(step.get(path));
      var simpler = Toy.whileChanges(eqn, function(eqn) {
          return rules._simplifyMath1(eqn, _path('/main/right', eqn));
        });
      return rules.rplace(simpler, step, path);
    }
  },

  // Applies up to one simplification within the part of the given
  // step at _path using basicSimpFacts.  Returns its result inline,
  // just the input step if there is nothing to do.
  //
  // From the UI use a rule that calls this one.
  _simplifyMath1: {
    action: function(step, _path) {
      var info = Toy.searchForMatchingFact(step.get(_path), basicSimpFacts);
      return (info
              ? rules.rewrite(step, _path.concat(info.path), info.stmt)
              : step);
    }
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
      var schemas = [{match: 'neg a', where: '$.a.isNumeral()'}];
      var info;
      while (info = Toy.searchForMatchingFact(simpler.get(path1), schemas)) {
        simpler = rules.arithmetic(simpler, path1.concat(info.path));
      }
      return simpler.justify('simplifyNegations', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Simplify negations in <input name=step>'),
    menu: 'algebra: simplify negations',
    offerExample: true,
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
    menu: 'algebra: convert - to +',
    description: 'convert subtraction to addition',
    labels: 'algebra'
  },

  cleanUpTerms: {
    action: function(step) {
      var facts = ['a * (b * c) = a * b * c',
                   {stmt: 'a * b = b * a',
                    where: '!$.b.hasVars() && $.a.hasVars()'},
                   // TODO: Consider a * b * c = a * c * b instead.
                   {stmt: 'a * b * c = a * (c * b)',
                    where: '!$.c.hasVars() && $.b.hasVars()'},
                   {stmt: 'a * b / c = a / c * b',
                    where: '!$.a.hasVars() && !$.c.hasVars()'}
                  ];
      var result = applyToVisible(step, facts);
      return result.justify('cleanUpTerms', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Clean up the terms in step <input name=step>'),
    menu: 'algebra: clean up terms',
    description: 'clean up each term',
    labels: 'algebra'
  }
};  // End of simplifiersInfo.

var moversInfo = {
  // Organize the factors in a term.  Processes multiplication,
  // division, negation, reciprocal, and arithmetic.
  //
  // TODO: Justify and test this extensively.
  arrangeTerm: {
    data: function() {
      var flatteners = [
        {stmt: 'neg (neg a) = a'},
        {stmt: 'a * (b * c) = a * b * c'},
        {stmt: 'a * (b / c) = a * b / c'},
        {stmt: 'neg (a * b) = neg a * b'},
        {stmt: 'neg (a / b) = neg a / b'},
        {stmt: 'a / (b * c) = a / b / c'},
        {stmt: 'a / (b / c) = a / b * c'},
        // TODO: Convert to this style:
        // {match: 'a * b', a: 'flatteners'},
        {descend:
         {schema: 'a * b',
          parts: {a: 'flatteners', b: 'flatteners'}}},
        {descend:
         {schema: 'a / b',
          parts: {a: 'flatteners'}}}
      ];
      var numeralAfterVar = '$.c.isNumeral() && $.b.isVariable()';
      var movers = [
        // Move "minus signs" to the left.
        {stmt: 'a * neg b = neg a * b',
         where: 'subst.a instanceof Toy.Atom'},
        {stmt: 'a / (neg b) = neg a / b',
         where: 'subst.a instanceof Toy.Atom'},
        {stmt: 'a * b * neg c = a * neg b * c'},
        {stmt: 'a * b / neg c = a * neg b / c'},
        {stmt: 'a / b * neg c = a / neg b * c'},
        {stmt: 'a / b / neg c = a / neg b / c'},

        // Move numerals toward the left.
        {stmt: 'a * b = b * a',
         where: '$.b.isNumeral() && $.a.isVariable()'},
        {stmt: 'a * b * c = a * c * b', where: numeralAfterVar},
        {stmt: 'a * b / c = a / c * b', where: numeralAfterVar},
        {stmt: 'a / b * c = a / c * b', where: numeralAfterVar},
        {stmt: 'a * b / c = a / c * b', where: numeralAfterVar},

        {descend:
         {schema: 'a * b',
          parts: {a: 'movers'}}}
      ];
      var numeralC = '$.c.isNumeral()';
      var numerators = [
        {stmt: 'a / b * c = a * c / b', where: numeralC},
        {descend:
         {schema: 'a * b',
          parts: {a: 'numerators'}}},
        {descend:
         {schema: 'a / b',
          parts: {a: 'numerators'}}}
      ];
      var denominators = [
        {stmt: 'a / b / c = a / (b * c)', where: numeralC},
        {descend:
         {schema: 'a * b',
          parts: {a: 'denominators'}}},
        {descend:
         {schema: 'a / b',
          parts: {a: 'denominators'}}}
      ];
      var bothNumerals = '$.a.isNumeral() && $.b.isNumeral() ';
      var arithmetizers = [
        {apply: tryArithmetic},
        // From 2 / -3 for example produces -2 / 3 for minus two thirds.
        {stmt: 'a / b = neg a / neg b',
         where: bothNumerals + ' && $.b.getNumValue() < 0'},
        {descend:
         {schema: 'a / b',
          parts: {a: 'arithmetizers', b: 'arithmetizers'}}},
        {descend:
         {schema: 'a * b',
          parts: {a: 'arithmetizers', b: 'arithmetizers'}}}
      ];
      var data =
            {context:
             {factLists:
              {flatteners: flatteners,
               movers: movers,
               numerators: numerators,
               denominators: denominators,
               arithmetizers: arithmetizers
              }}};
      return data;
    },
    toOffer: function(step, expr) {
      return (expr.matchSchema('a * b') ||
              expr.matchSchema('a / b') ||
              expr.matchSchema('neg (a * b)') ||
              expr.matchSchema('neg (a / b)'));
    },
    action: function(step, path) {
      var context = this.data.context;
      var arrangeRhs = Toy.arrangeRhs;

      return convert(step, path, function(expr) {
        var eqn = rules.consider(expr);
        var flat = arrangeRhs(eqn, context, 'flatteners');
        var ordered = arrangeRhs(flat, context, 'movers');
        var numerated = arrangeRhs(ordered, context, 'numerators');
        var denominated = arrangeRhs(numerated, context, 'denominators');
        var arranged = arrangeRhs(denominated, context, 'arithmetizers');
        // Perhaps this just applies 1 * x = x.
        return rules.simplifySite(arranged, '/main/right');
      }).justify('arrangeTerm', arguments, [step]);
    },
    inputs: {site: 1},
    offerExample: true,
    form: '',
    menu: 'algebra: get standard form of {term}',
    description: 'standard form of {site};; {in step siteStep}',
    labels: 'algebra'
  },

  regroupAdditions: {
    action: function(step) {
      function applyTo(eqn, facts) {
        return Toy.applyFactsWithinRhs(eqn, {facts: facts,
                                             searchMethod: 'searchTerms'});
      }
      function converter(expr) {
        var eqn = rules.consider(expr);
        // Linearize eqns.
        var eqn0 = applyTo(eqn, [{stmt: 'a + (b + c) = a + b + c'}]);

        // Move eqns that are numerals to the back of the bus.
        var facts1 = [{stmt: 'a + b = b + a',
                       where: '!$.a.hasVars() && $.b.hasVars()'},
                      {stmt: 'a + b + c = a + c + b',
                       where: '!$.b.hasVars() && $.c.hasVars()'}
                     ];
        var eqn1 = applyTo(eqn0, facts1);

        // Group numerals together.
        var facts2 = [{stmt: 'a + b + c = a + (b + c)',
                       where: '!$.b.hasVars()'}
                     ];
        var eqn2 = applyTo(eqn1, facts2);

        // These come from rules.cleanupTerms.
        var cleanFacts = ['a * (b * c) = a * b * c',
                          {stmt: 'a * b = b * a',
                           where: '!$.b.hasVars() && $.a.hasVars()'},
                          {stmt: 'a * b * c = a * (c * b)',
                           where: '!$.c.hasVars() && $.b.hasVars()'},
                          {stmt: 'a * b / c = a / c * b',
                           where: '!$.a.hasVars() && !$.c.hasVars()'}
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
      var visPath = step.pathToVisiblePart();
      if (step.get(visPath).isCall2('=')) {
        var step1 =
          convert(step, visPath.concat('/right'), converter);
        var result =
          convert(step1, visPath.concat('/left'), converter);
      } else {        
        var result = convert(step, visPath, converter);
      }
      return result.justify('regroupAdditions', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Regroup additive terms in step <input name=step>',
    menu: 'algebra: regroup additive terms',
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
      .andThen('regroupAdditions')
      .justify('regroup', arguments, [step]);
    },
    inputs: {step: 1},
    form: 'Regroup terms in step <input name=step>',
    menu: 'algebra: regroup terms',
    description: 'regroup terms',
    labels: 'algebra'
  },

  /**
   * Moves a term to the right in a sequence of summed terms.
   * The sequence must be "flat", associated to the left.
   */
  moveTermRight: {
    data: {
      factsA: [
        'neg a + b = b - a',
        'a + b = b + a',
        'a - b = neg b + a'
      ],
      factsB: [
        'a + b + c = a + c + b',
        'a + b - c = a - c + b',
        'a - b + c = a + c - b',
        'a - b - c = a - c - b'
      ]},
    toOffer: function(step, expr) {
      var path = step.pathTo(expr);
      var data = this.data;
      var factsA = data.factsA;
      var factsB = data.factsB;
      // Truthy value if the given name in the LHS of the fact can
      // match the part of this at the selected path.
      function testFact(name, fact_arg) {
        var schema = Toy.getResult(fact_arg).getMain().getLeft();
        var info = step.matchSchemaPart(path, schema, name);
        return info || undefined;
      }
      return (Toy.each(factsB, testFact.bind(null, 'b')) ||
              Toy.each(factsA, testFact.bind(null, 'a')));
    },
    autoSimplify: noSimplify,
    action: function(step, path_arg) {
      var data = this.data;
      var factsB = data.factsB;
      var factsA = data.factsA;
      function tryFact(name, fact_arg) {
        var schema = Toy.getResult(fact_arg).getMain().getLeft();
        var info = step.matchSchemaPart(path_arg, schema, name);
        if (info) {
          return rules.rewrite(step, info.path, fact_arg);
        }
      }
      var result = (Toy.each(factsB, tryFact.bind(null, 'b')) ||
                    Toy.each(factsA, tryFact.bind(null, 'a')) ||
                    step);
      return result.justify('moveTermRight', arguments, [step]);
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: move {term} to the right',
    description: 'move term right',
    labels: 'algebra'
  },

  /**
   * Moves a term to the left in a sequence of summed terms.
   * The sequence must be "flat" (associated to the left).
   */
  moveTermLeft: {
    toOffer: function(step, expr) {
      var path = step.prettyPathTo(expr);
      var lastSegment = path.last();
      if (lastSegment == 'right') {
        var parent = step.get(path.parent());
        return parent.isCall2('+') || parent.isCall2('-');
      } else {
        return false;
      }
    },
    autoSimplify: noSimplify,
    action: function(step, path_arg) {
      var factsC = [
        'a + b + c = a + c + b',
        'a + b - c = a - c + b',
        'a - b + c = a + c - b',
        'a - b - c = a - c - b'
      ];
      var factsB = [
        'a + b = b + a',
        'a - b = neg b + a'
      ];
      function tryFact(name, fact_arg) {
        var schema = termify(fact_arg).getLeft();
        var info = step.matchSchemaPart(path_arg, schema, name);
        if (info) {
          return rules.rewrite(step, info.path, fact_arg);
        }
      }
      var result = (Toy.each(factsC, tryFact.bind(null, 'c')) ||
                    Toy.each(factsB, tryFact.bind(null, 'b')));
      return (result || step).justify('moveTermLeft', arguments, [step]);
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: move {term} to the left',
    description: 'move term left',
    labels: 'algebra'
  },

  /**
   * Rule to force association to the right for addition, subtraction,
   * multiplication, and division.  Does nothing if not applicable.
   */
  groupToRight: {
    toOffer: function(step, expr) {
      return Toy.matchFactPart(step, step.pathTo(expr), regroupingFacts, 'b');
    },
    autoSimplify: function(step) {
      if (Toy.autoSimplifyWholeStep) {
        return rules.simplifyStep(step);
      } else {
        var path = getStepSite(step).parent().parent().concat('/right');
        return rules.simplifySite(step, path);
      }
    },
    action: function(step, path) {
      var func = Toy.matchFactPart(step, path, regroupingFacts, 'b');
      return func
        ? func().justify('groupToRight', arguments, [step])
        : step;
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: group {term} with {right}',
    description: 'group to the right',
    labels: 'algebra'
  },

  /**
   * Moves term to the left as needed until it does not necessarily
   * belong to the left of its left neighbor.
   * 
   */
  placeTermLeftward: {
    toOffer: function(step, expr) {
      var path = step.prettyPathTo(expr);
      var leftPath = step.leftNeighborPath(path, ['+', '-']);
      return leftPath && termLeftThan(expr, step.get(leftPath));
    },
    action: function(step, path_arg) {
      var path = step.prettifyPath(path_arg);
      var prev = step;
      while (true) {
        var further = rules.moveTermLeft(prev, path);
        var leftPath = prev.leftNeighborPath(path, ['+', '-']);
        if (further.matches(prev) ||
            !termLeftThan(step.get(path), step.get(leftPath))) {
          return further.justify('placeTermLeftward', arguments, [step]);
        }
        path = leftPath;
        prev = further;
      }
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: move term left as needed',
    description: 'move term left as needed',
    // Could be algebra, but this rule seems better for more advanced
    // students.
    labels: ''
  },

  /** TODO: Decide whether to keep or remove this rule.
  removeRightTerm: {
    action: function(step, path) {
      // This rule assumes that the step has the form
      // H => lhs = rhs
      //
      var term = step.get(path);
      assert(!step.rendering.hasLeftElision,
             'Not supported: would modify hidden equation left side');
      var xp = path.expand().toString();
      // Path to outer term of the form (A + <term>)
      var outPath;
      if (xp === '/arg/fn/arg/arg') {
        // Path is /main/left/right.
        var op = step.get('/main/left/binop');
        assert(op.name === '+' || op.name === '-',
               'Operator needs to be + or -');
        outPath = Toy.path('/main/left');
      } else if (xp === '/arg/arg/arg') {
        // Path is /main/right/right.
        var op = step.get('/main/right/binop');
        assert(op.name === '+' || op.name === '-',
               'Operator needs to be + or -');
               outPath = Toy.path('/main/right');
      } else {
        assert(false,
               'Term needs to be on the right outside parentheses: {1}', term);
      }
      if (op.name === '+') {
        var result = rules.applyToBothWith(step, '-', term)
        .rewrite(outPath, 'a + b - c = a + (b - c)')
        .rewrite(outPath.concat('/right'), 'a - a = 0')
        .rewrite(outPath, 'a + 0 = a');
        return result.justify('removeRightTerm', arguments, [step]);
      } else {
        var result = rules.applyToBothWith(step, '+', term)
        .rewrite(outPath, 'a - b + c = a + (c - b)')
        .rewrite(outPath.concat('/right'), 'a - a = 0')
        .rewrite(outPath, 'a + 0 = a');
        return result.justify('removeRightTerm', arguments, [step]);
      }
    },
    inputs: {site: 1},
    form: '',
    menu: 'move term to the other side',
    description: 'move term to the other side',
    labels: 'algebra'
  },
  */

  /* TODO: Choose a way to get varName into the "where" clauses,
   *   then finish this.
  regroupBy: {
    action: function(step, path, varName) {
      var facts = [{stmt: 'a + b = b + a',
                    where: '$.a.isNumeral() && !$.b.isNumeral()'},
                   {stmt: 'a + b + c = a + c + b',
                    where: '$.b.isNumeral() && !$.c.isNumeral()'}
                  ];
      var result = applyToVisible(step, facts);
      return result.justify('regroup', arguments, [step]);
    },
    inputs: {site: 1, varName: 3},
    form: 'Group terms with variable <input name=varName>',
    menu: 'algebra: group terms',
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
            return rules.rewrite(step, path, fact);
          } catch(e) { }
        });
      try {
        return rules.arithmetic(step, path);
      } catch(e) { }
      throw new Error('No simplification found');
    },
    inputs: {site: 1},
    form: (''),
    menu: 'simplify {term}'
  },

};  // End of moversInfo.


var fractionsInfo = {

  /**
   * Reduces the selected fraction to lower terms using their least
   * common divisor (via Toy.npd).  No, not the greatest common
   * divisor, for pedagogical reasons.
   */
  reduceFraction: {
    action: function(step, path) {
      var expr = step.get(path);
      var lv = expr.getLeft().getNumValue();
      var rv = expr.getRight().getNumValue();
      var divisor = Toy.npd(lv, rv, 0);
      var fact = rules.fact('b != 0 & c != 0 => a / b = (a / c) / (b / c)');
      var step1 = rules.instVar(fact, Toy.numify(divisor), 'c');
      var result = rules.rewriteOnlyFrom(step, path, step1);
      return result.justify('reduceFraction', arguments, [step]);
    },
    toOffer: function(step, expr) {
      if (expr.isCall2('/')) {
        var l = expr.getLeft();
        var r = expr.getRight();
        if (l.isNumeral() && r.isNumeral()) {
          var lv = l.getNumValue();
          var rv = r.getNumValue();
          return Toy.npd(lv, rv, 0);
        }
      }
    },
    inputs: {site: 1},
    form: (''),
    menu: 'reduce fraction {term}',
    labels: 'algebra'
  },

  /**
   * Reduces the selected fraction to the form 1/k in the case where
   * the numerator exactly divides the denominator.
   */
  reduceFraction1: {
    action: function(step, path) {
      var expr = step.get(path);
      var lv = expr.getLeft().getNumValue();
      var rv = expr.getRight().getNumValue();
      var divisor = Math.min(lv, rv);
      var fact = rules.fact('b != 0 & c != 0 => a / b = (a / c) / (b / c)');
      var step1 = rules.instVar(fact, Toy.numify(divisor), 'c');
      var result = rules.rewriteOnlyFrom(step, path, step1);
      return result.justify('reduceFraction1', arguments, [step]);
    },
    toOffer: function(step, expr) {
      if (expr.isCall2('/')) {
        var l = expr.getLeft();
        var r = expr.getRight();
        if (l.isNumeral() && r.isNumeral()) {
          var lv = l.getNumValue();
          var rv = r.getNumValue();
          return lv % rv === 0 || rv % lv === 0;
        }
      }
    },
    inputs: {site: 1},
    form: (''),
    menu: 'fully reduce {term}',
    labels: 'algebra'
  },

  /**
   * Given a target expression which is the sum of two fractions (with
   * integer denominators) and a requested new denominator, this
   * produces a result with the fraction denominators changed to the
   * specified value, which must be an exact multiple of both.
   */
  commonDenominator: {
    action: function(step, path_arg, num) {
      var path = Toy.path(path_arg, step);
      var n = num.getNumValue();
      var expr = step.get(path);
      var map = (expr.matchSchema('a / d1 + b / d2') ||
                 expr.matchSchema('a / d1 - b / d2'));
      assert(map, 'Not sum/diff of fractions: {1}', expr);
      var d1 = map.d1.getNumValue();
      var d2 = map.d2.getNumValue();
      assert(n % d1 == 0 && n % d2 == 0, 'Not a multiple: {1}', n);
      var k1 = n / d1;
      var k2 = n / d2;
      var fact = rules.fact('a / b = a * c / (b * c)');
      var fact1 = rules.instVar(fact, Toy.numify(k1), 'c');
      var step1 = step.rewrite(path.concat('/left'), fact1);
      var p2 = path.adjustForRewrite(step, step1);
      var fact2 = rules.instVar(fact, Toy.numify(k2), 'c');
      return (step1.rewrite(p2.concat('/right'), fact2)
              .justify('commonDenominator', arguments, [step]));
    },
    toOffer: function(step, expr) {
      var map = (expr.matchSchema('a / d1 + b / d2') ||
                 expr.matchSchema('a / d1 - b / d2'));
      return (map && map.d1.isNumeral() && map.d2.isNumeral());
    },
    inputs: {site: 1, term: 3},
    form: 'Use denominator <input name=term>',
    menu: 'use common denominator',
    labels: 'algebra'
  },

  /**
   * Given a numeric term (integer) that has prime factors, produce a
   * step that equates it to its prime factors.
   */
  primeFactors: {
    action: function(term_arg) {
      var term = termify(term_arg);
      var factors = [];
      if (term.isNumeral()) {
        factors = Toy.primeFactors(term.getNumValue());
      }
      assert(factors.length > 0, 'Does not have prime factors: {1}', term);
      var product = new Toy.numify(factors[0]);
      for (var i = 1; i < factors.length; i++) {
        product = Toy.infixCall(product, '*', new Toy.numify(factors[i]));
      }
      var step = rules.consider(Toy.infixCall(term, '=', product));
      return (rules.simplifySite(step, '/left')
              .andThen('fromTIsA')
              .justify('primeFactors', [term]));
    },
    inputs: {term: 1},
    form: '',
    menu: 'prime factors of {term}',
    description: 'prime factors of {term}',
    labels: 'algebra',
    toOffer: function(step, expr) {
      return expr && expr.isNumeral();
    },
    autoSimplify: noSimplify
  }

};  // End fractionsInfo.


//
// These are algebra facts.
//

var algebraFacts = {};

var realAxiomFacts = {

  // Axioms

  'a + b = b + a': {
    proof: function() {
      return rules.axiomCommutativePlus();
    },
    labels: 'algebra',
    noSwap: true
  },
  'a * b = b * a': {
    proof: function() {
      return rules.axiomCommutativeTimes();
    },
    labels: 'algebra',
    noSwap: true
  },
  'a + (b + c) = a + b + c': {
    proof: function() {
      return rules.axiomAssociativePlus();
    },
    labels: 'algebra',
    converse: { labels: 'algebra2' }
  },
  'a * (b * c) = a * b * c': {
    proof: function() {
      return rules.axiomAssociativeTimes();
    },
    labels: 'algebra',
    converse: { labels: 'algebra2' }

  },
  'a + 0 = a': {
    simplifier: true,
    proof: function() {
      return rules.axiomPlusZero();
    }
  },
  'a * 1 = a': {
    simplifier: true,
    proof: function() {
      return rules.axiomTimesOne();
    }
  },
  'a * 0 = 0': {
    simplifier: true,
    proof: function() {
      return rules.axiomTimesZero();
    }
  },
  'not (R none)': {
    proof: function() {
      return rules.axiomRealNotNull();
    }
  }
};
$.extend(algebraFacts, realAxiomFacts);


var basicFacts = {
  '@R a => a != none': {
    proof: function() {
      var asm = rules.assume('a = none');
      return (rules.fact('not (R none)')
              .rplace('/arg/arg', rules.eqnSwap(asm))
              .andThen('asImplication')
              .andThen('forwardChain', 'a => not b == b => not a')
              .andThen('simplifySite', '/right'));
    }
  },

  'a + neg a = 0': {
    simplifier: true,
    proof: function() {
      return rules.eqSelf('a + neg a')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c')
      .andThen('arithmetic', '/main/right/left')
      .rewrite('/main/right', '0 * a = 0');
    }
  },
  '@R a & a != 0 => a * recip a = 1': {
    proof: function() {
      return rules.axiomReciprocal();
    }
  },
  'a * b != 0 == a != 0 & b != 0': {
    proof: function() {
      return rules.factNonzeroProduct();
    }
  },
  'a = b == b = a': {
    proof: function() {
      return rules.equalitySymmetric();
    },
    noSwap: true,
    labels: 'algebra'
  },

  // Addition
  'a + b + c = a + c + b': {
    proof: function() {
      var step = rules.consider('a + b + c')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + b = b + a')
      .rewrite('/main/right', 'a + (b + c) = a + b + c');
      return step;
    }
  },
  'a + b + c = a + (c + b)': {
    proof: function() {
      return rules.consider('a + b + c')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)');
    }
  },

  // Multiplication
  'a * b * c = a * c * b': {
    proof: function() {
      var step = rules.consider('a * b * c')
      .rewrite('/main/right', 'a * b * c = a * (b * c)')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b * c) = a * b * c');
      return step;
    }
  },
  'a * b * c = a * (c * b)': {
    proof: function() {
      return (rules.fact('a * b * c = a * (b * c)')
              .rewrite('/main/right/right', 'a * b = b * a'));
    }
  }
};
$.extend(algebraFacts, basicFacts);

// Distributivity
var distribFacts = {
  'a * (b + c) = a * b + a * c': {
    proof: function() {
      return rules.axiomDistributivity();
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  '(a + b) * c = a * c + b * c': {
    proof: function() {
      var step = rules.consider('(a + b) * c')
      .rewrite('/main/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right/left', 'a * b = b * a');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  'a * b + b = (a + 1) * b': {
    proof: function() {
      var step = rules.consider('a * b + b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  'b + a * b = (1 + a) * b': {
    proof: function() {
      var step = rules.consider('b + a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  'a + a = 2 * a': {
    proof: function() {
      return rules.consider('a + a')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * b + b = (a + 1) * b')
      .andThen('arithmetic', '/main/right/left');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },

  // Distributivity with subtraction

  'a * (b - c) = a * b - a * c': {
    proof: function() {
      return rules.consider('a * (b - c)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * neg b = neg (a * b)')
      .rewrite('/main/right', 'a + neg b = a - b');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  '(a - b) * c = a * c - b * c': {
    proof: function() {
      var step = rules.consider('(a - b) * c')
      .rewrite('/main/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b - c) = a * b - a * c')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right/left', 'a * b = b * a');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  'a * b - b = (a - 1) * b': {
    proof: function() {
      return rules.consider('a * b - b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  'b - a * b = (1 - a) * b': {
    proof: function() {
      return rules.consider('b - a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  }
};

// TODO: Need distributivity of division over addition and subtraction.


// Private to isDistribFact.  A mapping from statement key to value
// that is truthy iff the statement is in distribFacts.
var _distribFactsTable;

// Initialization deferred until initialization makes parsing and thus
// getStatementKey available.
$(function() {
    var table = {};
    for (var key in distribFacts) {
      table[Toy.getStatementKey(key)] = true;
    }
    _distribFactsTable = table;
  });

/**
 * Returns a truthy value iff the statement is some version
 * of the distributed law in distribFacts.
 */
function isDistribFact(stmt) {
  return !!_distribFactsTable[Toy.getStatementKey(stmt)];
}
$.extend(algebraFacts, distribFacts);

var identityFacts = {
  // Plus zero
  /* Omit from UI: somewhat redundant
  'a = 0 + a': {
   proof: function() {
     var step1 = rules.axiomPlusZero();
     var step2 = rules.eqnSwap(step1);
     var step3 = rules.rewrite(step2, '/main/right',
                               'a + b = b + a');
     return step3;
     }
   },
  */
  '0 + a = a': {
    simplifier: true,
    proof: function() {
      var step1 = rules.axiomPlusZero();
      var step2 = rules.rewrite(step1, '/main/left',
                                'a + b = b + a');
      return step2;
    }
  },
  'a - 0 = a': {
    simplifier: true,
    proof: function() {
      var step1 = (rules.consider('a - 0')
                   .andThen('apply', '/main/right')
                   .andThen('arithmetic', '/main/right/right')
                   .rewrite('/main/right', 'a + 0 = a'));
      return step1;
    }
  },
  '0 - a = neg a': {
    proof: function() {
      var step1 = (rules.consider('0 - a')
                   .andThen('apply', '/main/right')
                   .rewrite('/main/right', '0 + a = a'));
      return step1;
    }
  },
  // Times one
  '1 * a = a': {
    simplifier: true,
    proof: function() {
      var step1 = rules.axiomTimesOne();
      var step2 = rules.rewrite(step1, '/main/left',
                                'a * b = b * a');
      return step2;
    }
  },

  // Zero times
  '0 * a = 0': {
    simplifier: true,
    proof: function() {
      return rules.axiomTimesZero()
      .rewrite('/main/left', 'a * b = b * a');
    }
  }
};
$.extend(algebraFacts, identityFacts);

var equivalences = {

  'a = b == a + c = b + c': {
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '+', 'c')
                     .andThen('asImplication'));
      var back = (rules.assume('a + c = b + c')
                  .andThen('applyToBothWith', '-', 'c')
                  .andThen('groupToRight', '/main/left/left/right')
                  .andThen('simplifySite', '/main/left')
                  .andThen('groupToRight', '/main/right/left/right')
                  .andThen('simplifySite', '/main/right')
                  .andThen('extractHyp', 'a + c = b + c'))
      var conj = rules.makeConjunction(forward, back);
      return rules.forwardChain(conj, '(p => q) & (q => p) == (p == q)');
    }
  },

  'a = b == a - c = b - c': {
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '-', 'c')
                     .andThen('asImplication'));
      var back = (rules.assume('a - c = b - c')
                  .andThen('applyToBothWith', '+', 'c')
                  .andThen('groupToRight', '/main/left/left/right')
                  .andThen('simplifySite', '/main/left')
                  .andThen('groupToRight', '/main/right/left/right')
                  .andThen('simplifySite', '/main/right')
                  .andThen('extractHyp', 'a - c = b - c'))
      var conj = rules.makeConjunction(forward, back);
      return rules.forwardChain(conj, '(p => q) & (q => p) == (p == q)');
    }
  },

  // This is primarily a lemma for the following equivalence.
  'c != 0 => (a * c = b * c => a = b)': {
    // TODO: Figure out why the user must enter the c != 0 part
    //   when working interactively.
    proof: function() {
      var rewrite = rules.rewrite;
      var s1 = rules.assume('a * c = b * c');
      var s2 = rules.applyToBothWith(s1, '/', 'c');
      var s3 = rewrite(s2, '/main/right', 'a * b / c = a * (b / c)');
      var s6 = rewrite(s3, '/main/left', 'a * b / c = a * (b / c)');
      var s7 = rules.simplifyStep(s6);
      var s8 = rules.extractHyp(s7, 'a * c = b * c');
      return s8;
    }
  },

  'c != 0 => (a = b == a * c = b * c)': {
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '*', 'c')
                     .andThen('asImplication'));
      var back = rules.fact('c != 0 => (a * c = b * c => a = b)');
      var conj = rules.makeConjunction(forward, back);
      var taut = rules.tautology('(a => b) & (b => a) == (a == b)');
      var result = rules.forwardChain(conj, taut);
      return result;
    }
  },

  // This is primarily a lemma for the following equivalence.
  'c != 0 => (a / c = b / c => a = b)': {
    // TODO: Figure out why the user must enter the c != 0 part
    //   when working interactively.
    proof: function() {
      var regroup = rules.fact('a / b * c = a * (c / b)');
      var cancel = rules.fact('a != 0 => a / a = 1');
      return (rules.assume('a / c = b / c')
              .andThen('applyToBothWith', '*', 'c')
              .rewrite('/main/right', regroup)
              .rewrite('/main/right/right', cancel)
              .rewrite('/main/left', regroup)
              .rewrite('/main/left/right', cancel)
              .andThen('simplifyStep')
              .andThen('extractHyp', 'a / c = b / c'));
    }
  },

  'c != 0 => (a = b == a / c = b / c)': {
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '/', 'c')
                     .andThen('asImplication'));
      var back = rules.fact('c != 0 => (a / c = b / c => a = b)');
      var conj = rules.makeConjunction(forward, back);
      return rules.forwardChain(conj, '(p => q) & (q => p) == (p == q)');
    }
  }
};
$.extend(algebraFacts, equivalences);


/*
  // Since functions are total, an operation such as x / 0 has a value,
  // though the value might not be a number.  Thus an equation such as
  // x / (1 - x) = 1 / (1 - x) is true when x = 1 since 1 / 0 = 1 / 0,
  // with the same operations being applied to the same inputs.

  // It is logically correct to allow x = 1 as a solution to the
  // equation x / (1 - x) = 2 / (1 - x).  Even if such problems are
  // not stated with the side conditions that avoid zero denominators,
  // the fact that x / x = 1 == x != 0 prevents inconsistency.

  // In textbook math, a solution is only considered valid if it
  // results in values outside the domain, usually the real numbers.
  // An implementable approach to this is to state the problem with
  // the side condition, e.g. if the given is X1 / X2 = X3 (where the
  // Xes are expressions), state the problem as X1 / X2 = X3 and X2 !=
  // 0, on the grounds that the values involved will not be real
  // numbers ("undefined").

  // Note: we could use the following to generate the side condition.
  // (a = b | c = 0) == a * c = b * c
  //   and therefore
  // c != 0 => (a = b == a * c = b * c)
  //   and so
  // (c != 0 & a = b) == (c != 0 & a * c = b * c)
  // This lets us multiply both sides when appropriate.

  // We could use the following to eliminate the side condition
  // (for example in case a is <expr> = 0):
  // ((!a => (b == c)) & (a => !b) & (a => !c)) => (b == c)
  //
  // In the usual use case b is an equation to solve and c is the
  // solution.  This works for most division by zero situations, where
  // a is X = 0 for an expression X, but if both sides of b have the
  // same denominator, for example, it will be true when that
  // denominator is zero, so this approach will not apply.
  //
  // Unfortunately, eliminating the side condition in this way is
  // probably not great for educational purposes because the reasoning
  // involves "undefined" terms.
  //
  */

var negationFacts = {
  // Negation rules
  'a - b = a + neg b': {
    proof: function() {
      var step1 = rules.consider('a - b');
      var step2 = rules.apply(step1, '/main/right');
      return step2;
    }
  },
  'a - neg b = a + b': {
    proof: function() {
      return rules.consider('a - neg b')
      .andThen('apply', '/main/right')
      .rewrite('/main/right/right', 'neg (neg a) = a');
    }
  },
  'neg a + b = b - a': {
    proof: function() {
      var parse = Toy.justParse;
      return rules.fact('a + neg b = a - b')
        .rewrite('/main/left', 'a + b = b + a');
        // .andThen('instMultiVars', {a: parse('b'), b: parse('a')});
    }
  },
  'a - b = neg b + a': {
    proof: function() {
      return rules.fact('a + neg b = a - b')
      .andThen('eqnSwap')
      .rewrite('/main/right', 'a + b = b + a');
    }
  },
  'neg a + a = 0': {
    proof: function() {
      return rules.fact('a + neg a = 0')
      .rewrite('/main/left', 'a + b = b + a');
    }
  },
  'neg (neg a) = a': {
    proof: function() {
      return rules.fact('neg a + a = 0')
      .andThen('instVar', 'neg a', 'a')
      .andThen('applyToBothWith', '+', 'a')
      .rewrite('/main/left', 'a + b + c = a + (b + c)')
      .rewrite('/main/left/right', 'neg a + a = 0')
      .rewrite('/main/left', 'a + 0 = a')
      .rewrite('/main/right', '0 + a = a');
    }
  },
  'a + neg b + b = a': {
    proof: function() {
      return rules.consider('a + neg b + b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'neg a + a = 0')
      .rewrite('/main/right', 'a + 0 = a');
    }
  },
  'a + b + neg b = a': {
    proof: function() {
      return rules.consider('a + b + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg a = 0')
      .rewrite('/main/right', 'a + 0 = a');
    }
  },

  // Negation with multiplication
  '@neg a = -1 * a': {
    proof: function() {
      return rules.axiomNeg();
    }
  },
  'neg (a * b) = neg a * b': {
    proof: function() {
      return rules.consider('neg (a * b)')
      .rewrite('/main/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * (b * c) = (a * b) * c')
      .rewrite('/main/right/left', '-1 * a = neg a');
    }
  },
  'a * neg b = neg (a * b)': {
    proof: function() {
      return rules.consider('a * neg b')
      .rewrite('/main/right/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right/left', 'a * b = b * a')
      .rewrite('/main/right', 'a * b * c = a * (b * c)')
      .rewrite('/main/right', '-1 * a = neg a');
    }
  },
  'a * neg b = neg a * b': {
    proof: function() {
      return rules.fact('a * neg b = neg (a * b)')
      .rewrite('/main/right', 'neg (a * b) = neg a * b');
    }
  },

  // Negation with division
  'neg (a / b) = neg a / b': {
    proof: function() {
      return (rules.consider('neg (a / b)')
              .rewrite('/main/right', 'neg a = -1 * a')
              .rewrite('/main/right', 'a * (b / c) = a * b / c')
              .rewrite('/main/right/left', '-1 * a = neg a'));
    }
  },

  // Other negation facts
  'neg (a + b) = neg a + neg b': {
    proof: function() {
      var rewrite = rules.rewrite;
      var step1 = rules.fact('a + neg a = 0');
      var step2 = rules.instVar(step1, Toy.parse('a + b'), 'a');
      var step3 = rewrite(step2, '/right/left',
                                        'a + b + c = a + c + b');
      var step4 = rules.applyToBothWith(step3, '+', 'neg b')
      var step5 = rewrite(step4, '/right/left', 'a + b + c = a + (b + c)');
      var step6 = rewrite(step5, '/right/left/right', 'a + neg a = 0');
      var step7 = rewrite(step6, '/right/right', '0 + a = a');
      var step8 = rewrite(step7, '/right/left', 'a + 0 = a');
      var step9 = rules.applyToBothWith(step8, '+', 'neg a');
      var step10 = rewrite(step9, '/right/left/left', 'a + b = b + a');
      var step11 = rewrite(step10, '/right/left', 'a + b + c = a + (b + c)');
      var step12 = rewrite(step11, '/right/left/right', 'a + neg a = 0');
      var step13 = rewrite(step12, '/right/left', 'a + 0 = a');
      var step14 = rewrite(step13, '/right/right', 'a + b = b + a');
      return step14;
    }
  },
  'neg (a - b) = b - a': {
    proof: function() {
      return rules.consider('neg (a - b)')
      .rewrite('/main/right/arg', 'a - b = a + neg b')
      .rewrite('/main/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right', 'neg (neg a) = a')
      .rewrite('/main/right', 'a + b = b + a')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  'neg (a - b) = neg a + b': {
    proof: function() {
      return rules.consider('neg (a - b)')
      .rewrite('/main/right/arg', 'a - b = a + neg b')
      .rewrite('/main/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right', 'neg (neg a) = a');
    }
  },
  'b != 0 => neg a / neg b = a / b': {
    proof: function() {
      return rules.consider('neg a / neg b')
      .rewrite('/main/right/left', 'neg a = -1 * a')
      .rewrite('/main/right/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a / (b * c) = a / b / c')
      .rewrite('/main/right/left', 'a * b / c = a / c * b')
      .andThen('arithmetic', '/main/right/left/left')
      .rewrite('/main/right/left', '1 * a = a');
    }
  }
};
$.extend(algebraFacts, negationFacts);

var subtractionFacts = {
  // Subtraction facts

  // Moving terms to the left
  'a + b - c = a - c + b': {
    proof: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right/left', 'a + neg b = a - b');
    }
  },
  'a - b + c = a + c - b': {
    proof: function() {
      return rules.consider('a - b + c')
      .rewrite('/main/right/left', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  'a - b + c = a + (c - b)': {
    proof: function() {
      return rules.fact('a - b + c = a + c - b')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg b = a - b');
    }
  },
  'a - (b - c) = a + (c - b)': {
    proof: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right/right', 'neg (a - b) = b - a');
    }
  },
  'a - (b - c) = a + c - b': {
    proof: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right', 'a - (b - c) = a + (c - b)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },

  // Associativity: four cases: each operation can be + or -, and
  // initial association can be to the left or right.
  'a + b - c = a + (b - c)': {
    proof: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg b = a - b');
    },
    labels: 'algebra2',
    converse: { labels: 'algebra' }
  },
  'a - (b + c) = a - b - c': {
    proof: function() {
      var step = rules.consider('a - (b + c)')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right/right',
               'neg (a + b) = neg a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', 'a + neg b = a - b')
      .rewrite('/main/right/left', 'a + neg b = a - b');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra2' }
  },  
  'a - b - c = a - c - b': {
    proof: function() {
      return rules.consider('a - b - c')
      .rewrite('/main/right/left', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b - c = a - c + b')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  'a - (b - c) = a - b + c': {
    proof: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right/right', 'neg (neg a) = a')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right/left', 'a + neg b = a - b');
    },
    labels: 'algebra',
    converse: { labels: 'algebra2' }
  },

  // Simplification
  'a - a = 0': {
    simplifier: true,
    proof: function() {
      return (rules.eqSelf('a - a')
              .andThen('apply', '/right')
              .rewrite('/main/right', 'a + neg a = 0'));
    }
  },

  'a + b - b = a': {
    proof: function() {
      return (rules.consider('a + b - b')
              .rewrite('/main/right', 'a + b - c = a + (b - c)')
              .rewrite('/main/right/right', 'a - a = 0')
              .rewrite('/main/right', 'a + 0 = a'));
    }
  },

  'a - b + b = a': {
    proof: function() {
      return (rules.consider('a - b + b')
              .rewrite('/main/right', 'a - b + c = a + c - b')
              .rewrite('/main/right', 'a + b - b = a'));
    }
  }
};
$.extend(algebraFacts, subtractionFacts);

var recipFacts = {
  // Reciprocal facts

  'a != 0 => recip a * a = 1': {
    proof: function() {
      return rules.axiomReciprocal()
      .rewrite('/main/left', 'a * b = b * a');
    }
  },
  'a != 0 => recip a != 0': {
    proof: function() {
      var step1 = rules.axiomReciprocal();
      var step2 = rules.fact('1 != 0');
      var step3 = rules.rRight(step1, step2, '/left')
      .rewrite('/main', 'a * b != 0 == a != 0 & b != 0');
      var step4 = rules.tautology('a & b => b');
      var step5 = rules.forwardChain(step3, step4);
      return step5;
    }
  },
  'a / b = a * recip b': {
    proof: function() {
      var step1 = rules.consider('a / b');
      var step2 = rules.apply(step1, '/main/right');
      return step2;
    }
  },
  'a != 0 => recip a = 1 / a': {
    proof: function() {
      return rules.consider('recip s')
      .rewrite('/main/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * recip b = a / b');
    }
  },
  'a != 0 => recip (recip a) = a': {
    proof: function() {
      var rewrite = rules.rewrite;
      var step1 = rules.fact('a * recip a = 1');
      var step2 = rules.applyToBothWith(step1, '*', Toy.parse('recip (recip a)'));
      var step3 = rewrite(step2, '/main/right', '1 * a = a');
      var step4 = rewrite(step3, '/main/left', 'a * b * c = a * (b * c)');
      var step5 = rules.instVar(step1, Toy.parse('recip a'), 'a');
      var step6 = rules.rplace(step5, step4, '/main/left/right');
      var step7 = rewrite(step6, '/main/left', 'a * 1 = a');
      var step8 = rules.eqnSwap(step7);
      return step8;
    }
  },
  '@R (recip a) & recip a != 0 => R a & a != 0': {
    proof: function() {
      var taut = rules.tautology('(a == b) => (a => b)');
      var fact = rules.axiomReciprocal2();
      return rules.forwardChain(fact, taut);
    }
  },
  '@R a & a != 0 => R (recip a) & recip a != 0': {
    proof: function() {
      var taut = rules.tautology('(a == b) => (b => a)');
      var fact = rules.axiomReciprocal2();
      return rules.forwardChain(fact, taut);
    }
  },
  'a != 0 & b != 0 => recip (a * b) = recip a * recip b': {
    proof: function() {
      var rewrite = rules.rewrite;
      var step1 = rules.fact('a * recip a = 1');
      var step2 = rules.instVar(step1, Toy.parse('a * b'), 'a');
      var step3 = rewrite(step2, '/right/left', 'a * b * c = a * c * b');
      var step4 = rules.applyToBothWith(step3, '*', Toy.parse('recip b'));
      var step5 = rewrite(step4, '/right/left', 'a * b * c = a * (b * c)');
      var step6 = rewrite(step5, '/right/left/right', 'a * recip a = 1');
      var step7 = rewrite(step6, '/right/right', '1 * a = a');
      var step8 = rewrite(step7, '/right/left', 'a * 1 = a');
      var step9 = rules.applyToBothWith(step8, '*', Toy.parse('recip a'));
      var step10 = rewrite(step9, '/right/left/left', 'a * b = b * a');
      var step11 = rewrite(step10, '/right/left', 'a * b * c = a * (b * c)');
      var step12 = rewrite(step11, '/right/left/right', 'a * recip a = 1');
      var step13 = rewrite(step12, '/right/left', 'a * 1 = a');
      var step14 = rewrite(step13, '/right/right', 'a * b = b * a');
      return step14;
    }
  }
};
$.extend(algebraFacts, recipFacts);

var divisionFacts = {
  // Division rules

  'c != 0 => a * b / c = a / c * b': {
    proof: function() {
      var step = rules.consider('a * b / c')
      .rewrite('/main/right', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * b * c = a * c * b')
      .rewrite('/main/right/left', 'a * recip b = a / b');
      return step;
    }
  },
  'b != 0 => a / b * c = a * c / b': {
    proof: function() {
      var step = rules.consider('a / b * c')
      .rewrite('/main/right/left', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * b * c = a * c * b')
      .rewrite('/main/right', 'a * recip b = a / b');
      return step;
    }
  },
  'b != 0 => a / b * c = a * (c / b)': {
    proof: function() {
      var divFact = rules.fact('a * recip b = a / b');
      return (rules.fact('a * b * c = a * (c * b)')
              .andThen('instVar', 'recip d', 'b')
              .rewrite('/main/right/right', divFact)
              .rewrite('/main/left/left', divFact));
    }
  },
  'b != 0 & c != 0 => a / (b * c) = a / b / c': {
    proof: function() {
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
  'c != 0 => a * (b / c) = a * b / c': {
    proof: function() {
      var step = rules.consider('a * (b / c)')
      .rewrite('/main/right/right', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right', 'a * recip b = a / b');
      return step;
    }
  },
  'a != 0 => a / a = 1': {
    simplifier: true,
    proof: function() {
      var fact = rules.fact('a / b = a * recip b').andThen('eqnSwap');
      return (rules.fact('a != 0 => a * recip a = 1')
              .rewrite('/main/left', fact));
    }
  },
  'b != 0 => a = a * b / b': {
    proof: function() {
      var fact = rules.fact('1 = (a / a)').andThen('instVar', 'b', 'a');
      return (rules.consider('a')
              .rewrite('/right', 'a = a * 1')
              .rewrite('/right/right/right', fact)
              .rewrite('/right/right', 'a * (b / c) = a * b / c'));
    },
  },
  // This is useful for converting a summand to a fraction like
  // its neighbor.
  '@R b & R c & c != 0 => a / c + b = a / c + b * c / c': {
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a / c + b')
              .rewrite('/right/right', fact));
    },
    labels: 'algebra'
  },
  // Likewise useful for converting a summand to a fraction like
  // its neighbor.
  '@R b & R c & c != 0 => a + b / c = a * c / c + b / c': {
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a + b / c')
              .rewrite('/right/left', fact));
    },
    labels: 'algebra'
  },
  // Similar to the above, but now for subtraction rather than addition.
  '@R b & R c & c != 0 => a / c - b = a / c - b * c / c': {
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a / c - b')
              .rewrite('/right/right', fact));
    },
    labels: 'algebra'
  },
  // More of the same.
  '@R b & R c & c != 0 => a - b / c = a * c / c - b / c': {
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a - b / c')
              .rewrite('/right/left', fact));
    },
    labels: 'algebra'
  },
  'b != 0 & c != 0 => a / b = (a * c) / (b * c)': {
    proof: function() {
      var fact = rules.fact('1 = (a / a)').andThen('instVar', 'c', 'a');
      return (rules.consider('a / b')
              .rewrite('/right', 'a = (a * 1)')
              .rewrite('/right/right/right', fact)
              .rewrite('/right/right', 'c != 0 => a / c * b = a * b / c')
              .rewrite('/right/right/left', 'c != 0 => a * (b / c) = a * b / c')
              .rewrite('/right/right', 'b != 0 & c != 0 => a / b / c = a / (b * c)')
              .rewrite('/right/right/right', 'a * b = b * a'))
    },
    labels: 'algebra'
  },
  'b != 0 & c != 0 => a / b = (a / c) / (b / c)': {
    proof: function() {
      return (rules.fact('a / b = (a * c) / (b * c)')
              .andThen('instVar', 'recip c', 'c')
              .rewrite('/right/right/left', 'a * recip b = a / b')
              .rewrite('/right/right/right', 'a * (recip b) = a / b'));
    }
  },
  // Distributivity:
  'c != 0 => (a + b) / c = a / c + b / c': {
    proof: function() {
      var tx = Toy.transformApplyInvert;
      var mp = Toy.mathParse;
      return tx(Toy.parse('(a + b) / c'),
                mp('a / b = a * recip b'),
                mp('(a + b) * c = a * c + b * c'))
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
  // Distributivity:
  'c != 0 => (a - b) / c = a / c - b / c': {
    proof: function() {
      var tx = Toy.transformApplyInvert;
      var mp = Toy.mathParse;
      return tx(Toy.parse('(a - b) / c'),
                mp('a / b = a * recip b'),
                mp('(a - b) * c = a * c - b * c'))
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  }
};
$.extend(algebraFacts, divisionFacts);

var powerFacts = {
  'a ** 1 = a': {
    proof: function() {
      return rules.axiomNextPower()
      .andThen('instMultiVars', {x: Toy.parse('a'), y: Toy.parse('0')})
      .andThen('arithmetic', '/main/left/right')
      .rewrite('/main/right/left', rules.axiomPower0())
      .rewrite('/main/right', '1 * a = a');
    }
  },
  'a ** 2 = a * a': {
    proof: function() {
      return rules.axiomNextPower()
      .andThen('instVar', '1', 'y')
      .rewrite('/main/right/left', 'a ** 1 = a')
      .andThen('arithmetic', '/main/left/right');
    }
  },
  // TODO: Add a rule to convert a ** n to multiplication for any
  // non-negative integer n.
  'a ** 3 = a * a * a': {
    proof: function() {
      return rules.axiomNextPower()
      .andThen('instVar', '2', 'y')
      .rewrite('/main/right/left', 'a ** 2 = a * a')
      .andThen('arithmetic', '/main/left/right');
    }
  }
};
$.extend(algebraFacts, powerFacts);


// MOVING EXPRESSIONS AROUND

var algebraIdentities = {
  'a = neg b == a + b = 0': {
    proof: function() {
      var step = rules.assume('a = neg b')
      .andThen('applyToBothWith', '+', 'b')
      .rewrite('/main/right', 'neg a + a = 0')
      .andThen('extractHyp', 'a = neg b');
      var converse = rules.assume('a + b = 0')
      .andThen('applyToBothWith', '+', 'neg b')
      .rewrite('/main/right', '0 + a = a')
      .rewrite('/main/left', 'a + b + c = a + (b + c)')
      .rewrite('/main/left/right', 'a + neg a = 0')
      .rewrite('/main/left', 'a + 0 = a')
      .andThen('extractHyp', 'a + b = 0');
      var conj = rules.makeConjunction(step, converse);
      var taut = rules.tautology('(a => b) & (b => a) == (a == b)');
      return rules.rewriteOnly(conj, '/main', taut);

    }
  },
  'a = b == a - b = 0': {
    proof: function() {
      return rules.fact('a = neg b == a + b = 0')
      .andThen('instVar', 'neg b', 'b')
      .rewrite('/main/left/right', 'neg (neg a) = a')
      .rewrite('/main/right/left', 'a + neg b = a - b');
    }
  }
};
$.extend(algebraFacts, algebraIdentities);

/**
 * Basic simplification facts for algebra, used in _simplifyMath1
 * and related places.
 *
 * TODO: Consider -1 * a = neg a; a + a = 2 * a;
 *   Consider whether x - 7 is simpler than x + -7.
 */
var basicSimpFacts = [
                      'not (a = b) = (a != b)',
                      'a - a = 0',
                      'a + neg a = 0',
                      'a + 0 = a',
                      '0 + a = a',
                      'a * 1 = a',
                      '1 * a = a',
                      'a - 0 = a',
                      '0 * a = 0',
                      'a * 0 = 0',
                      'a != 0 => a / a = 1',
                      {stmt: 'a + neg b = a - b',
                       where: '!$.b.isNumeral()'},
                      {stmt: 'a - b = a + neg b',
                       where: '$.b.isNumeral() && $.b.getNumValue() < 0'},
                      {apply: function(term, cxt) {
                          return (isArithmetic(term) &&
                                  rules.axiomArithmetic(term)); } }
                      ];


//// Export public names.

Toy.algebraFacts = algebraFacts;
Toy.distribFacts = distribFacts;
Toy.basicSimpFacts = basicSimpFacts;
Toy.isDistribFact = isDistribFact;
Toy.termGetRightVariable = termGetRightVariable;
Toy.varFactorCounts = varFactorCounts;
Toy.termLeftThan = termLeftThan;
Toy.tryArithmetic = tryArithmetic;
Toy.isArithmetic = isArithmetic;


//// INITIALIZATION CODE

// Do this after support modules are initialized.
$(function() {
    Toy.addRules(numbersInfo);
    Toy.addRules(equationOpsInfo);
    Toy.addRules(simplifiersInfo);
    Toy.addRules(moversInfo);
    Toy.addRules(fractionsInfo);
    Toy.addFactsMap(algebraFacts);
});

})();
