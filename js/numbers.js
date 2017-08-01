// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

// Set all of this up immediately upon load, but avoiding changes
// to the global environment (except through the "Toy" namespace).
(function() {

//// THEOREMS AND RULES

var rules = Toy.rules;

var assert = Toy.assertTrue;
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
var noSimplify = Toy.noSimplify;


//// Utility functions

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
//// Definitions
////

$(function() {
    var define = Toy.define;
    define('neg', '{x. -1 * x}');
    define('-', '{x. {y. x + neg y}}');
    define('/', '{x. {y. the {z. x = y * z}}}');
    define('recip', '{x. 1 / x}');
  });


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

  // TODO: Make this a theorem someday.
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

  // Some interim "axioms" to be replaced by proved facts.

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

  axiomDivisionType: {
    statement: '@R x & R y & y != 0 == R (x / y)'
  },

  axiomStrictPlus: {
    statement: '@not (R (x + y)) == (x + y = none)'
  },

  axiomStrictTimes: {
    statement: '@not (R (x * y)) == (x * y = none)'
  },

  axiomStrictNeg: {
    statement: '@not (R (neg x)) == neg x = none'
  },

  axiomStrictRecip: {
    statement: '@not (R (recip x)) == recip x = none'
  },

  // End of interim axioms.

  // Evaluates arithmetic expressions with operators: +, -, *, /, div,
  // mod, neg, =, !=, >, >=, <, <=, and the type operator "R".  Checks
  // that inputs are all numeric and that the result can be guaranteed
  // to be an exact integer.
  //
  // Result is always an equation (or biconditional) with the given
  // term as the LHS.  Throws an error if it cannot obey these
  // specifications.
  axiomArithmetic: {
    action: function(term_arg) {
      var term = termify(term_arg);
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
          assert(right !== 0, 'Cannot divide by zero');
          value = left / right;
          // abs(value) <= abs(left) since abs(right) >= 1 so the
          // magnitude is not a problem.  The fractional part of a
          // result must have denominator no greater than MAX_INT,
          // so it should be distinguishable from an integer.
          if (value !== Math.floor(value)) {
            Toy.fail('Inexact division');
          }
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
        assert(op.isConst(), 'Unsupported operator: {1}', op);
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

  reciprocalType: {
    statement: '@R x & x != 0 == R (recip x)',
    // TODO: Prove me!
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
          Toy.fail('Not an arithmetic expression: {1}', term);
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
      var step3 = rules.rplaceEither(step1, '/main/right/right', eqn2);
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
      var step3 = rules.rplaceEither(step1, '/main/right/right', eqn2);
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

var ungroupingFacts;
$(function() {
    ungroupingFacts = regroupingFacts.map(function(fact) {
        return Toy.commuteEqn(termify(fact));
      });
  });

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
 * This does the auto-simplification for add/subtract both sides.  It
 * tries regrouping and then possible simplification.
 *
 */
function simplifyAddSubBoth(step, eqnPath) {
  var right = eqnPath.concat('/right');
  var left = eqnPath.concat('/left');
  var step1 = rules.arrangeSum(step, right);
  var step2 = rules.arrangeSum(step1, left);
  return rules.simplifyStep(step2);
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
  //
  // Note that when rearranging terms as with commutativity and
  // associativity, it is efficient to defer this simplification
  // until all rearrangements are completed.
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
      var divider = proveIsT(rules.axiomDivisionType());
      var negger = memo(function() {
          return rules.axiomNegType().andThen('eqnSwap');
        });
      // x != 0 => (R (recip x) == R x)
      var reciper = memo(function() {
          var step = rules.reciprocalType();
          var schema = rules.tautology('(a & b == c) => (b => (c == a))');
          // TODO: Add assumptions to the schema?
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
            return proveIsT(rules.fact('recip a != 0'));
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
  //   different possible renderings.  Probably make it accept a
  //   site, which in the UI is determined by the visible part.
  simplifyStep: {
    action: function(step) {
      var visPath = step.pathToVisiblePart();
      if (step.get(visPath).isCall2('=')) {
        // Why this special case?
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
        console.trace(Toy.format('No term in {1} at path {2}', step, path));
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
        // This check relies on _simplifyMath1 trying first to simplify
        // the whole term.
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

  // Uses the associative law to "flatten" an expression made
  // up of additions and subtractions.
  flattenSum: {
    data: {flatteners: [
           {stmt: 'a + (b + c) = a + b + c'},
           {stmt: 'a + (b - c) = a + b - c'},
           {stmt: 'a - (b + c) = a - b - c'},
           {stmt: 'a - (b - c) = a - b + c'},
           {descend:
            {schema: 'a + b',
             parts: {a: 'flatteners', b: 'flatteners'}}},
           {descend:
            {schema: 'a - b',
             parts: {a: 'flatteners', b: 'flatteners'}}}]
    },
    action: function(step, path) {
      var context = {factLists: {flatteners: this.data.flatteners}};
      return convert(step, path, function(expr) {
          var arrangeRhs = Toy.arrangeRhs;
          var eqn = rules.consider(step.get(path));
          var flat = arrangeRhs(eqn, context, 'flatteners');
          return flat;
        }).justify('flattenSum', arguments, [step]);
    },
    inputs: {site: 1},
    toOffer: function(step, term) {
      return (term.matchSchema('a + b') || term.matchSchema('a - b'));
    },
    offerExample: true,
    form: '',
    menu: 'algebra: flatten {term}',
    description: 'flatten term {site};; {in step siteStep}',
    labels: 'algebra'
  },

  // In a flattened sequence of additions and subtractions, this
  // moves all the numeric terms to the end.
  arrangeSum: {
    action: function(step, path) {
      var numeralBefore = '$.b.isNumeral() && !$.c.isNumeral()';
      var numRightMovers = [
        {stmt: 'a + b = b + a',
         where: '$.a.isNumeral() && !$.b.isNumeral()'},
        {stmt: 'a - b = neg b + a',
         where: '$.a.isNumeral() && !$.b.isNumeral()'},
        {stmt: 'a + b + c = a + c + b', where: numeralBefore},
        {stmt: 'a + b - c = a - c + b', where: numeralBefore},
        {stmt: 'a - b + c = a + c - b', where: numeralBefore},
        {stmt: 'a - b - c = a - c - b', where: numeralBefore},
        {descend: {
            schema: 'a + b',
            parts: {a: 'numRightMovers'}
          }
        },
        {descend: {
          schema: 'a - b',
          parts: {a: 'numRightMovers'}}
        }];
      var context = {factLists: {numRightMovers: numRightMovers}};
      return convert(step, path, function(expr) {
          var arrangeRhs = Toy.arrangeRhs;
          var eqn = rules.consider(step.get(path));
          var flat = arrangeRhs(eqn, context, 'numRightMovers');
          return flat;
        }).justify('arrangeSum', arguments, [step]);
    },
    inputs: {site: 1},
    toOffer: function(step, term) {
      return (term.matchSchema('a + b') || term.matchSchema('a - b'));
    },
    offerExample: true,
    form: '',
    menu: 'algebra: collect like terms in {term}',
    description: 'collect like terms in {site};; {in step siteStep}',
    labels: 'algebra'
  },

  /**
   * "Flattens" a term made up of "*", "/", and "neg".  Converts
   * uses of "neg" into multiplication by -1, then removes
   * parentheses, traversing uses of "*" and "/".  Simplfies
   * the resulting RHS.
   */
  flattenTerm: {
    data: {flatteners: [
        {stmt: 'a * (b * c) = a * b * c'},
        {stmt: 'a * (b / c) = a * b / c'},
        {stmt: 'a / (b * c) = a / b / c'},
        {stmt: 'a / (b / c) = a / b * c'},
        // TODO: Support the following style, like in walkPatterns,
        //   and convert uses of "descend" to it.
        // {match: 'a * b', a: 'flatteners'},
        {descend:
         {schema: 'a * b',
          parts: {a: 'flatteners', b: 'flatteners'}}},
        {descend:
         {schema: 'a / b',
          parts: {a: 'flatteners'}}}
    ], denegaters: [
        {stmt: 'neg a = -1 * a'},
        {descend:
         {schema: 'a * b',
          parts: {a: 'denegaters', b: 'denegaters'}}},
        {descend:
         {schema: 'a / b',
          parts: {a: 'denegaters', b: 'denegaters'}}}
    ]},
    action: function flattenTerm(step, path) {
      var context = {factLists:
                     {denegaters: this.data.denegaters,
                      flatteners: this.data.flatteners}};
      return convert(step, path, function(expr) {
          var arrangeRhs = Toy.arrangeRhs;
          var eqn = rules.consider(step.get(path));
          var noneg = arrangeRhs(eqn, context, 'denegaters');
          var flat = arrangeRhs(noneg, context, 'flatteners');
          return flat;
        }).justify('flattenTerm', arguments, [step]);
    },
    inputs: {site: 1},
    offerExample: true,
    form: '',
    menu: 'algebra: flatten {term}',
    description: 'flatten term {site};; {in step siteStep}',
    labels: 'algebra'
  },

  /**
   * Organize the factors in a term.  Processes multiplication,
   * division, negation, reciprocal, and does arithmetic.  Works by
   * applying flattenTerm, which also simplifies out negations, then
   * moves numeric terms all to the left, separates numerator terms
   * from denominator terms without disturbing ordering of numerals,
   * and finally does arithmetic on numeric products.
   *
   * Inline, for internal use.
   */
  arrangeRational: {
    data: function() {
      // TODO: For terms containing composite terms e.g. 2*(x + y),
      //   consider changing "isVariable" in these tests to
      //   just "not a numeral".
      var numeralAfterVar = '$.c.isNumeral() && $.b.isVariable()';
      // Moves numerals to the left.
      var numLeftMovers = [
        {stmt: 'a * b = b * a',
         where: '$.b.isNumeral() && $.a.isVariable()'},
        {stmt: 'a * b * c = a * c * b', where: numeralAfterVar},
        {stmt: 'a * b / c = a / c * b', where: numeralAfterVar},
        {stmt: 'a / b * c = a * c / b', where: numeralAfterVar},
        {stmt: 'a / b / c = a / c / b', where: numeralAfterVar},
        {descend: {
            schema: 'a * b',
            parts: {a: 'numLeftMovers'}
          }
        },
        {descend: {
          schema: 'a / b',
          parts: {a: 'numLeftMovers'}}
        }
      ];
      var numeralBeforeVar = '$.b.isNumeral() && $.c.isVariable()';
      // Moves numerals to the right.  Currently unused.
      var numRightMovers = [
        {stmt: 'a * b = b * a',
         where: '$.a.isNumeral() && $.b.isVariable()'},
        {stmt: 'a * b * c = a * c * b', where: numeralBeforeVar},
        {stmt: 'a * b / c = a / c * b', where: numeralBeforeVar},
        {stmt: 'a / b * c = a * c / b', where: numeralBeforeVar},
        {stmt: 'a / b / c = a / c / b', where: numeralBeforeVar},
        {descend: {
            schema: 'a * b',
            parts: {a: 'numRightMovers'}
          }
        },
        {descend: {
          schema: 'a / b',
          parts: {a: 'numRightMovers'}}
        }
      ];
      var numeralC = '$.c.isNumeral()';
      // Groups together terms that belong in the numerator by
      // moving multiplications to the left.
      // Assumes the term is already flattened.
      var numerators = [
        {stmt: 'a / b * c = a * c / b'},
        {descend:
         {schema: 'a * b',
          parts: {a: 'numerators'}}},
        {descend:
         {schema: 'a / b',
          parts: {a: 'numerators'}}}
      ];
      // Groups together terms that belong in the denominator, albeit
      // grouped to the right.  When done there is only one division.
      // Assumes the term is already flattened.
      var denominators = [
        {stmt: 'a / b / c = a / (b * c)'},
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
        // TODO: Perhaps neither tryArithmetic nor arithRight
        //   are needed here given that the site will be simplified
        //   in the end.
        // {apply: arithRight},
        // If there is a negated numeral in the denominator, moves
        // the negation into the numerator.
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
              {numLeftMovers: numLeftMovers,
               numRightMovers: numRightMovers,
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
    action: function arrangeRational(step, path, numsLeft) {
      var context = this.data.context;
      var arrangeRhs = Toy.arrangeRhs;
      var numMovers = numsLeft ? 'numLeftMovers' : 'numRightMovers';
      return convert(step, path, function(expr) {
          var infix = Toy.infixCall;
          var eqn = rules.consider(expr);
          var flat = rules.flattenTerm(eqn, '/main/right');
          // TODO: For large terms consider separating numerator
          //   and denominator first, then move numerals within each.
          var ordered = arrangeRhs(flat, context, numMovers);
          var numerated = arrangeRhs(ordered, context, 'numerators');
          var denominated = arrangeRhs(numerated, context, 'denominators');
          var arithmetized = arrangeRhs(denominated, context, 'arithmetizers');
          var div = arithmetized.getMain().matchSchema('l = a / b');
          var resulted;
          if (div) {
            // TODO: Debug this branch of the code, including the
            // recursive call.
            var b = div.b;
            var product = b.matchSchema('c * d');
            if (product && product.c.isNumeral() &&
                product.c.getNumValue() < 0) {
              var fact1 = rules.arithmetic('-1 / -1').andThen('eqnSwap');
              var quotient = rules.consider(infix(div.a, '/', div.b));
              resulted = (rules.rewrite(arithmetized, '/main/right', 'a = a * 1')
                          .rewrite('/main/right/right', fact1)
                          // CAUTION: recursive call.  There will be
                          // trouble if recursion reaches here.
                          // TODO: Decide at the start whether to multiply
                          //   by -1 / -1 and skip this whole condition.
                          .andThen('arrangeRational', path));
            } else {
              // Flatten the denominator.
              resulted = rules.flattenTerm(arithmetized, '/main/right/right');
            }
          } else {
            resulted = arithmetized;
          }
          // Perhaps this just applies 1 * x = x and -1 * x = neg x.
          return rules.simplifySite(resulted, '/main/right');
        });
    },
  },

  /**
   * Arrange a rational expression with numeric coefficents on the
   * left.  This is useful, but if there is a denominator or more than
   * two factors in the numerator, the result will need to be
   * converted to coefficient form.
   */
  arrangeRatio: {
    action: function arrangeRatio(step, path) {
      return (rules.arrangeRational(step, path, true)
              .justify('arrangeRatio', arguments, step));
    },
    inputs: {site: 1},
    offerExample: true,
    toOffer: 'return term.isReal()',
    form: '',
    menu: 'algebra: to standard ratio form',
    description: 'standard ratio form for term {site};; {in step siteStep}',
    labels: 'algebra'
  },

  /**
   * Arrange a rational expression into "coefficient" form, with a leading
   * numeric coefficient where possible.  This form is useful as preparation
   * for gathering like terms.
   *
   * TODO: Complete the implementation, or perhaps implement a rule
   *   that converts the "ratio" form above into coefficient form.
   *   A known problem with the code here is that numeric terms
   *   are not coalesced into a single factor.  Pull them all
   *   out of both numerator and denominator, then do arithmetic.
   *   
   */
  arrangeTerm: {
    action: function arrangeTerm(step, path) {
      var step1 = rules.arrangeRational(step, path, false);
      var step2 = rules.simplifySite(step1, path);
      // These facts cover the cases where there is a numeral
      // at the end of the numerator or denominator or both.
      var facts = [
          {stmt: 'a * b = b * a',
           where: '$.b.isNumeral()'},
          {stmt: 'a * b / (c * d) = b / d * (a / c)',
           where: '$.b.isNumeral() && $.d.isNumeral()'},
          {stmt: 'a * b / c = b * (a / c)',
           where: '$.b.isNumeral()'},
          {stmt: 'a / (b * c) = 1 / c * (a / b)',
           where: '$.c.isNumeral()'}
      ];
      return (Toy.applyFactsOnce(step2, path, facts)
              .justify('arrangeTerm', arguments, step));
    },
    inputs: {site: 1},
    offerExample: true,
    toOffer: 'return term.isReal()',
    form: '',
    menu: 'algebra: to standard form for term in sum',
    description: 'standard form for term {site};; {in step siteStep}',
    labels: 'algebra'
  },

  // Regrouping, but just for additions.
  // TODO: When there is a more suitable regrouping rule, remove this.
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
   * Removes parentheses from an add/sub/mul/div expression that
   * needs them to force association to the right.  Uses converses
   * of regroupingFacts.
   */
  ungroup: {
    toOffer: function(step, expr) {
      var path = step.prettyPathTo(expr).upTo('/right');
      if (!path) {
        return false;
      }
      var term = step.get(path);
      return !!Toy.findMatchingFact(ungroupingFacts, null, term);
    },
    action: function(step, path_arg) {
      var path = step.prettifyPath(path_arg).upTo('/right');
      return (Toy.applyFactsOnce(step, path, ungroupingFacts)
              .justify('ungroup', arguments, [step]));
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: ungroup {term}',
    description: 'ungroup',
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
    action: function(step, path, num) {
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
      var fact2 = rules.instVar(fact, Toy.numify(k2), 'c');
      return (step1.rewrite(path.concat('/right'), fact2)
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
   * Convert the target term from "coefficient" form to "fraction"
   * form.  The coefficient is the leftmost factor of the term, and if
   * it has a (numeric) denominator, this moves it to be the
   * denominator of the entire term.  If this rule fails for any
   * reason, it returns the given step unchanged.
   */
  asFraction: {
    toOffer: function(step, target) {
      var path = step.pathTo(target);
      return this(step, path) !== step;
    },
    action: function(step, path) {
      var infix = Toy.infixCall;
      var target = step.get(path);
      var coefficient = target;
      // Get the "coefficient" part (leftmost call to "*").
      while (coefficient.isCall2('*') && coefficient.getLeft().isCall2()) {
        coefficient = coefficient.getLeft();
      }
      if (coefficient.isCall2('/') && coefficient.getRight().isNumeral()) {
        var divisor = coefficient.getRight();
        var step1 = rules.eqSelf(target);
        var step2 = (rules.multiplyBoth(step1, '', divisor)
                     .andThen('arrangeTerm', '/main/right')
                     .andThen('divideBoth', '/main', divisor)
                     .rewrite('/main/left', 'a * b / c = a * (b / c)')
                     .andThen('simplifySite', '/main/left/right')
                     .andThen('simplifySite', '/main/left'));
        return (rules.rplace(step2, step, path)
                .justify('asFraction', arguments, [step]));
      } else {
        return step;
      }
    },
    inputs: {site: 1},
    form: '',
    menu: 'to fraction form',
    description: 'convert to fraction form',
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

  // TODO: Many of these carry unnecessary conditions that their
  // arguments are real numbers, which propagate to unnecessary
  // nonzero conditions of many facts about division and reciprocal.
  // Lift the unnecessary conditions all around.

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

  // A real number exists.  Equivalently exists {x. R x}.
  'exists R': {
    proof: function() {
      return (rules.fact('p x => exists p')
              // This line helps simplifyStep to simplify the
              // assumptions and also helps the display to show
              // the user what is going on.
              .andThen('asImplication')
              .andThen('instMultiVars', {x: '0', 'p': 'R'})
              .andThen('simplifyStep'));
    }
  },
  
  '@R a => a != none': {
    proof: function() {
      var asm = rules.assume('a = none');
      return (rules.fact('not (R none)')
              .rplace('/arg/arg', rules.eqnSwap(asm))
              // Just to make the display clearer:
              .andThen('asImplication')
              .andThen('rewriteOnly', '', 'a => not b == b => not a')
              .andThen('simplifySite', '/right'));
    }
  },

  '@neg x = -1 * x': {
    proof: function() {
      return (rules.consider('neg x')
              .andThen('useDefinition', '/right')
              .andThen('apply', '/right'));
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
      return rules.rewriteOnly(conj, '/main', '(p => q) & (q => p) == (p == q)');
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
      return rules.rewriteOnly(conj, '/main', '(p => q) & (q => p) == (p == q)');
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
      var result = rules.rewriteOnly(conj, '/main', taut);
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
      return rules.rewriteOnly(conj, '/main', '(p => q) & (q => p) == (p == q)');
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
    },
    simplifier: true
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

  // Negation with multiplication

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
  'a / -1 = -1 * a': {
    proof: function() {
      var fact = rules.axiomArithmetic('1 / -1');
      return (rules.consider('a / -1')
              .rewrite('/main/right/left', 'a = a * 1')
              .rewrite('/main/right', 'a * b / c = a * (b / c)')
              .rewrite('/main/right/right', fact)
              .rewrite('/main/right', 'a * b = b * a'));
    }
  },
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
  },

  'a + b - b = a': {
    proof: function() {
      return (rules.fact('a + b - c = a + (b - c)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyStep'));
    },
    simplifier: true
  },

  'a - b + b = a': {
    proof: function() {
      return (rules.fact('a - b + c = a - (b - c)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyStep'));
    },
    simplifier: true
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
      var step3 = (rules.rRight(step1, step2, '/left')
                   .rewrite('/main', 'a * b != 0 == a != 0 & b != 0'));
      var step4 = rules.tautology('a => (b & c) => (a => c)');
      var step5 = rules.forwardChain(step3, step4);
      return step5;
    }
  },
  'a / b = a * recip b': {
    // TODO: Prove me!
  },
  'a != 0 => recip a = 1 / a': {
    proof: function() {
      return rules.consider('recip s')
      .rewrite('/main/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * recip b = a / b');
    }
  },
  'a != 0 => recip (recip a) = a': {
    simplifier: true,
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
  'b != 0 => a / b * b  = a': {
    proof: function() {
      return (rules.fact('a / b * c = a * (c / b)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyStep'));
    },
    simplifier: true
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
  'b != 0 & c != 0 => a / b / c = a / c / b': {
    proof: function() {
      var arrange = Toy.applyFactsWithinRhs;
      var step1 = arrange(rules.consider('a / b / c'),
                          ['a / b = a * recip b']);
      var step2 = rules.rewrite(step1, '/main/right',
                                'a * b * c = a * c * b');
      var step3 = arrange(step2, ['a * recip b = a / b']);
      return step3;
    }
  },
  'b != 0 & c != 0 => a / (b / c) = a / b * c': {
    proof: function() {
      var arrange = Toy.applyFactsWithinRhs;
      var step1 = arrange(rules.consider('a / (b / c)'),
                          ['a / b = a * recip b',
                           'recip (a * b) = recip a * recip b',
                           'recip (recip a) = a']);
      var result = arrange(step1,
                           ['a * (b * c) = a * b * c',
                            'a * recip b = a / b']);
      return result;
    }
  },
  'a != 0 & b != 0 => a / (a * b) = 1 / b': {
    proof: function() {
      return (rules.fact('a / (b * c) = a / b / c')
              .andThen('instVar', 'a', 'b')
              .andThen('simplifyStep'));
    },
    simplifier: true
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
  'b != 0 => a * b / b = a': {
    proof: function() {
      return (rules.fact('a * b / c = a * (b / c)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyStep'));
    },
    simplifier: true
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
  // Used in arrangeTerm.
  'c != 0 & d != 0 => (a * b) / (c * d) = (b / d) * (a / c)': {
    proof: function() {
      return (rules.consider('a * b / (c * d)')
              .andThen('flattenTerm', '/main/right')
              .rewrite('/main/right/left', 'a * b / c = a / c * b')
              .rewrite('/main/right', 'a * b / c = a * (b / c)')
              .rewrite('/main/right', 'a * b = b * a'));
    }
  },
  // Used in arrangeTerm.
  'c != 0 => a * b / c = b * (a / c)': {
    proof: function() {
      return (rules.consider('a * b / c')
              .rewrite('/main/right/left', 'a * b = b * a')
              .rewrite('/main/right', 'a * b / c = a * (b / c)'));
    }
  },
  // Used in arrangeTerm.
  'a / (b * c) = 1 / c * (a / b)': {
    proof: function() {
      return (rules.consider('a / (b * c)')
              .rewrite('/main/right/left', 'a = a * 1')
              .rewrite('/main/right', 'a * b / (c * d) = (b / d) * (a / c)'));
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

// Internal to arithRight.
var _arithInfo = [{schema: 'a + b + c = a + (b + c)'},
                  {schema: 'a + b - c = a + (b - c)'},
                  {schema: 'a - b + c = a - (b - c)'},
                  {schema: 'a - b - c = a - (b + c)'},
                  {schema: 'a * b * c = a * (b * c)'},
                  {schema: 'a * b / c = a * (b / c)',
                   nz: {c: true}},
                  {schema: 'a / b * c = a / (b / c)',
                   nz: {b: true, c: true}},
                  {schema: 'a / b / c = a / (b * c)',
                   nz: {b: true, c: true}},
                  ];

// Internal to arithRight.
var _arithOps = {'+': true, '-': true, '*': true, '/': true};

/**
 * If the given term has the form [a op1 b op2 c] where op1 and op2
 * are among the basic four math operations, and an associative law
 * can be applied, followed by an arithmetic simplification on b and c
 * (with their new operator), then this does so, and returns an
 * equation with LHS matching the term and RHS in reduced form.
 */
function arithRight(term, cxt) {
  // TODO: When all of these facts are proved to be unconditionally
  //   true, remove "nz" conditions that cause the side condition to
  //   be added when the fact is used.  When arithmetic includes the
  //   null element, remove all "nz" conditions.
  if (term.isCall2() && term.getLeft().isCall2()) {
    var op1 = term.getLeft().getBinOp().name;
    var op2 = term.getBinOp().name;
    if (((op1 === '+' || op1 === '-') &&
         (op2 === '+' || op2 === '-')) ||
        ((op1 === '*' || op1 === '/') &&
         (op2 === '*' || op2 === '/'))) {
      var info = _arithInfo;
      for (var i = 0; i < info.length; i++) {
        var item = info[i];
        var map = term.matchSchema(Toy.parse(item.schema).getLeft());
        if (map) {
          var nz = item.nz;
          var bValue = map.b.isNumeral() && map.b.getNumValue();
          var cValue = map.c.isNumeral() && map.c.getNumValue();
          if (bValue === 0 && nz.b ||
              cValue === 0 && nz.c) {
            continue;
          }
          var step1 = rules.consider(term);
          var step2 = rules.rewrite(step1, '/right', item.schema);
          var eqn = Toy.tryArithmetic(step2.get('/main/right/right'));
          if (eqn) {
            var step3 = rules.replace(step2, '/main/right/right', eqn);
            return step3;
          }
        }
      }
    }
  }
}

/**
 * Simplification facts for algebra, used in _simplifyMath1
 * and related places.  During initialization all facts
 * flagged as simplifier: true are added to this list.
 *
 * TODO: Consider whether x - 7 is simpler than x + -7.
 */
var basicSimpFacts = [
                      'T & a == a',
                      'a & T == a',
                      'x = x == T',
                      'T => a == a',
                      'not (a = b) == a != b',
                      {stmt: 'a + neg b = a - b',
                       // This condition makes extra-sure there will be
                       // no circularity during simplification.
                       // Negation of a numeral will be simplified by
                       // other rules.
                       where: '!$.b.isNumeral()'},
                      {stmt: 'a - b = a + neg b',
                       // This one is an exception to the general rule
                       // that simplifiers make the expression tree
                       // smaller; but arithmetic will follow this, and
                       // with high priority.
                       where: '$.b.isNumeral() && $.b.getNumValue() < 0'},
                      {apply: function(term, cxt) {
                          return (isArithmetic(term) &&
                                  rules.axiomArithmetic(term));
                        }
                      },
                      {apply: arithRight}
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

    Toy.eachFact(function(info) {
        if (info.simplifier) {
          basicSimpFacts.push(info.synopsis);
        }
      });

    // For testing (computed value).
    Toy._ungroupingFacts = ungroupingFacts;
});

})();
