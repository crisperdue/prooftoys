// Copyright 2011, 2012, 2013, 2014, 2015 Crispin Perdue.
// All rights reserved.

// Set all of this up immediately upon load, but avoiding changes
// to the global environment (except through the "Toy" namespace).
(function() {

//// THEOREMS AND RULES

var rules = Toy.rules;
var ruleData = Toy.ruleData;

var assert = Toy.assertTrue;
var check = Toy.check;
var memo = Toy.memo;

//  Make some useful names available here.
var assertEqn = Toy.assertEqn;
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
 * Given an equational step with a single term on each side, puts each
 * in standard form, then does general simplification throughout
 * the step.  For use after mul/div both sides of an equation.
 */
function simplifyRegroupedMuls(eqn) {
  var right = rules.arrangeTerm(eqn, '/main/right');
  var left = rules.arrangeTerm(right, '/main/left');
  return rules.simplifyStep(left);
}


/**
 * Given an equational step, tries regrouping and simplifying the
 * regrouped site, on both sides.  Keeps the result if the
 * simplification succeeds.  Returns the result of applying
 * basic simplifications to the whole step at the end.  For use
 * after add/subtract both sides of an equation.
 */
function simplifyRegroupedAdds(eqn) {
  var applyFactsOnce = Toy.applyFactsOnce;
  // Simplify the right side by regrouping and simplifying the result.
  var right = eqn;
  var right1 = applyFactsOnce(eqn, '/main/right', regroupingFacts);
  if (right1 !== eqn) {
    right = rules.simplifySite(right1, '/main/right/right');
    if (right == right1) {
      // Don't bother regrouping if the result cannot be simplified.
      right = eqn;
    }
  }
  // Simplify the left side by regrouping and simplifying the result.
  var left = right;
  var left1 = applyFactsOnce(right, '/main/left', regroupingFacts);
  if (left1 !== right) {
    left = rules.simplifySite(left1, '/main/left/right');
    if (left == left1) {
      // Don't bother regrouping if the result cannot be simplified.
      left = right;
    }
  }
  return rules.simplifyStep(left);
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
    action: function() {
      return (rules.assert('R x & R y => x + y = y + x')
              .apply('asHypotheses').justify('axiomCommutativePlus'));
    },
    inputs: {},
    form: '',
    tooltip: 'commutativity of addition',
    description: 'commutativity of addition'
  },

  axiomAssociativePlus: {
    action: function() {
        return (rules.assert('R x & R y & R z => x + (y + z) = (x + y) + z')
                .apply('asHypotheses').justify('axiomAssociativePlus'));
    },
    inputs: {},
    form: '',
    tooltip: 'associativity of addition',
    description: 'associativity of addition'
  },

  axiomCommutativeTimes: {
    action: function() {
        return (rules.assert('R x & R y => x * y = y * x')
                .apply('asHypotheses').justify('axiomCommutativeTimes'));
      },
    inputs: {},
    form: '',
    tooltip: 'commutativity of multiplication',
    description: 'commutativity'
  },

  axiomAssociativeTimes: {
    action: function() {
          return (rules.assert('R x & R y & R z => x * (y * z) = (x * y) * z')
                  .apply('asHypotheses').justify('axiomAssociativeTimes'));
      },
    inputs: {},
    form: '',
    tooltip: 'associativity of multiplication',
    description: 'associativity of multiplication'
  },

  axiomDistributivity: {
    action: function() {
        return (rules.assert('R x & R y & R z => x * (y + z) = x * y + x * z')
                .apply('asHypotheses').justify('axiomDistributivity'));
      },
    inputs: {},
    form: '',
    tooltip: 'distributive law',
    description: 'distributive law'
  },

  axiomPlusZero: {
    action: function() {
        return (rules.assert('R x => x + 0 = x')
                .apply('asHypotheses').justify('axiomPlusZero'));
      },
    inputs: {},
    form: '',
    tooltip: 'x + 0 = x',
    description: 'additive identity'
  },

  axiomTimesOne: {
    action: function() {
        return (rules.assert('R x => x * 1 = x')
                .apply('asHypotheses').justify('axiomTimesOne'));
      },
    inputs: {},
    form: '',
    tooltip: 'x * 1 = x',
    description: 'multiplicative identity'
  },

  axiomTimesZero: {
    action: function() {
        return (rules.assert('R x => x * 0 = 0')
                .apply('asHypotheses').justify('axiomTimesZero'));
      },
    inputs: {},
    form: '',
    tooltip: 'x * 0 = 0',
    description: 'multiplication by 0'
  },

  axiomNeg: {
    action: function() {
        return rules.assert('neg x = -1 * x').justify('axiomNeg');
      },
    inputs: {},
    form: '',
    tooltip: 'neg x = -1 * x',
    description: 'definition of negation'
  },

  axiomReciprocal: {
    action: function() {
        return (rules.assert('R x & x != 0 => x * recip x = 1')
                .apply('asHypotheses').justify('axiomReciprocal'));
      },
    inputs: {},
    form: '',
    tooltip: 'x * recip x = 1 if x is not 0',
    description: 'recip is inverse to multiplication'
  },

  // TODO: Prove this as a theorem.
  axiomReciprocal2: {
    action: function() {
      return rules.assert('R (recip x) & recip x != 0 == R x & x != 0')
        .justify('axiomReciprocal2');
    },
    inputs: {},
    form: '',
    tooltip: 'nonzero reciprocals',
    description: 'reciprocals are nonzero'
  },

  // This implies that 0 ** 0 = 1.  It is also legitimate to define
  // that 0 ** 0 is undefined.
  // TODO: Eventually prove these laws of powers as theorems.
  axiomPower0: {
    action: function() {
        return (rules.assert('R x => x ** 0 = 1')
                .apply('asHypotheses').justify('axiomPower0'));
      },
    inputs: {},
    form: '',
    tooltip: 'real number to the zeroth power',
    description: 'real number to the zeroth power is 1'
  },

  // TODO: Eventually prove these laws of powers as theorems.
  axiomNextPower: {
    action: function() {
      return rules.assert('x ** (y + 1) = (x ** y) * x')
        .justify('axiomNextPower');
    },
    inputs: {},
    form: '',
    tooltip: 'real number to the next power',
    description: 'real number to the next power'
  },

  // TODO: Prove this as a consequnce of completeness.
  factNonzeroProduct: {
      proof: function() {
        return (rules.assert('R x & R y => (x * y != 0) = (x != 0 & y != 0)')
                .apply('asHypotheses'));
      }
  },

  // Type-related axioms

  // This axiom applies to all normal objects, not just reals.
  axiomRealNotNull: {
    proof: function() {
      return rules.assert('not (R none)');
    }
  },

  // Note: not structured as a rewrite rule.
  axiomPlusType: {
    action: function() {
      return rules.assert('R x & R y == R (x + y)')
        .justify('axiomPlusType');
    },
    inputs: {},
    form: '',
    menu: 'axiom ' + Toy.mathMarkup('R (x + y)'),
    tooltip: 'sum of real numbers is real',
    description: 'sum of real numbers is real'
  },

  // Note: not structured as a rewrite rule.
  axiomTimesType: {
    action: function() {
      return rules.assert('R x & R y == R (x * y)')
	.justify('axiomTimesType');
    },
    inputs: {},
    form: '',
    menu: 'axiom ' + Toy.mathMarkup('R (x*y)'),
    tooltip: 'product of real numbers is real',
    description: 'product of real numbers is real'
  },

  axiomNegType: {
    action: function() {
      return rules.assert('R x == R (neg x)')
	.justify('axiomNegType');
    },
    inputs: {},
    form: '',
    menu: 'axiom ' + Toy.mathMarkup('R (-x)'),
    tooltip: 'negation of real number is real',
    description: 'negation of real number is real'
  },

  // TODO: Replace me.
  axiomReciprocalType: {
    action: function() {
      return rules.assert('R x & x != 0 == R (recip x)')
	.justify('axiomReciprocalType');
    },
    inputs: {},
    menu: 'axiom ' + Toy.mathMarkup('x != 0 == R (recip x)'),
    form: '',
    tooltip: 'reciprocal of nonzero real number is real',
    description: 'reciprocal of real number'
  },

  // Evaluates arithmetic expressions with operators:
  // +, -, *, /, neg, =, !=, >, >=, <, <=, and the type operator "R".
  // Checks that inputs are all numeric and that the result can be
  // guaranteed to be an exact integer.
  //
  // Result is always an equation (or biconditional) with the given
  // term as the LHS.  Throws an error if it cannot obey these
  // specifications.
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
          var value = Toy.checkRange(value);
          var rhs = Toy.constify(value.toFixed(0));
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
          var rhs = Toy.constify(value.toFixed(0));
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
    proof: function() {
      var step1 = rules.axiomPlusType();
      var step2 = rules.instVar(step1, Toy.parse('neg y'), 'y');
      var step3 = rules.axiomNegType();
      var step4 = rules.instVar(step3, 'y', 'x');
      var step5 = rules.rRight(step4, step2, '/left/right');
      var step6 = rules.eqSelf(Toy.parse('x - y'));
      var step7 = rules.apply(step6, '/left');
      return rules.replace(step7, step5, '/main/right/arg');
    },
    form: '',
    menu: 'theorem R (x - y)',
    tooltip: 'difference of real numbers is real',
    description: 'difference of real numbers is real',
    labels: 'uncommon'
  },

  divisionType: {
    proof: function() {
      var step1 = rules.axiomTimesType();
      var step2 = rules.instVar(step1, Toy.parse('recip y'), 'y');
      var step3 = rules.axiomReciprocalType();
      var step4 = rules.instVar(step3, 'y', 'x');
      var step5 = rules.rRight(step4, step2, '/left/right');
      var step6 = rules.eqSelf(Toy.parse('x / y'));
      var step7 = rules.apply(step6, '/left');
      var step8 = rules.replace(step7, step5, '/main/right/arg')
      // TODO: Normalize the assumptions automatically, not by hand.
      return rules.rewrite(step8, '/left',
                           rules.tautology('a & (b & c) == c & a & b'));
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
  },

  // Managing numeric type hypotheses

  // Given a step that is a conditional, proves a version with the
  // assumptions simplified.  Reduces assumptions about "R" type of
  // expressions with arithmetic operators to assumptions about "R"
  // type of variables; removes assumptions that specific numerals are
  // real or nonzero; simplifies assumptions about products being
  // nonzero into assertions that both operands are real; removes
  // duplicate terms and occurrences of T.
  simplifyAssumptions: {
    action: function(step) {
      if (!step.isCall2('=>')) {
        // Shortcut inline return.
        return step;
      }
      // From a conditional a => b, prove a => (b == T).
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
      var adder = proveIsT(rules.axiomPlusType());
      var multiplier = proveIsT(rules.axiomTimesType());
      var subtracter = proveIsT(rules.subtractionType());
      var divider = proveIsT(rules.divisionType());
      var negger = memo(function() {
          return rules.axiomNegType().apply('eqnSwap');
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
        if (!stepArg.isCall2('=>')) {
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
          var expr = step.get(path);
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
    tooltip: 'simplify assumptions in a step',
    menu: 'simplify assumptions',
    labels: 'uncommon'
  },

  // TODO: Thes "both" ops are less general than the related facts
  //   such as 'a = b => a * c = b * c'.  Consider using those here.
  addToBoth: {
    action: function(eqn, term_arg) {
      return (rules.applyToBothWith(eqn, '+', term_arg)
              .justify('addToBoth', arguments, [eqn]));
    },
    inputs: {equation: 1, term: 2},
    autoSimplify: simplifyRegroupedAdds,
    form: ('Add <input name=term> to both sides of ' +
           'step <input name=equation>'),
    menu: 'algebra: add to both sides',
    tooltip: ('add to both sides'),
    description: 'add {term};; {in step equation}',
    labels: 'algebra'
  },

  subtractFromBoth: {
    action: function(eqn, term_arg) {
      return (rules.applyToBothWith(eqn, '-', term_arg)
              .justify('subtractFromBoth', arguments, [eqn]));
    },
    inputs: {equation: 1, term: 2},
    autoSimplify: simplifyRegroupedAdds,
    form: ('Subtract <input name=term> from both sides of ' +
           'step <input name=equation>'),
    menu: 'algebra: subtract from both sides',
    tooltip: ('subtract from both sides'),
    description: 'subtract {term};; {in step equation}',
    labels: 'algebra'
  },

  multiplyBoth: {
    action: function(eqn, term_arg) {
      return (rules.applyToBothWith(eqn, '*', term_arg)
              .justify('multiplyBoth', arguments, [eqn]));
    },
    inputs: {equation: 1, term: 2},
    autoSimplify: simplifyRegroupedMuls,
    form: ('Multiply both sides of step <input name=equation>' +
           ' by <input name=term>'),
    menu: 'algebra: multiply both sides',
    tooltip: ('multiply both sides'),
    description: 'multiply by {term};; {in step equation}',
    labels: 'algebra'
  },

  divideBoth: {
    action: function(eqn, term_arg) {
      return (rules.applyToBothWith(eqn, '/', term_arg)
              .justify('divideBoth', arguments, [eqn]));
    },
    inputs: {equation: 1, term: 2},
    autoSimplify: simplifyRegroupedMuls,
    form: ('Divide both sides of step <input name=equation>' +
           ' by <input name=term>'),
    menu: 'algebra: divide both sides',
    tooltip: ('divide both sides'),
    description: 'divide by {term};; {in step equation}',
    labels: 'algebra'
  },

  addThisToBoth: {
    action: function(step, path) {
      var term = step.get(path);
      return (rules.addToBoth(step, term)
              .justify('addThisToBoth', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: simplifyRegroupedAdds,
    toOffer: 'return term.isReal();',
    form: '',
    menu: 'algebra: add {term} to both sides',
    description: 'add {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  subtractThisFromBoth: {
    action: function(step, path) {
      var term = step.get(path);
      return (rules.subtractFromBoth(step, term)
              .justify('subtractThisFromBoth', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: simplifyRegroupedAdds,
    toOffer: 'return term.isReal();',
    form: '',
    menu: 'algebra: subtract {term} from both sides',
    description: 'subtract {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  multiplyBothByThis: {
    action: function(step, path) {
      var term = step.get(path);
      return (rules.multiplyBoth(step, term)
              .justify('multiplyBothByThis', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: simplifyRegroupedMuls,
    toOffer: 'return term.isReal();',
    form: '',
    menu: 'algebra: multiply both sides by {term}',
    description: 'multiply by {site};; {in step siteStep}',
    labels: 'algebra'
  },    

  divideBothByThis: {
    action: function(step, path) {
      var term = step.get(path);
      return (rules.divideBoth(step, term)
              .justify('divideBothByThis', arguments, [step]));
    },
    inputs: {site: 1},
    autoSimplify: simplifyRegroupedMuls,
    toOffer: 'return term.isReal();',
    form: '',
    menu: 'algebra: divide both sides by {term}',
    description: 'divide by {site};; {in step siteStep}',
    labels: 'algebra'
  },

  addEquationToThis: {
    action: function(eqn1, eqn2) {
      var lhs = eqn2.getMain().getLeft();
      var step1 = rules.addToBoth(eqn1, lhs);
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
      var step1 = rules.subtractFromBoth(eqn1, lhs);
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
  },

  // Looks up the statement string, proving it if needed. Returns that
  // result, justified as a "fact".  This is the way to refer to a
  // fact in a proof, displaying it on its own proof line.
  // Currently inline if it is a no-op.
  // Also proves statements of tautologies and simple arithmetic facts.
  // Removes any " = T" from boolean-valued arithmetic facts.
  // Programmatic usage supports theorems by name, but not the UI.
  fact: {
    action: function(statement) {
      if (Toy.isProved(statement)) {
        // It is an already proved statement.
        return statement;
      }
      // Try named theorems (not available from the UI).
      var result = Toy.getTheorem(statement);
      if (result) {
        return result;
      }
      // Try ordinary proved facts.
      if (Toy.isRecordedFact(statement)) {
        return Toy.getResult(statement).justify('fact', arguments);
      }
      // Next try arithmetic facts.
      var stmt = Toy.getStatement(statement);
      if (stmt.isEquation()) {
        var result = tryArithmetic(stmt.eqnLeft());
        if (result && result.alphaMatch(stmt)) {
          return result;
        }
      } else {
        // Relational operators can go here.
        var result = tryArithmetic(stmt);
        // x = T is the expected result.
        if (result && result.matchSchema('x = T')) {
          return rules.rewriteWithFact(result, '', '(x = T) = x');
        }
      }
      // Try tautologies.
      try {
        // Inline for tautologies.
        return rules.tautology(statement);
      } catch(err) {}
      throw new Error('No such fact: ' + statement);
    },
    inputs: {bool: 1},
    form: ('Look up fact <input name=bool size=40>'),
    menu: 'look up a fact',
    tooltip: (''),
    description: 'fact',
    labels: 'basic'
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
    menu: 'match with an equation LHS',
    description: 'rewrite {site};; {in step siteStep} {using step equation}',
    labels: 'basic'
  },

  // Repeatedly applies simplifyMath1 to do trivial simplifications.
  // If the visible part of the step is an equation, simplify each
  // side, otherwise the entire expression.
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
      var eqn1 = rules.consider(step.get(path));
      var ref = refStep.get(path);
      var abort = false;
      var simpler = Toy.whileSimpler(eqn1, function(eqn) {
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
        : (rules.replace(simpler, step, path)
           .justify('autoSimplifySite', arguments, [step]));
    },
    inputs: {site: 1, step: 3},
    form: 'Simplify w.r.t. step <input name=step>',
    menu: 'algebra: auto-simplify {term}',
    description: 'auto-simplify {site};; {in step siteStep}',
    labels: 'uncommon'
  },

  // Performs math-oriented simplification throughout the part of the
  // given step at the given path.  Works repeatedly until no more
  // simplifications are found.
  simplifySite: {
    action: function(step, path) {
      var result = rules._simplifySite(step, path);
      return result.justify('simplifySite', arguments, [step]);
    },
    inputs: {site: 1},
    form: '',
    menu: 'algebra: simplify {term}',
    description: 'simplify {site};; {in step siteStep}',
    labels: 'algebra'
  },
    
  // Inline version of simplifySite.
  _simplifySite: {
    action: function(step, path) {
      var _path = Toy.path;
      var eqn = rules.consider(step.get(path));
      var simpler = Toy.whileSimpler(eqn, function(eqn) {
          return rules._simplifyMath1(eqn, _path('/main/right', eqn));
        });
      return rules.replace(simpler, step, path);
    }
  },

  // Simplifies the part of the given step at _path using the axiom of
  // arithmetic and selected simplifying facts in basicSimpFacts.
  // Returns its result inline, just the input step if there is
  // nothing to do.
  //
  // From the UI use a rule that calls this one.
  _simplifyMath1: {
    action: function(step, _path) {
      var info = Toy.findMatchingCall(step.get(_path), basicSimpFacts);
      return (info
              ? rules.rewriteWithFact(step,
                                      _path.concat(info.path),
                                      info.stmt)
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
      while (info = Toy.findMatchingCall(simpler.get(path1), schemas)) {
        simpler = rules.arithmetic(simpler, path1.concat(info.path));
      }
      return simpler.justify('simplifyNegations', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Simplify negations in <input name=step>'),
    menu: 'algebra: simplify negations',
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
  },

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
        // TODO: Restore this line when the fact is available.
        // {stmt: 'neg (a / b) = neg a / b'},
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
      var context = ruleData.arrangeTerm.context;
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
    form: '',
    menu: 'algebra: get standard form of {term}',
    description: 'standard form of {site};; {in step siteStep}',
    labels: 'algebra'
  },

  regroupAdditions: {
    action: function(step) {
      function applyTo(eqn, facts) {
        return applyFactsWithinRhs(eqn, {facts: facts,
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
      .apply('regroupAdditions')
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
      var data = ruleData.moveTermRight;
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
      var data = ruleData.moveTermRight;
      var factsB = data.factsB;
      var factsA = data.factsA;
      function tryFact(name, fact_arg) {
        var schema = Toy.getResult(fact_arg).getMain().getLeft();
        var info = step.matchSchemaPart(path_arg, schema, name);
        if (info) {
          return rules.rewriteWithFact(step, info.path, fact_arg);
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
          return rules.rewriteWithFact(step, info.path, fact_arg);
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
    menu: 'simplify {term}'
  },

};  // End of numbersInfo.

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
    noSwap: true
  },
  'a * b = b * a': {
    proof: function() {
      return rules.axiomCommutativeTimes();
    },
    noSwap: true
  },
  'a + (b + c) = a + b + c': {
    proof: function() {
      return rules.axiomAssociativePlus();
    }
  },
  'a * (b * c) = a * b * c': {
    proof: function() {
      return rules.axiomAssociativeTimes();
    }
  },
  'a + 0 = a': {
    proof: function() {
      return rules.axiomPlusZero();
    }
  },
  'a * 1 = a': {
    proof: function() {
      return rules.axiomTimesOne();
    }
  },
  'a * 0 = 0': {
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
              .replace('/arg/arg', asm)
              .apply('asImplication')
              .apply('forwardChain', 'a => not b == b => not a')
              .apply('simplifySite', '/right'));
    }
  },

  'a + neg a = 0': {
    proof: function() {
      return rules.eqSelf('a + neg a')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c')
      .apply('arithmetic', '/main/right/left')
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
    noSwap: true
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
    }
  },
  '(a + b) * c = a * c + b * c': {
    proof: function() {
      var step = rules.consider('(a + b) * c')
      .rewrite('/main/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right/left', 'a * b = b * a');
      return step;
    }
  },
  'a * b + b = (a + 1) * b': {
    proof: function() {
      var step = rules.consider('a * b + b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    }
  },
  'b + a * b = (1 + a) * b': {
    proof: function() {
      var step = rules.consider('b + a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    }
  },
  'a + a = 2 * a': {
    proof: function() {
      return rules.consider('a + a')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * b + b = (a + 1) * b')
      .apply('arithmetic', '/main/right/left');
    }
  },

  // Distributivity with subtraction

  'a * (b - c) = a * b - a * c': {
    proof: function() {
      return rules.consider('a * (b - c)')
      .rewrite('/main/right/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * neg b = neg (a * b)')
      .rewrite('/main/right', 'a + neg b = a - b');
    }
  },
  '(a - b) * c = a * c - b * c': {
    proof: function() {
      var step = rules.consider('(a - b) * c')
      .rewrite('/main/right', 'a * b = b * a')
      .rewrite('/main/right', 'a * (b - c) = a * b - a * c')
      .rewrite('/main/right/right', 'a * b = b * a')
      .rewrite('/main/right/left', 'a * b = b * a');
      return step;
    }
  },
  'a * b - b = (a - 1) * b': {
    proof: function() {
      return rules.consider('a * b - b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    }
  },
  'b - a * b = (1 - a) * b': {
    proof: function() {
      return rules.consider('b - a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    }
  }
};

// Private to isDistribFact.  A mapping from statement key to value
// that is truthy iff the statement is in distribFacts.
var _distribFactsTable =
    (function() {
      var table = {};
      for (var key in distribFacts) {
        table[Toy.getStatementKey(key)] = true;
      }
      return table;
    })();

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
     var step3 = rules.rewriteWithFact(step2, '/main/right',
     'a + b = b + a');
     return step3;
     }
   },
  */
  '0 + a = a': {
    proof: function() {
      var step1 = rules.axiomPlusZero();
      var step2 = rules.rewriteWithFact(step1, '/main/left',
                                        'a + b = b + a');
      return step2;
    }
  },
  'a - 0 = a': {
    proof: function() {
      var step1 = (rules.consider('a - 0')
                   .apply('apply', '/main/right')
                   .apply('arithmetic', '/main/right/right')
                   .rewrite('/main/right', 'a + 0 = a'));
      return step1;
    }
  },
  '0 - a = neg a': {
    proof: function() {
      var step1 = (rules.consider('0 - a')
                   .apply('apply', '/main/right')
                   .rewrite('/main/right', '0 + a = a'));
      return step1;
    }
  },
  // Times one
  'a = 1 * a': {
    proof: function() {
      var step1 = rules.axiomTimesOne();
      var step2 = rules.eqnSwap(step1);
      var step3 = rules.rewriteWithFact(step2, '/main/right',
                                        'a * b = b * a');
      return step3;
    }
  },

  // Zero times
  '0 * a = 0': {
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
                     .apply('addToBoth', 'c')
                     .apply('asImplication'));
      var back = (rules.assume('a + c = b + c')
                  .apply('subtractFromBoth', 'c')
                  .apply('groupToRight', '/main/left/left/right')
                  .apply('simplifySite', '/main/left')
                  .apply('groupToRight', '/main/right/left/right')
                  .apply('simplifySite', '/main/right')
                  .apply('extractHyp', 'a + c = b + c'))
      var conj = rules.makeConjunction(forward, back);
      return rules.forwardChain(conj, '(p => q) & (q => p) == (p == q)');
    }
  },

  'a = b == a - c = b - c': {
    proof: function() {
      var forward = (rules.assume('a = b')
                     .apply('subtractFromBoth', 'c')
                     .apply('asImplication'));
      var back = (rules.assume('a - c = b - c')
                  .apply('addToBoth', 'c')
                  .apply('groupToRight', '/main/left/left/right')
                  .apply('simplifySite', '/main/left')
                  .apply('groupToRight', '/main/right/left/right')
                  .apply('simplifySite', '/main/right')
                  .apply('extractHyp', 'a - c = b - c'))
      var conj = rules.makeConjunction(forward, back);
      return rules.forwardChain(conj, '(p => q) & (q => p) == (p == q)');
    }
  },

  // This is primarily a lemma for the following one.
  'c != 0 => (a * c = b * c => a = b)': {
    // TODO: Figure out why the user must enter the c != 0 part
    //   when working interactively.
    proof: function() {
      var rewrite = rules.rewriteWithFact;
      var s1 = rules.assume('a * c = b * c');
      var s2 = rules.divideBoth(s1, 'c');
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
                     .apply('multiplyBoth', 'c')
                     .apply('asImplication'));
      var back = rules.fact('c != 0 => (a * c = b * c => a = b)');
      var conj = rules.makeConjunction(forward, back);
      var taut = rules.tautology('(a => b) & (b => a) == (a == b)');
      var result = rules.forwardChain(conj, taut);
      return result;
    }
  },

  // This is primarily a lemma for the following one.
  'c != 0 => (a / c = b / c => a = b)': {
    // TODO: Figure out why the user must enter the c != 0 part
    //   when working interactively.
    proof: function() {
      var regroup = rules.fact('a / b * c = a * (c / b)');
      var cancel = rules.fact('a != 0 => a / a = 1');
      return (rules.assume('a / c = b / c')
              .apply('multiplyBoth', 'c')
              .rewrite('/main/right', regroup)
              .rewrite('/main/right/right', cancel)
              .rewrite('/main/left', regroup)
              .rewrite('/main/left/right', cancel)
              .apply('simplifyStep')
              .apply('extractHyp', 'a / c = b / c'));
    }
  },

  'c != 0 => (a = b == a / c = b / c)': {
    proof: function() {
      var forward = (rules.assume('a = b')
                     .apply('divideBoth', 'c')
                     .apply('asImplication'));
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
      .apply('apply', '/main/right')
      .rewrite('/main/right/right', 'neg (neg a) = a');
    }
  },
  'neg a + b = b - a': {
    proof: function() {
      var parse = Toy.justParse;
      return rules.fact('a + neg b = a - b')
        .rewrite('/main/left', 'a + b = b + a');
        // .apply('instMultiVars', {a: parse('b'), b: parse('a')});
    }
  },
  'a - b = neg b + a': {
    proof: function() {
      return rules.fact('a + neg b = a - b')
      .apply('eqnSwap')
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
      .apply('instVar', 'neg a', 'a')
      .apply('addToBoth', Toy.parse('a'))
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
  'neg (a + b) = neg a + neg b': {
    proof: function() {
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
      .apply('arithmetic', '/main/right/left/left')
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

  // Four cases: each operation can be + or -, and initial association
  // can be to the left or right.
  'a + b - c = a + (b - c)': {
    proof: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', 'a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', 'a + neg b = a - b');
    }
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
    }
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
    }
  },

  // Simplification
  'a - a = 0': {
    proof: function() {
      return (rules.eqSelf('a - a')
              .apply('apply', '/right')
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
              .apply('instVar', 'recip d', 'b')
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
    proof: function() {
      var fact = rules.fact('a / b = a * recip b').apply('eqnSwap');
      return (rules.fact('a != 0 => a * recip a = 1')
              .rewrite('/main/left', fact));
    }
  }
};
$.extend(algebraFacts, divisionFacts);

var powerFacts = {
  'a ** 1 = a': {
    proof: function() {
      return rules.axiomNextPower()
      .apply('instMultiVars', {x: Toy.parse('a'), y: Toy.parse('0')})
      .apply('arithmetic', '/main/left/right')
      .rewrite('/main/right/left', rules.axiomPower0())
      .rewrite('/main/right', '1 * a = a');
    }
  },
  'a ** 2 = a * a': {
    proof: function() {
      return rules.axiomNextPower()
      .apply('instVar', '1', 'y')
      .rewrite('/main/right/left', 'a ** 1 = a')
      .apply('arithmetic', '/main/left/right');
    }
  },
  // TODO: Add a rule to convert a ** n to multiplication for any
  // non-negative integer n.
  'a ** 3 = a * a * a': {
    proof: function() {
      return rules.axiomNextPower()
      .apply('instVar', '2', 'y')
      .rewrite('/main/right/left', 'a ** 2 = a * a')
      .apply('arithmetic', '/main/left/right');
    }
  }
};
$.extend(algebraFacts, powerFacts);


// MOVING EXPRESSIONS AROUND

var algebraIdentities = {
  'a = neg b == a + b = 0': {
    proof: function() {
      var step = rules.assume('a = neg b')
      .apply('addToBoth', 'b')
      .rewrite('/main/right', 'neg a + a = 0')
      .apply('extractHyp', 'a = neg b');
      var converse = rules.assume('a + b = 0')
      .apply('addToBoth', 'neg b')
      .rewrite('/main/right', '0 + a = a')
      .rewrite('/main/left', 'a + b + c = a + (b + c)')
      .rewrite('/main/left/right', 'a + neg a = 0')
      .rewrite('/main/left', 'a + 0 = a')
      .apply('extractHyp', 'a + b = 0');
      var conj = rules.makeConjunction(step, converse);
      var taut = rules.tautology('(a => b) & (b => a) == (a == b)');
      return rules.rewrite(conj, '/main', taut);

    }
  },
  'a = b == a - b = 0': {
    proof: function() {
      return rules.fact('a = neg b == a + b = 0')
      .apply('instVar', 'neg b', 'b')
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
    Toy.addFactsMap(algebraFacts);
});

})();
