// Copyright 2016 Crispin Perdue.
// All rights reserved.

(function() {

var StepEditor = Toy.StepEditor;

/**
 * Truthy iff the given step matches some stated solution
 * for this StepEditor.
 */
StepEditor.prototype.matchesSolution = function(step) {
  // If this matches a specified solution, then great!
  if (this.solutions.length) {
    return Toy.each(this.solutions, function(solution) {
        if (Toy.termify(solution).alphaMatch(step) ||
            Toy.termify(solution).alphaMatch(step.getMain())) {
          return true;
        }
      }) && 'You have found a valid solution';
  }
};

// True iff expr is a fraction in lowest terms.
function isLowestTerms(expr) {
  // Computes the GCD of the left and right operands of the given Expr,
  // ordinarily a division.
  function gcd(expr) {
    return Toy.gcd(expr.getLeft().getNumValue(),
                   expr.getRight().getNumValue());
  }
  return (expr.isNumeral() ||
          (Toy.isFraction(expr) && gcd(expr) === 1));
}

// True iff the given assumption is neither a type condition nor
// a given.
StepEditor.prototype.isGiven = function(asm) {
  var givens = this.givens;
  var len = givens.length;
  for (var i = 0; i < len; i++) {
    // Is it one of the givens?
    if (asm.alphaMatch(givens[i].getMain().getRight())) return true;
  }
  return false;
};

function notTypeCond(asm) {
  return !asm.isTypeCond();
}

/**
 * Returns a solution status for a single equation as described for
 * StepEditor.solutionStatus.  If the equation LHS is simply a
 * variable, returns 'none', 'solved', 'simplify', 'overdetermined',
 * or a list of names of other variables it is solved for in the given
 * step.  Otherwise returns null.
 */
function eqnStatus(eqn, givenVars) {
  // The equation should have the form <var> = <expr>.
  if (!(eqn.isCall2('=') && eqn.getLeft().isVariable())) {
    return null;
  }

  function power(status) {
    return (status == 'solved'
            ? 10
            : status == 'simplify'
            ? 5
            : 1);
  }
  var varName = eqn.getLeft().pname;
  var answer = eqn.getRight();
  if (isLowestTerms(answer)) {
    return 'solved';
  } else {
    // In this case check more carefully if this may be a
    // solution that needs simplification or if it may be a
    // solution in terms of other variables.

    // Map keyed by names of variables in the "answer" part.
    var rightVars = answer.freeVars();
    // List of names of vars in the answer.
    var rightVarsList = [];
    if (Toy.isEmpty(rightVars)) {
      return 'simplify';
    } else {
      // This may be a partial solution.
      for (name in rightVars) {
        rightVarsList.push(name);
        if (!givenVars[name] || name == varName) {
          // The answer depends on a variable not in the problem
          // statement or on the LHS vriable, so it is not even a
          // partial solution.
          return null;
        }
      }
      return rightVarsList;
    }
  }
}

/**
 * Returns the status for one solution in the context of the givenVars
 * information.
 */
function oneSolutionStatus(solution, givenVars) {
  // Information about status of solution for each free variable,
  // with variable names as keys.  For each equation with non-null
  // solution status, associates its LHS variable name with the
  // status computed by eqnStatus.
  var byVar = {};
  // True iff some solution part is not in "solution form".
  var conditional = false;
  // Add information about this solution part.  It will be
  // an equation: term1 = term2.
  function addSolutionPart(eqn) {
    var status = eqnStatus(eqn, givenVars);
    if (status) {
      var varName = eqn.getLeft().pname;
      byVar[varName] = (byVar[varName]
                        ? 'overdetermined'
                        : {eqn: eqn, status: status});
    } else {
      conditional = true;
    }
  }
  // Add info for this solution into "vars".  The solution may be a
  // conjunction of equations or a single equation.
  solution.scanConjuncts(addSolutionPart);
  return {byVar: byVar, formula: solution, conditional: conditional};
}

StepEditor.prototype._checkFaults = function(step) {
  var self = this;
  var wff = step.wff;
  // List of "givens" for the problem.
  var givens = this.givens;

  // Determine the solution from its form and the givens.
  // At this point if there are no givens there can be no solution.
  if (givens.length == 0) {
    return 'noGivens';
  }

  // True if one or more assumptions is neither a type assumption
  // nor a given.
  if (wff.isCall2('=>')) {
    function isBadAsm(asm) {
      if (!self.isGiven(asm) && !asm.isTypeCond()) {
        return true;
      }
    }
    var badAsms = wff.getLeft().scanConjuncts(isBadAsm);
    if (badAsms) {
      // If the step has extraneous assumptions, it is not a solution.
      return 'badAsms';
    }
  }

  var main = wff.getMain();
  // If there is an ==, the solutions are its RHS, otherwise they are
  // the entire main.
  var solutions = main;
  if (main.isCall2('==')) {
    solutions = main.getRight();
    function notGiven(e) {
      if (!self.isGiven(e)) { return true; }
    }
    // All LHS conjuncts should be givens.
    if (main.getLeft().scanConjuncts(notGiven)) {
      return 'badLHS';
    }
  }
}

/**
 * This deals with solutions that in the general case may be a
 * disjunction of multiple conjunctions, each conjunction representing
 * one solution to the problem.  A solution has the form of a
 * conjunction of equations, where each equation has just a variable
 * on the left, and a simplified term on the right.  If a variable
 * appears by itself on the LHS, we will say it appears in solution
 * position.
 *
 * "Atomic" status values:
 *
 * Boolean - true or false if there are stated solutions and the step
 *   does or does not match one.
 *
 * Else false if standardSolution is false.
 * Else "noGivens" if there are no givens.
 * Else "badAsms" if the step uses extra assumptions.
 *
 * This method handles steps of these three forms:
 * typeAsms => givens == equations; or -
 * typeAsms & givens => equations; or conceivably some mixture:
 * typeAsms & someGivens => moreGivens == equations
 *
 * The first and third forms contain an equivalence.  This method only
 * recognizes solutions and partial solutions in which the LHS
 * contains only givens.  It returns
 *
 * "badLHS" if the LHS of the equivalence has any conjuncts that are
 *   not givens.
 *
 * If none of the above (mostly error) conditions applies, the return
 * value is an object with properties as follows:
 *
 * precise: true iff main connective is == (not =>) after assuming
 *   appropriate types for variables.
 * solutions: list of individual solution status objects.
 *
 * Solution status object; one for each conjunction and refers to the
 *   equations in that conjunction:
 *
 *   formula: formula (conjunction) representing this solution.
 *   byVar: object/map indexed by variable name.  Each value is an
 *       object/map with properties:
 *     eqn: the equation in this solution with this vbl as its LHS.
 *     status: 'none', 'solved', 'simplify', 'overdetermined', or a
 *       list of names of other variables the given variable is solved
 *       for in the given step.  Variables not in solution position are
 *       not included.  "Solved" indicates the variable appears in
 *       solution position in exactly one equation, depending on no free
 *       variables.  "Simplify" indicates the same, except the RHS is
 *       not simplified.  "Overdetermined" indicates that the variable
 *       appears in solution in more than one equation.
 */
StepEditor.prototype.solutionStatus = function(step) {
  // TODO: Support simplified expressions other than trivial
  // fractions.

  // If there is a list of solutions, true or falsy if the step
  // matches one.
  if (this.solutions.length) {
    return Toy.each(this.solutions, function(solution) {
        if (Toy.termify(solution).alphaMatch(step)) {
          return true;
        }
      }) || false;
  }

  // This method declared not applicable in this StepEditor.
  if (!this.standardSolution) {
    return false;
  }

  var fault = this._checkFaults(step);
  if (fault) {
    return fault;
  }

  var wff = step.wff;
  var main = wff.getMain();
  var solutions = main.isCall2('==') ? main.getRight() : main;

  // Everything but the solutions part is OK.  Now attempt to treat
  // "solutions" as a disjunction of conjunctions of equations.

  // An object/set with names of all variables in any of the
  // givens:
  // TODO: Precompute the givenVars and use here.
  var givenVars = {};
  this.givens.forEach(function(g) { $.extend(givenVars, g.wff.freeVars()); });

  // This will be a list of solution results, one for each solution.
  var solutionResults = [];
  solutions.scanDisjuncts(function(term) {
      solutionResults.push(oneSolutionStatus(term, givenVars));
    });

  // Indicates that (the step has assumptions and) the assumptions
  // include one or more givens.  If true, the main may be a solution,
  // but not a precise solution.
  var asmsGiven = (wff.isCall2('=>') &&
                   wff.getLeft().scanConjuncts(this.isGiven.bind(this)));
  return {precise: !asmsGiven, solutions: solutionResults};
};

})();
