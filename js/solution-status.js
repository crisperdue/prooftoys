// Copyright 2016 Crispin Perdue.
// All rights reserved.

(function() {

var ProofEditor = Toy.ProofEditor;

/**
 * Truthy iff the given step matches some stated solution
 * for this ProofEditor.
 */
ProofEditor.prototype.matchesSolution = function(step) {
  // If this matches a specified solution, then great!
  if (this.solutions.length) {
    return Toy.each(this.solutions, function(solution) {
        if (Toy.termify(solution).alphaMatch(step) ||
            Toy.termify(solution).alphaMatch(step.getMain())) {
          return true;
        }
      });
  }
};

/**
 * Returns a solution status for a single equation in the context of a
 * set of names of variables free in the givens of an algebra problem.
 * If the equation LHS is anything other than a variable, or if the
 * RHS has the LHS variable free, or if the RHS contains any variable
 * not among the free variables of the givens, returns null.
 *
 * If the LHS is a variable and its RHS has no free variables, returns
 * 'simplify' if the RHS needs simplification, otherwise 'solved'.  If
 * the RHS contains free variables (among those in givenVars), returns
 * a list of their names.
 */
function eqnStatus(eqn, givenVars) {
  // The equation should have the form <var> = <expr>.
  if (!(eqn.isCall2('=') && eqn.getLeft().isVariable())) {
    return null;
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
 * Returns an object with properties, information useful to get from
 * givens and/or type conditions.  The value of each property of the
 * result is a list of terms that are conjuncts of the given expr.
 * The properties are:
 *   tcs: type conditions
 *   givens: members of the givens of the problem, excluding type conditions
 *   others: other terms
 * Each conjunct is categorized as exactly one of these.
 * Null input results in null value.
 * TODO: Only record one instance of any given, perhaps also others
 *   as well.
 */
function analyzeConditions(expr, givens) {
  var tcs = [];
  var givs = [];
  var others = [];
  function collate(x) {
    if (x.isTypeCond()) {
      tcs.push(x);
    } else if (alphaMatchesMember(x, givens)) {
      givs.push(x);
    } else {
      others.push(x);
    }
  }
  expr.scanConjuncts(collate);
  var result = {
    tcs: tcs,
    givens: givs,
    others: others
  };
  return result;
}

/**
 * Returns a list of object/maps, one for each disjunct ("solution")
 * of the given expression, each list element having the following
 * properties:
 *   eqns: Array of all equations among the term's conjuncts.
 *   byVar: a value for each equation in the solution with just a
 *     variable in its LHS, a value indexed by LHS variable name.
 *     If multiple equations have the same LHS variable, then the
 *     value is "overdetermined".  Otherwise it is an object with
 *     properties:
 *       eqn: the equation itself,
 *       status: status of the equation as from eqnStatus.
 *   tcs: list of any type conditions appearing in the "solution".
 *   others: other conjuncts in the "solution".
 *
 * Thus for example if x2 is the parsed form of "x = 2", the value is:
 * [{eqns: [x2], byVar: {x: {eqn: x2, status: 'solved'}}, tcs: [], others: []}]
 */
function analyzeSolutions(disj, givenVars) {
  var results = [];
  function handleSolution1(conj) {
    var byVar = {};
    var tcs = [];
    var others = [];
    function handleEqn(term) {
      var status = eqnStatus(term, givenVars);
      if (status) {
        var name = term.getLeft().name;
        if (byVar[name]) {
          byVar[name] = 'overdetermined';
        } else {
          var info = {
            eqn: term,
            status: status
          };
          byVar[name] = info;
        }
      } else if (term.isTypeCond()) {
        tcs.push(term);
      } else {
        others.push(term);
      }
    }
    conj.scanConjuncts(handleEqn);
    var result = {
      byVar: byVar,
      tcs: tcs,
      others: others
    };
    results.push(result);
  }
  disj.scanDisjuncts(handleSolution1);
  return results;
}

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

// True iff the given term is a given.
// TODO: Move in with other ProofEditor methods or REMOVE.
ProofEditor.prototype.isGiven = function(asm) {
  return alphaMatchesMember(asm, this.givens);
};

function alphaMatchesMember(term, array) {
  for (var i = 0; i < array.length; i++) {
    // Is it one of the givens?
    if (asm.alphaMatch(array[i])) return true;
  }
  return false;
};

/**
 * Returns solution status information for the equations of the given
 * solution in the context of the givenVars information.  The result
 * is in the form of an object/map keyed by variable name, with the
 * status information from eqnStatus for the equation with that
 * variable as its LHS.  If a variable appears in LHS position of more
 * than one equation of this "solution", returns status information
 * for that variable as 'overdetermined'.
 */
// TODO: REMOVE.
function oneSolutionStatus(solution, givenVars) {
  // Information about status of solution for each free variable,
  // with variable names as keys.  For each equation with non-null
  // solution status, associates its LHS variable name with the
  // status computed by eqnStatus.
  var byVar = {};
  // Add information about this solution part.  It will be
  // an equation: term1 = term2.
  function addSolutionPart(eqn) {
    var status = eqnStatus(eqn, givenVars);
    if (status) {
      var varName = eqn.getLeft().pname;
      byVar[varName] = (byVar[varName]
                        ? 'overdetermined'
                        : {eqn: eqn, status: status});
    }
  }
  solution.scanConjuncts(addSolutionPart);
  return byVar;
}

 /**
 * Extracts key information from the step, all related to solution status.
 *
 * Returns an object with properties:
 * structure: string, one of 'full', 
 */
ProofEditor.prototype.statusInfo = function(step) {
  var wff = step.wff;
  var givens = this.givens;
  var givenVars = this.givenVars;
  
  // String indicating the overall form of the step: one of 'full',
  // 'conditional', 'partial', or 'equiv'.
  var structure;
  // Info about type conditions only, may be null if there is no
  // such section in the input step.
  var tcInfo = null;
  // Info about givens and type conditions.
  var givensInfo;
  // Info about potential solutions.
  var solutionsInfo;

  // Exact solution, normally lhs givens, rhs solution(s).  Note that
  // if there are givens in the tc section, it is possible for there
  // to be "solutions" for which those givens are false.
  var full = wff.matchSchema('tc => (giv == sol)');
  // TODO: Consider also supporting tc => (sol == giv).
  if (full) {
    tcInfo = analyzeConditions(full.tc, givens);
    givensInfo = analyzeConditions(full.giv, givens);
    solutionsInfo = analyzeSolutions(full.sol, givenVars);
    structure = 'full';
  } else {
    //   Note that solutions are built from equations of the form:
    //     <var> = <term>
    //   and
    //     a => (b == c) == (a => b) & (a => c)
    var equiv = wff.matchSchema('tc_giv == sol');
    if (equiv) {
      givensInfo = analyzeConditions(full.tc_giv, givens);
      solutionsInfo = analyzeSolutions(full.sol, givenVars);
      structure = 'equiv';
    } else {
      var conditional = wff.matchSchema('lhs => rhs');
      if (conditional) {
        // This form has two distinct cases.  If the givens are on the
        // left, all solutions are conditional and must be checked
        // that they satisfy the givens.  We call this the "conditional"
        // form.
        //
        // If the givens are on the right, all solutions are valid,
        // but there may be others not deducible from this statement.
        // We call this the "partial" form.
        givensInfo = analyzeConditions(conditional.lhs, givens);
        solutionsInfo = analyzeSolutions(conditional.rhs, givenVars);
        var rhsGivensInfo = analyzeConditions(conditional.rhs, givens);
        structure = 'conditional';
        // Treat the step based on which part has more givens. The
        // idea is that as an actual solution is approached, more and
        // more givens transform into solutions.
        if (rhsGivensInfo.givens.length > givensInfo.givens.length) {
          // Take this as the "partial" form (solutions => givens).
          givensInfo = rhsGivensInfo;
          solutionsInfo = analyzeSolutions(conditional.lhs, givenVars);
          structure = 'partial';
        }
      }
    }
  }
  if (!structure) {
    return null;
  }
  var result = {
    structure: structure,
    tcInfo: tcInfo,
    givensInfo: givensInfo,
    solutionsInfo: solutionsInfo
  };
  return result;
}

// conditional: truthy if the format is conditions => solutions or
//   conditions1 => (conditions2 == solutions).  Type conditions
//   do not count as conditions in this case, only explicit (normally
//   equational conditions.  In this case any solutions found must
//   be tested to see if they satisfy the givens.
//
// partial: truthy if the format is solutions => conditions.  In this
//   case all solutions are valid, but there may be others also.
//

// Notes:
//
// If any givens are missing there may be excess solutions.
//
// If format is conds => sols, some of the sols may not be real solutions.
//
// If the format is conds => (givens == sols), and if conds includes
// any conditions besides type conditions, or if "givens" includes
// conditions that are not givens or tcs, the sols may not be
// complete.  An exception is that conds may include (temporary)
// definitions.  These will be eliminable if / when their uses have been
// eliminated.

// TODO: Keep comments, remove existing code here?
/**
 * Returns information about apparent progress toward solution of a
 * problem of solving an equation.  The problem may be stated with
 * multiple variables and may have multiple solutions, so in the
 * general case the "solution" may be a disjunction of multiple
 * conjunctions, each conjunction representing one specific solution
 * to the problem.  A specific solution may have multiple equations,
 * one for each variable to be solved for.
 *
 * "Atomic" status values:
 *
 * Boolean - true or false if there are stated solutions and the step
 *   does (or does not) match one.
 *
 * Else false if standardSolution is false.
 * Else "noGivens" if there are no givens.
 *
 * This method handles steps of these three forms:
 * typeAsms => (givens == equations); or
 * typeAsms & givens => equations; or conceivably some mixture:
 * typeAsms & someGivens => (moreGivens == equations)
 *
 * If none of the above (mostly error) conditions applies, the return
 * value is an object with properties as follows:
 *
 * precise: true iff main connective is == (not =>) after assuming
 *   appropriate types for variables.
 * solutions: list of individual solution status objects.
 * nDisjuncts: number of disjuncts in the "solutions" section of the
 *   statement.
 *
 * Solution status object; one for each conjunction that shows signs
 *   of progress toward being a solution:
 *
 *   formula: formula (conjunction) representing this solution.
 *   byVar: object/map indexed by variable name.  Each value is an
 *       object/map with properties:
 *     eqn: the equation in this solution with this variable as its LHS.
 *     status: 'solved', 'simplify', 'overdetermined', or a
 *       list of names of other variables the given variable is solved
 *       for in the given step.  Variables not in solution position are
 *       not included.  "Solved" indicates the variable appears in
 *       solution position in exactly one equation, depending on no free
 *       variables.  "Simplify" indicates the same, except the RHS is
 *       not simplified.  "Overdetermined" indicates that the variable
 *       appears in solution position in more than one equation.
 */
ProofEditor.prototype.solutionStatus = function(step) {
  // TODO: Support simplified expressions other than trivial
  // fractions.

  // If there is a list of solutions, true or falsy if the step
  // matches one.
  if (this.matchesSolution(step)) {
    return true;
  }
  // This method declared not applicable in this ProofEditor.
  if (!this.standardSolution) {
    return 'noStandard';
  }
  if (this.givens.length == 0) {
    return 'noGivens';
  }
  var givenVars = this.givenVars;
  var info = this.statusInfo(step);

  var solutions = info.solutionsInfo;

  // Indicates that (the step has assumptions and) the assumptions
  // include one or more givens.  If true, the main may be a solution,
  // but not a precise solution.
  var asmsGiven = info.missing.length < this.givens.length;
  var result = {
    precise: info.structure !== 'conditional',
    solutions: solutionResults,
    nDisjuncts: nDisjuncts,
    missing: info.missing,
    extra: info.extraConds
  };
  return result;
};

window.eqnStatus = function(eqn_arg) {
  var eqn = Toy.termify(eqn_arg);
  return eqnStatus(eqn, eqn.freeVars());
};

})();
