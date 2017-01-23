// Copyright 2016, 2017 Crispin Perdue.
// All rights reserved.

(function() {

var isEmpty = Toy.isEmpty;  
var ProofEditor = Toy.ProofEditor;
var TermSet = Toy.TermSet;

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
 * Returns an object with properties having useful information from a
 * TermSet of givens and/or type conditions.  The value of each
 * property of the result is a list of terms that are conjuncts of the
 * given expr.  The properties are TermSets:
 *   tcs: type conditions
 *   givens: members of the givens of the problem, excluding type conditions
 *   others: other terms
 * Each conjunct is categorized as exactly one of these.
 */
function analyzeConditions(expr, givens) {
  var tcs = new TermSet();
  var givs = new TermSet();
  var others = new TermSet();
  function collate(x) {
    if (x.isTypeCond()) {
      tcs.add(x);
    } else if (givens.has(x)) {
      givs.add(x);
    } else {
      others.add(x);
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
 * Returns a solution status for a single equation given also a set of
 * names of variables free in the givens of an algebra problem.
 *
 * If the equation LHS is anything other than a variable (in the
 * givenVars), or if the RHS has the LHS variable free, or if the RHS
 * contains any variable not among the given object / set of variable
 * names, returns null.
 *
 * Otherwise returns an object/set of the variable names that occur
 * free in the RHS, i.e. this term has the form of a solution for the
 * LHS variable in terms of the returned set of RHS variables.
 */ 
function eqnStatus(eqn, givenVars) {
  var parts = eqn.matchSchema('v = t');
  if (!parts) {
    return null;
  }
  var vbl = parts.v;
  var varName = vbl.isVariable() && vbl.name;
  // The equation should have the form <var> = <expr>.
  if (!(parts && varName && givenVars[varName])) {
    return null;
  }
  var answer = parts.t;
  // Map keyed by names of variables in the "answer" part.
  var rightVars = answer.freeVars();
  if (Toy.hasOwn(rightVars, varName)) {
    return null;
  }
  for (var name in rightVars) {
    if (!givenVars[name]) {
      // The answer may depend on a variable not in the problem
      // statement.
      return null;
    }
  }
  return rightVars;
}

/**
 * Internal to analyzeSolutions.  Analyzes one term of a disjunction
 * within a "solutions" formula.  The given term itself is potentially
 * a conjunction.  Builds and returns the information structure that
 * will be the relevant element of the array returned by
 * analyzeSolutions.
 */
function analyze1Solution(conj, givenVars) {
  var eqns = [];
  var byVar = {};
  var overages = {};
  var tcs = new TermSet();
  var others = new TermSet();
  function analyzeConjunct(term) {
    var status = eqnStatus(term, givenVars);
    if (status) {
      eqns.push(term);
      var name = term.getLeft().name;
      if (byVar[name]) {
        delete byVar[name];
        overages[name] = true;
      } else {
        var info = {
          eqn: term,
          using: status
        };
        byVar[name] = info;
      }
    } else if (term.isTypeCond()) {
      tcs.add(term);
    } else {
      others.add(term);
    }
  }
  conj.scanConjuncts(analyzeConjunct);
  var result = {
    byVar: byVar,
    eqns: eqns,
    overages: overages,
    tcs: tcs,
    others: others
  };
  return result;
}

/**
 * Returns an array of object/maps, one for each disjunct
 * ("solution") of the given expression.  We will call each of these
 * object/maps a "solution info" object, having the following
 * properties:
 *   eqns: Array of all equations among the term's conjuncts.
 *   overages: a map/set of names of variables that appear in more than
 *     one equation of this "solution" as its LHS.
 *   byVar: an object/map with an entry for each variable that appears
 *     in exactly one equation of the solution as its LHS.  Each entry
 *     value is an object with properties:
 *       eqn: the equation itself,
 *       using: set of RHS vars of the equation as from eqnStatus.
 *   tcs: TermSet of any type conditions appearing in the "solution".
 *   others: TermSet of other conjuncts in the "solution".
 *
 * Thus for example if x2 is the parsed form of "x = 2", the value is:
 * [{byVar: {x: {eqn: x2, using: {}}}, overages: {},
 *   tcs: TermSet(...), others: TermSet(...)}]
 */
function analyzeSolutions(disj, givenVars) {
  var results = [];
  function analyze(term) { results.push(analyze1Solution(term, givenVars)); }
  disj.scanDisjuncts(analyze);
  return results;
}

/**
 * True iff expr is a fraction in lowest terms.
 */
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

/**
 * Extracts key information from the given step, related to solution
 * status.  If the step does not match any of the understood formats,
 * returns null.
 *
 * Otherwise returns an object with properties:
 *   structure: string, one of "full", "equiv", "confirmation", or "tentative".
 *   tcInfo: information from analyzeConditions if the format is "full",
 *     otherwise null.
 *   givensInfo: information on givens (and type conditions) from
 *     analyzeConditions.
 *   solutionsInfo: information on solutions from analyzeSolutions.
 */
ProofEditor.prototype.statusInfo = function(step) {
  var wff = step.wff;
  var givens = this.givens;
  var givenVars = this.givenVars;
  
  // String indicating the overall form of the step: one of 'full',
  // 'tentative', 'confirmation', or 'equiv'.
  var structure;
  // Info about type conditions only, may be null if there is no
  // such section in the input step.
  var tcInfo = null;
  // Info about givens and type conditions.
  var givensInfo;
  // Info about potential solutions.
  var solutionsInfo;

  // An exact solution can look like this, normally lhs givens, rhs
  // solution(s).  Note that if there are givens in the tc section, any
  // "solutions" are actually candidates and need checking.
  var full = wff.matchSchema('t => (g == s)');
  if (full && wff.getRight().getBinOp().pname === '==') {
    // TODO: Remove the pname check when the terms all have type information
    // built into them.
    tcInfo = analyzeConditions(full.t, givens);
    givensInfo = analyzeConditions(full.g, givens);
    solutionsInfo = analyzeSolutions(full.s, givenVars);
    structure = 'full';
  } else {
    var equiv = wff.matchSchema('g == s');
    if (equiv) {
      givensInfo = analyzeConditions(equiv.g, givens);
      solutionsInfo = analyzeSolutions(equiv.s, givenVars);
      structure = 'equiv';
    } else {
      var conditional = wff.matchSchema('l => r');
      if (conditional) {
        // This form has two distinct cases.  If the givens are on the
        // left, all solutions are conditional and must be checked
        // that they satisfy the givens.  We call this the "conditional"
        // form.
        //
        // Call it a "tentative" for now.
        structure = 'tentative';
        givensInfo = analyzeConditions(conditional.l, givens);
        solutionsInfo = analyzeSolutions(conditional.r, givenVars);
        var rhsGivensInfo = analyzeConditions(conditional.r, givens);
        // Classify the step based on which part has more givens. The
        // idea is that as an actual solution is approached, more and
        // more givens are transformed, eventually taking the form of
        // solutions.
        if (rhsGivensInfo.givens.size() > givensInfo.givens.size()) {
          // Take this as the "confirmation" form (solutions => givens).
          //
          // If the lhs is in the form of a solution and the rhs is in
          // the form of one or more givens, the solution is valid, but
          // there may be other solutions as well.
          givensInfo = rhsGivensInfo;
          solutionsInfo = analyzeSolutions(conditional.l, givenVars);
          structure = 'confirmation';
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
};

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
//
// About the "type" property of the result: 
// tentative: truthy if the format is conditions => solutions or
//   conditions1 => (conditions2 == solutions).  Type conditions
//   do not count as conditions in this case, only explicit (normally
//   equational conditions.  In this case any solutions found must
//   be tested to see if they satisfy the givens.
//
// confirmation: truthy if the format is solutions => conditions.  In this
//   case all solutions are valid, but there may be others also.

/**
 * Returns solution status in a form prepared for straightforward
 * display.  Current return values, in order of checking:
 *
 * true: iff the step matches a stated solution.
 * 'noStandard': if this ProofEditor has standardSolution turned off.
 * 'noGivens': if the problem has no givens.
 * null: if not in any of the formats recognized by statusInfo.
 * null: if this is in the form of a confirmation, but does not solve
 *   for all variables, has overages or extra conditions in the LHS.
 * 
 * If in the form <solution> => <givens>, an object with properties:
 * type: 'confirmation'
 * givens: a TermSet of the givens in the RHS.
 * solution: an object/map of information about solutions "by variable"
 * In this form there is no harm if the RHS has additional conjuncts that
 * are not givens, but they are not part of the return value.
 *
 * If in tentative or equivalence form:
 * If extra assumptions are present, an object with property:
 * type: 'extras'
 * extras: TermSet of those extra assumptions
 *
 * Otherwise in case of these forms, an object with properties:
 * type: 'equiv' if truly an equivalence (no givens with type conds),
 *   otherwise 'tentative'.
 * solutions: array of solution status objects.  In this context the
 *   "byVar" property is typically the one of interest, and "overages"
 *   should be checked.
 * absentGivens: TermSet of any problem givens not in the assumptions
 *   or LHS.
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
  var problemGivens = this.givens;
  if (problemGivens.size() == 0) {
    return 'noGivens';
  }
  var info = this.statusInfo(step);

  if (info == null) {
    return null;
  }

  var structure = info.structure;
  var solsInfo = info.solutionsInfo;
  var givsInfo = info.givensInfo;

  if (structure == 'confirmation') {
    // A confirmation has the form of <solution(s)> => <given(s)>,
    // with one or more solutions and one or more givens.
    // 
    // We consider this step to be notable progress if, other than
    // type conditions, its LHS contains only a conjunction of
    // equations in solution form, each with no RHS variables, and its
    // RHS contains one or more givens conjoined.  Normally the LHS
    // solves for all variables of the problem, but that is not
    // technically required.  After all, assumptions can be added
    // later.
    //
    // One full solution can built from multiple steps with the same
    // LHS if every given is in the RHS of one of those steps.  (It
    // can the entire RHS or a conjunct.)  In this case it is
    // especially important for the solution equations to be fully
    // simplified.

    // At most one full solution is present in this format, possibly
    // just a solution for one variable.
    // TODO: Consider extending this code to handle LHS disjunctions,
    // thus multiple solutions in one step; looks easy to implement.
    if (solsInfo.length == 0) { return null; }
    var solInfo = solsInfo[0];
    var overages = solInfo.overages;
    var eqnsByVar = solInfo.byVar;

    // Ignore steps that have certain kinds of defects.
    // TODO: Check tcs appropriately.
    if (isEmpty(givsInfo) || !isEmpty(overages) || solInfo.others.size()) {
      return null;
    }
    var result = {
      // This step does not preclude other solutions.
      type: 'confirmation',
      givens: givsInfo.givens,
      solution: eqnsByVar
    };
    return result;
  } else {
    // The structure of the step is essentially either givens => solutions
    // or possibly givens == solutions, which we treat almost the same.
    var tcInfo = info.tcInfo;
    var tcGivens = tcInfo ? tcInfo.givens : new TermSet();
    var tcOthers = tcInfo ? tcInfo.others : new TermSet();
    var allOthers = new TermSet();
    // eslint-disable-next-line no-inner-declarations
    function add(value) { allOthers.add(value); }
    givsInfo.others.each(add);
    tcOthers.each(add);

    // If an extra assumption is present, we do not show this step as
    // progress toward a solution.  Although the extra assumption
    // might not have been used to derive the step's conclusion or
    // that it is consistent with the givens, most likely any
    // tentative solution would be spurious.
    if (allOthers.size()) {
      // Something like this.
      result = {
        type: 'extras',
        extras: allOthers
      };
      return result;
    }
    var isConditional = (structure == 'tentative' ||
                         structure == 'equiv' && tcGivens.size());
    var givensPresent = new TermSet().addAll(givsInfo.givens).addAll(tcGivens);
    var absentGivens = new TermSet();
    // Returns fml iff it is not present in this step.
    // eslint-disable-next-line no-inner-declarations
    function checkAbsent(fml) {
      if (!givensPresent.has(fml)) {
        absentGivens.add(fml);
      }
    }
    problemGivens.each(checkAbsent);
    
    // This step (may) show progress toward a solution or solutions.
    // The caller can use the status to describe the progress toward
    // solution(s).
    result = {
      type: isConditional ? 'tentative' : 'equiv',
      solutions: solsInfo,
      absentGivens: absentGivens
    };
    return result;
  }
};

ProofEditor.prototype.solutionMessage = function(step) {
  var status = this.solutionStatus(step);
  if (status == true) {
    return 'You have found a solution';
  } else if (status === 'noStandard' ||
             status === 'noGivens' ||
             status == null) {
    return '';
  } else if (status.extras) {
  } else {
    var type = status.type;
    function termSetList(terms) {
      var a = [];
      terms.each(function (a) { extras.push(a.toUnicode()); });
      return extras.join(', ');
    }
    if (type === 'extras') {
      var asms = termSetList(status.extras);
      return ('Caution: step has extra assumptions: ' + asms);
    } else if (type === 'confirmation') {
      if (status.givens.superset(this.givens)) {
        return 'This is one solution to the problem';
      } else {
        return ('This is one solution of ' + termSetList(status.givens));
      }
    } else if (type === 'equiv' || type === 'tentative') {
      var format = Toy.format;
      var isEmpty = Toy.isEmpty;
      var solutions = status.solutions;
      var msgs = [];
      for (var i = 0; i < solutions.length; i++) {
        var sol = solutions[i];
        if (sol.eqns.length === 0) {
          continue;
        }
        var solMsg = sol.eqns.map(x => x.toUnicode()).join(' \u2227 ');
        msgs.push(format('{1} solves for ', solMsg));
        var overages = sol.overages;
        if (isEmpty(overages)) {
          var byVar = sol.byVar;
          for (var name in byVar) {
            var termsOf = byVar[name].using;
            if (isEmpty(termsOf)) {
              msgs.push(format('  {1}', name));
            } else {
              msgs.push(format('  {1} in terms of {2}', name, termsOf.join(', ')));
            }
          }
        }
      }
      if (msgs.length) {
        msgs.unshift(type === 'tentative' ? 'Candidate solutions:' : 'Solutions:');
      }
      return msgs.join('\n');
    }
  }
};

// For testing:
Toy._eqnStatus = eqnStatus;
Toy._analyzeConditions = analyzeConditions;
Toy._analyze1Solution = analyze1Solution;
Toy._analyzeSolutions = analyzeSolutions;
Toy._isLowestTerms = isLowestTerms;

})();