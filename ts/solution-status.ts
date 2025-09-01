// Copyright Crispin Perdue.  All rights reserved.

namespace Toy {

'use strict';

var isEmpty = Toy.isEmpty;  
var ProofEditor = Toy.ProofEditor;
var TermSet = Toy.TermSet;

/**
 * Returns an object with properties having useful information about a
 * term ("expr") in the context of a
 * TermSet of givens and/or type conditions.  The value of each
 * property of the result is a list of terms that are conjuncts of the
 * given expr.  The properties are TermSets:
 *   tcs: type declarations  TODO: Rename to tds.
 *   givens: members of the givens of the problem, excluding type conditions
 *   others: other terms
 * Each conjunct is categorized as exactly one of these.
 */
export function analyzeConditions(expr, givens) {
  var tcs = new TermSet();
  var givs = new TermSet();
  var others = new TermSet();
  function collate(x) {
    if (x.isTypeDecl()) {
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
 * Accepts a single equation, checking that it is of the form v = t,
 * where v among the given vars, and t a term with free variables only
 * among givenVars, and not including v.
 *
 * If the criteria are met, returns an object/set of the variable names
 * that occur free in the RHS, i.e. this term has the form of a solution
 * for the LHS variable in terms of the returned set of RHS variables.
 *
 * If eqn is not of this form, returns null.
 */ 
export function eqnDeps(eqn, givenVars) {
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
 * Internal to analyzeSolutions.  Analyzes one term of a disjunct of a
 * "solutions" formula.  The given term itself is potentially a
 * conjunction.  Builds and returns the information structure that
 * will be the relevant element of the array returned by
 * analyzeSolutions.
 * 
 * For conjuncts found by scanConjuncts, if the conjunct is acceptable
 * to eqnDeps either as given, or commuted, works with its result as a
 * status.  Any variable that eqnDeps takes as the variable solved for
 * in an equation in more than one conjunct is taken as an "overage".
 */
function analyze1Solution(conj, givenVars) {
  var eqns = [];
  var byVar = {};
  var overages = {};
  var tcs = new TermSet();
  var others = new TermSet();
  function analyzeConjunct(term) {
    var swapped = false;
    var status = eqnDeps(term, givenVars);
    if (!status && term.isCall2('=')) {
      swapped = true;
      status = eqnDeps(Toy.commuteEqn(term), givenVars);
    }
    if (status) {
      eqns.push(term);
      var name = swapped ? term.getRight().name : term.getLeft().name;
      if (byVar[name]) {
        delete byVar[name];
        overages[name] = true;
      } else {
        var info = {
          eqn: term,
          swapped: swapped,
          using: status
        };
        byVar[name] = info;
      }
    } else if (term.isTypeDecl()) {
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
 * Apply analyze1Solution to each disjuct of the given "solution part"
 * of a formula, potentially a disjunction of conjunctions,
 * returning an array of plain objects with the following properties,
 * one for each disjunct.  We will call each of these
 * object/maps a "solution info" object, having the following
 * properties:
 *   eqns: Array of all equations among the term's conjuncts.
 *     Each of these is potentially a solution for one variable of
 *     the given problem.
 *   overages: a map/set of names of variables that are overdetermined in
 *     the sense that appear as the LHS of more than
 *     one equation of this "solution".
 *   byVar: an object/map with an entry for each variable that appears
 *     as they LHS of exactly one equation of the "solution" conjunction.
 *     Each entry value is an object with properties:
 *       eqn: the equation itself,
 *       using: set of RHS vars of the equation as from eqnStatus.
 *   tcs: TermSet of any type conditions appearing in the "solution".
 *   others: TermSet of other conjuncts in the "solution".
 *
 * Thus for example if x2 is the parsed form of "x = 2", the value is:
 * [{byVar: {x: {eqn: x2, using: {}}}, overages: {},
 *   tcs: TermSet(...), others: TermSet(...)}]
 */
export function analyzeSolutions(disj, givenVars) {
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
 * TODO: Refactor this into a "problem source" or something like it,
 *   with these methods and some properties such as:
 * 
 * solutions: specified solutions
 * givens: (read-only) TermSet of conjuncts of the
 *   problem statement as supplied to solveReal; typically equations.
 * standardSolution: boolean, true to enable standard processing 
 */
export interface ProofEditor {
  matchesSolution(step);
  statusInfo(step);
  solutionStatus(step);
  progressMessage(step);
  messageForSolution(step, sol);
}

// This defines solutionStatus-related methods of a
// proof editor, or potentially some other "problem source".
var methods = {

  /**
   * Truthy iff the given step matches some stated solution
   * for this ProofEditor.
   */
  matchesSolution: function(step) {
    // If this matches a specified solution, then great!
    if (this.solutions.length) {
      return Toy.each(this.solutions, function(solution) {
          if (Toy.termify(solution).alphaMatch(step) ||
              Toy.termify(solution).alphaMatch(step.getMain())) {
            return true;
          }
        });
    }
  },

  /**
   * Extracts key information from the given step, related to solution
   * status, for use by solutionStatus.  If the step does not match any
   * of the understood formats, returns null.
   * 
   * This classifies the step structure as "full" if a conditional
   * equivalence; "equiv" if a pure equivalence, and either "tentative"
   * or "confirmation" if some other variety of conditional.  If the RHS
   * has more problem statement "given" terms than the LHS, then
   * "confirmation", else "tentative".  (Usually the choice is
   * clearcut.)
   *
   * In these cases, returns an object with properties:
   *   structure: string, one of "full", "equiv", "confirmation", or "tentative".
   *   tcInfo: information from applying analyzeConditions to the step's
   *     assumptions if the format is "full", otherwise null.
   *   givensInfo: information from applying analyzeConditions to the
   *     step's "givens" part, if any.
   *   solutionsInfo: information on solutions from analyzeSolutions.
   */
  statusInfo: function(step) {
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
    // TODO: Consider modifying matchSchema to require "==" in the
    //   wff; then remove the excess isEquivOp test here.
    if (full && wff.get('/right/binop').isEquivOp()) {
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
  },

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
  //   equational) conditions.  In this case any solutions found must
  //   be tested to see if they satisfy the givens.
  //
  // confirmation: truthy if the format is solutions => conditions.  In this
  //   case all solutions are valid, but there may be others also.

  /**
   * Returns solution status in a form prepared for straightforward
   * display.  In typical cases this is based on the result of calling
   * this.statusInfo.
   * 
   * Return values, in order of checking, are:
   *
   * true: iff the step matches a stated solution.
   * 'noStandard': if this ProofEditor has standardSolution turned off.
   * 'noGivens': if the problem has no givens.
   * null: if not in any of the formats recognized by statusInfo.
   * null: if this is in the form of a confirmation, but does not solve
   *   for all variables, has overages or extra conditions in the LHS.
   * 
   * If the step has the form <solution> => <givens>, an object with
   * properties:
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
   * type: 'equiv' if truly an equivalence (no givens among the type
   *   conds), otherwise 'tentative'.
   * solutions: array of solution status objects.  In this context the
   *   "byVar" property is typically the one of interest, and "overages"
   *   should be checked.
   * absentGivens: TermSet of any problem givens not in the assumptions
   *   or LHS.
   */
  solutionStatus: function(step) {
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
      //   thus multiple solutions in one step; looks easy to implement.
      // TODO: Handle the case where there are no solutions because
      //   the "solutions part" is F (false).  This means there are no
      //   solutions.
      if (solsInfo.length == 0) { return null; }
      var solInfo = solsInfo[0];
      var overages = solInfo.overages;
      var eqnsByVar = solInfo.byVar;

      // Ignore steps that have certain kinds of defects.
      // TODO: Check tcs appropriately.
      if (isEmpty(givsInfo) || !isEmpty(overages) || solInfo.others.size()) {
        return null;
      }
      let result = {
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
      // If an extra assumption is present, we may not want to show
      // this step as progress toward a solution.  Although the extra
      // assumption might not have been used to derive the step's
      // conclusion or that it is consistent with the givens, most
      // likely any tentative solution would be spurious.
      // TODO: Figure out reasonable ways to distinguish between
      //   arbitrary extra assumptions and necessary ones such as
      //   division by nonzero.
      var allOthers = new TermSet();
      function add(value) { allOthers.add(value); }
      givsInfo.others.each(add);
      tcOthers.each(add);

      var isConditional = (structure == 'tentative' ||
                           structure == 'equiv' && tcGivens.size());
      var givensPresent = new TermSet().addAll(givsInfo.givens).addAll(tcGivens);
      var absentGivens = new TermSet();
      // Returns fml iff it is not present in this step.
      function checkAbsent(fml) {
        if (!givensPresent.has(fml)) {
          absentGivens.add(fml);
        }
      }
      problemGivens.each(checkAbsent);

      // This step (may) show progress toward a solution or solutions.
      // The caller can use the status to describe the progress toward
      // solution(s).
      let result = {
        type: isConditional ? 'tentative' : 'equiv',
        solutions: solsInfo,
        absentGivens: absentGivens,
        extras: allOthers
      };
      return result;
    }
  },

  /**
   * Solution progress message for the entire step as a single string,
   * based on the solutionStatus of the step. It could be a combination
   * of multiple messages separated in case of multiple solutions, or
   * null if there is no notable progress.
   *
   * TODO: Consider how to handle underdetermined problems.
   */
  progressMessage: function(step) {
    var status = this.solutionStatus(step);
    if (status == true) {
      // This is the meaning of this status.
      return 'You have found a solution';
    } else if (status === 'noStandard' ||
               status === 'noGivens' ||
               status == null ||
               // No message if the step has none of the givens as an
               // assumption.  Most likely it is some general fact not
               // directly part of progress toward the solution.
               (status.absentGivens &&
                status.absentGivens.size() == this.givens.size())) {
      return null;
    } else {
      var type = status.type;
      if (type === 'confirmation') {
        // TODO: Consider if extras should be reported here.
        if (status.givens.superset(this.givens)) {
          return 'This is one solution to the problem';
        } else {
          return ('This is one solution of ' + status.givens);
        }
      } else if (type === 'equiv' || type === 'tentative') {
        var solutions = status.solutions;
        if (solutions.length == 1 && solutions[0].others.has(Toy.parse('F'))) {
          // If there was just one "solution" with one of the "others"
          // being "F", we have shown there is no solution.
          return '&check; You have shown there is no solution.';
        }
        var messages = [];
        // Count of non-empty messages to report.
        var nonempties = 0;
        // Count of the number of full solutions found.
        var fullCount = 0;
        for (var i = 0; i < solutions.length; i++) {
          var sol = solutions[i];
          var msg = this.messageForSolution(step, sol);
          messages.push(msg);
          if (msg) { nonempties++; }
          // Heuristic to detect a "full" solution.
          if (msg.match(/&check;/)) {
            fullCount++;
          }
        }
        var extrasMessage = '';
        if (status.extras.size()) {
          var asms = status.extras.values().map(function (x) {
              return x.toUnicode();
            }).join(', ');
          extrasMessage = 'Caution: step has extra assumptions: ' + asms;
        }
        if (fullCount == solutions.length) {
          if (extrasMessage) {
            return (extrasMessage + '\n' +
                    'Otherwise the problem appears to be solved.');
          } else {
            return '&check; Problem solved.';
          }
        }
        var multiple = nonempties > 1;
        var results = [];
        if (extrasMessage) {
          // TODO: Consider whether to report this message if there
          //   are no others to report.
          results.push(extrasMessage);
        }
        for (var i = 0; i < messages.length; i++) {
          var msg = messages[i];
          if (msg === '') {
            continue;
          }
          if (multiple) {
            msg = 'Solution = ' + (i + 1) + ':\n' + msg;
          }
          results.push(msg);
        }
        return results.join('\n\n');
      }
    }
  },

  /**
   * Message for one of the status.solutions objects for a step.
   */
  messageForSolution: function(step, sol) {
    var isEmpty = Toy.isEmpty;
    var format = Toy.format;
    if (sol.eqns.length === 0) {
      return '';
    }
    var overages = sol.overages;
    if (!isEmpty(overages)) {
      var overNames = Object.getOwnPropertyNames(overages);
      var has = (overNames.length == 1 ? 'has' : 'have');
      var names = overNames.join(', ');
      return format('{1} {2} multiple possibly contradictory solutions.',
                    names, has);
    }
    // Message for each name, keyed by name, only if message is
    // non-empty.
    var messagesByName = {};
    var byVar = sol.byVar;
    for (var name in byVar) {
      const msg = messageForName(name, byVar[name]);
      if (msg) {
        messagesByName[name] = msg;
      }
    }
    if (Toy.isEmpty(messagesByName)) {
      // No message at all if nothing here resembling a solution.
      return '';
    }
    // Sorted array of "given" variable names.
    var varsList = Object.getOwnPropertyNames(this.givenVars).sort();
    // Array of messages.
    var results = [];
    /* TODO: Figure out if this (currently non-working) coe
     * can be revived, and perhaps revive it.
    if (type === 'tentative') {
      results.push('Tentatively ');
    }
    */
    // Array of problem variable names not solved at all.
    var unsolved = []
    // Count of variables fully solved for.
    var fullySolvedCount = 0;
    for (var i = 0; i < varsList.length; i++) {
      const name = varsList[i];
      const msg = messagesByName[name];
      if (msg) {
        results.push(msg);
        if (msg.match(/Solves for \w*$/)) {
          fullySolvedCount++;
        }
      } else {
        unsolved.push(name);
      }
    }
    if (fullySolvedCount == varsList.length) {
      // The &check; is matched against a regex in progressMessage.
      results.push('&check; A full solution.');
    } else if (unsolved.length) {
      results.push('Needs to solve for ' + unsolved.join(', '));
    }
    return results.join('\n');
  }
};
$.extend(ProofEditor.prototype, methods);

/**
 * Returns a string with message in a solution for the name, possibly
 * empty string.  Here info is the byVar information for the name.
 */
function messageForName(name, info) {
  var format = Toy.format;
  var rhsVars = info.using;
  var msg = '';
  if (name in rhsVars) {
    // Not solved, do not comment.
  } else if (isEmpty(rhsVars)) {
    // The "Solves for \w*" part is matched against a regex
    // in messageForSolution.
    msg = format('Solves for {1}', name);
    var main = info.eqn.getMain();
    var rhs = info.swapped ? main.getLeft() : main.getRight();
    if (!isLowestTerms(rhs)) {
      msg += ', but needs simplification';
    }
    if (info.swapped) {
      msg += format('; {1} should be on the left', name);
    }
  } else {
    msg = format('Solves for {1} in terms of {2}',
                 name, Object.keys(rhsVars).sort().join(', '));
  }
  return msg;
}

}  // namespace;
