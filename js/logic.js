// Copyright 2018 Crispin Perdue.
// All rights reserved.
//
// Definitions and theorems of pure logic

+function() {

var assert = Toy.assertTrue;

//// Import names

const assertEqn = Toy.assertEqn;
const varify = Toy.varify;
const constify = Toy.constify;
const termify = Toy.termify;
const mathParse = Toy.mathParse;
const call = Toy.call;
const equal = Toy.equal;
const implies = Toy.implies;
const lambda = Toy.lambda;

const Expr = Toy.Expr;
const Atom = Toy.Atom;
const Call = Toy.Call;
const Lambda = Toy.Lambda;

const define = Toy.define;
const defineCases = Toy.defineCases;
const definition = Toy.definition;

const identity = Toy.parse('{x. x}');
const allT = Toy.parse('{x. T}');

const rules = Toy.rules;
const addRulesMap = Toy.addRulesMap;

//// Rules needed to support definition

// simpleApply
// applyBoth

//// Definitions

define('not', '(=) F');
define('!=', '{x. {y. not (x = y)}}');
define('forall', '(=) {x. T}');
define('F', 'forall {x. x}');

// define('forall', '(=) {x. T}');
// definition('forall = ((=) {x. T})');
// definition('F = forall {x. x}');

define('exists', '{p. p != {x. F}}');
define('exists1', '{p. exists {x. p = {y. y = x}}}');
defineCases('&', identity, '{x. F}');
defineCases('|', allT, identity);
defineCases('=>', identity, allT);

const axioms = {
  // TODO: LOGIC: Consider the possibility of instead saying that
  //     p T & p F => p x
  //   and defining forall:bool->bool as {p. p T & p F}.
  //   Most uses of axiom1 are immediately followed by instEqn, and
  //   use the definition of forall:bool->bool.
  //   We could prove that any two boolean functions with the same
  //   definition by cases are equal.  This still assumes that
  //   definition by cases is at least admissible.  (There exists
  //   a function as defined.)
  axiom1: {
    statement: 'g T & g F == forall {a. g a}',
    inputs: {},
    form: '',
    description: 'axiom of T & F',
    tooltip: ('T and F are all the booleans')
  },

  axiom2: {
    statement: 'x = y => h x = h y',
    inputs: {},
    form: '',
    description: 'axiom of function application',
    tooltip: ('functions take equal values to equal values')
  },

  /**
   * Axiom 2 specialized for predicates.  This is actually more like
   * Andrews' axiom 2.
   */
  axiom2a: {
    statement: 'x = y => (p x == p y)',
    proof: function() {
      var step1 = rules.instVar(rules.axiom2(), 'p', 'h');
      var step2 = rules.eqIsEquiv();
      var result = rules.replace(step1, '/right/binop', step2);
      return result;
    },
    inputs: {},
    form: '',
    description: 'axiom of predicate application',
    tooltip: ('predicates take equal values to the same truth value')
  },

  axiom3: {
    statement: '(f = g) == forall {x. f x = g x}',
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    inputs: {},
    form: '',
    tooltip: ('extensionality: functions are equal based on equal results'
              + ' on all inputs.'),
    description: 'axiom of equal functions'
  },

  axiom3a: {
    statement: '(p = q) == forall {x. p x == q x}',
    proof: function() {
      const map = {f: 'p', g: 'q'};
      const step1 = rules.instMultiVars(rules.axiom3(), map);
      const step2 = rules.eqIsEquiv();
      const result = rules.replace(step1, '/right/arg/body/binop', step2);
      return result.justify('axiom3a');
    },
    labels: 'higherOrder',
    converse: {labels: 'higherOrder'},
    inputs: {},
    form: '',
    tooltip: ('extensionality: predicates are equal ' +
              'based on equal membership.'),
    description: 'axiom of equal predicates'
  },

  /**
   * Generates an instance of Axiom 4 from an application of a lambda
   * expression to an argument expression, returning a term that
   * expresses the equality of the input and its beta reduction.
   */
  axiom4: {
    action: function(call) {
      call = typeof call == 'string' ? Toy.parse(call) : call;
      assert(call.isLambdaCall(),
             'Axiom 4 needs ({v. B} A), got: {1}', call.toString());
      var lambda = call.fn;
      var result =
        (call.arg.name === lambda.bound.name
         // In this case the substitution will have no effect,
         // though subFree might incidentally rename the bound variable.
         ? equal(call, lambda.body)
         : equal(call, lambda.body.subFree1(call.arg, lambda.bound.name)));
      // Always make sure the call has a type.  It came from elsewhere.
      Toy.findType(call);
      return rules.assert(result).justify('axiom4', [call]);
    },
    labels: 'primitive',
    inputs: {term: 1},  // Specifically a Call to a Lambda.
    form: 'Enter {v. body} expr <input name=term>',
    menu: 'apply a lambda to its argument',
    description: 'axiom of substitution',
    tooltip: ('')
  },

  axiom5: {
    statement: 'iota {x. x = y} = y',
    inputs: {},
    form: '',
    tooltip: ('axiom of description'),
    description: 'axiom of description',
    simplifier: true
  }

};
addRulesMap(axioms);


}();
  
