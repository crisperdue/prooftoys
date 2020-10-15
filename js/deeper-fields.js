// Copyright 2018 Crispin Perdue.
// All rights reserved.

// Incomplete development of some of the facts about fields given in
// numbers.js, starting from weaker premises.  Load this before
// numbers.js to use "weaker" (but equivalent) field axioms that
// require more proofs to get up to the level provided by the default
// field axioms.

// Set all of this up immediately upon load, but avoiding changes
// to the global environment (except through the "Toy" namespace).
+function() {

const rules = Toy.rules;
const addRule = Toy.addRule;
const addRules = Toy.addRules;
const definex = Toy.definex;
const definition = Toy.definition;
const basicSimpFacts = Toy.basicSimpFacts;

const assert = Toy.assertTrue;
const memo = Toy.memo;

//  Make some useful names available here.
const assertEqn = Toy.assertEqn;
const err = Toy.err;
const varify = Toy.varify;
const constify = Toy.constify;
const termify = Toy.termify;
const call = Toy.call;
const equal = Toy.equal;
const implies = Toy.implies;
const lambda = Toy.lambda;

const Expr = Toy.Expr;
const Call = Toy.Call;
const Lambda = Toy.lambda;

//// Field laws

// Indicate that the "deeper" axioms are in use.
Toy.deeperFieldAxioms = true;

const strictness =
  [
   {statement: '@not (R none)', axiom: true,
    description: 'null value is not Real'},
   {statement: '@strict2 (+)', axiom: true,
    description: 'real addition is strict'},
   {statement: '@strict2 (*)', axiom: true,
    description: 'real multiplication is strict'}
   ];
addRules(strictness);

definition('isAddIdentity = {x. R x & forall {y. R y => y + x = y}}');
definition('isMulIdentity = {x. R x & forall {y. R y => y * x = y}}');

const fieldLaws1 =
  [
   {statement: 'R (x + y)', axiom: true,
    description: 'real addition is closed'
   },
   {statement: '(x + y) + z = x + (y + z)', axiom: true,
    description: 'associativity of addition',
    labels: 'algebra',
    converse: { labels: 'algebra2' }
   },
   {statement: 'x + y = y + x', axiom: true,
    description: 'commutativity of addition',
    labels: 'algebra',
    noSwap: true
   },
   {statement: 'exists isAddIdentity', axiom: true,
    description: 'additive identity exists'
   },
   {statement: 'R (x * y)', axiom: true,
    description: 'real multiplication is closed'
   },
   {statement: '(x * y) * z = x * (y * z)', axiom: true,
    description: 'associativity of multiplication',
    labels: 'algebra',
    converse: { labels: 'algebra2' }
   },
   {statement: 'x * y = y * x', axiom: true,
    description: 'commutativity of multiplication',
    labels: 'algebra',
    noSwap: true
   },
   {statement: 'exists isMulIdentity', axiom: true,
    description: 'multiplicative identity exists'
   },
   {statement: 'x * (y + z) = x * y + x * z', axiom: true,
    description: 'distributive law',
    labels: 'algebra',
    converse: { labels: 'algebra' }
   }
   ];
addRules(fieldLaws1);

const identityFacts =
  [
   {statement: 'isAddIdentity x & isAddIdentity y => x = y',
    name: 'uniqueAddIdentity',
    proof: function() {
       const factX1 = (rules.assume('isAddIdentity x')
                       .andThen('apply', '/right'));
       const xType = factX1.andThen('forwardChain', 'a => b & c => (a => b)');
       const factX = (factX1.andThen('forwardChain',
                                      'a => b & c => (a => c)')
                      .andThen('instForall', '/rt', 'y')
                      .andThen('asAssumption', '(R y)'));
       const factY = (factX.andThen('instMultiVars', {x: 'y', y: 'x'})
                      .andThen('rewrite', '/rt/left', 'x + y = y + x'));
       const yType = xType.andThen('instMultiVars', {x: 'y'});
       const result = (rules.replace(factY, '/rt/left', factX)
                       .andThen('trueBy1', '(R x)', xType)
                       .andThen('trueBy1', '(R y)', yType)
                       .andThen('eqnSwap'));
       return result;
     }
   },
   {statement: 'isMulIdentity x & isMulIdentity y => x = y',
    name: 'uniqueMulIdentity',
    proof: function() {
       const factX1 = (rules.assume('isMulIdentity x')
                       .andThen('apply', '/right'));
       const xType = factX1.andThen('forwardChain', 'a => b & c => (a => b)');
       const factX = (factX1.andThen('forwardChain',
                                      'a => b & c => (a => c)')
                      .andThen('instForall', '/rt', 'y')
                      .andThen('asAssumption', '(R y)'));
       const factY = (factX.andThen('instMultiVars', {x: 'y', y: 'x'})
                      .andThen('rewrite', '/rt/left', 'x * y = y * x'));
       const yType = xType.andThen('instMultiVars', {x: 'y'});
       const result = (rules.replace(factY, '/rt/left', factX)
                       .andThen('trueBy1', '(R x)', xType)
                       .andThen('trueBy1', '(R y)', yType)
                       .andThen('eqnSwap'));
       return result;
     }
   },
   {statement: 'exists1 isAddIdentity',
    proof: function() {
       const notMulti = (rules.fact('uniqueAddIdentity')
                         .andThen('toForall0', 'y')
                         .andThen('toForall0', 'x')
                         .andThen('rewriteOnly', '', rules.notMulti().swap()));
       return (rules.fact('exists isAddIdentity')
               .andThen('and', notMulti)
               .andThen('rewrite', '', rules.exists1a().swap()));
                               
     }
   },
   {statement: 'exists1 isMulIdentity ',
    proof: function() {
       const notMulti = (rules.fact('uniqueMulIdentity')
                         .andThen('toForall0', 'y')
                         .andThen('toForall0', 'x')
                         .andThen('rewriteOnly', '', rules.notMulti().swap()));
       return (rules.fact('exists isMulIdentity')
               .andThen('and', notMulti)
               .andThen('rewrite', '', rules.exists1a().swap()));
                               
     }
   }
   ];
addRules(identityFacts);

definition('0 = the1 isAddIdentity');
definition('1 = the1 isMulIdentity');

const inverseFacts =
  [
   {statement: 'exists {y. R y & x + y = 0}', axiom: true,
    description: 'additive inverses exist'
   },
   {statement: 'x != 0 => exists {y. R y & x * y = 1}', axiom: true,
    description: 'multiplicative inverses exist'
   },
   {statement: 'x + y = 0 & x + z = 0 => y = z',
    name: 'no2AddInverses',
    proof: function() {
       const a1 = rules.assume('x + y = 0');
       const a2 = rules.assume('x + z = 0');
       return (rules.consider('x + y + z')
               .andThen('rewriteFrom', '/right/left', a1)
               .andThen('simplifySite', '/right')
               .andThen('rewrite', '/main/left/left', 'x + y = y + x')
               .andThen('rewrite', 'y + x + z',
                        'y + x + z = y + (x + z)')
               .andThen('rewriteFrom', 'x + z', a2)
               .andThen('simplifySite', '/right'));
                        
     }
   },
   {statement: 'x * y = 1 & x * z = 1 => y = z',
    name: 'no2MulInverses',
    proof: function() {
       const a1 = rules.assume('x * y = 1');
       const a2 = rules.assume('x * z = 1');
       return (rules.consider('x * y * z')
               .andThen('rewriteFrom', '/right/left', a1)
               .andThen('simplifySite', '/right')
               .andThen('rewrite', '/main/left/left', 'x * y = y * x')
               .andThen('rewrite', 'y * x * z',
                        'y * x * z = y * (x * z)')
               .andThen('rewriteFrom', 'x * z', a2)
               .andThen('simplifySite', '/right'));
                        
     }
   }

   // TODO: Prove the actual unique existence properties (easy from
   // here).

   ];
addRules(inverseFacts);

}();
