// Copyright Crispin Perdue.  All rights reserved.

// Set all of this up immediately upon load, but avoiding changes
// to the global environment (except through the "Toy" namespace).
(function() {

'use strict';

//// THEOREMS AND RULES

var rules = Toy.rules;
var declare = Toy.declare;
var definex = Toy.definex;
const definition = Toy.definition;
var basicSimpFacts = Toy.basicSimpFacts;

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

var Path = Toy.Path;
var Expr = Toy.Expr;
var Call = Toy.Call;
var Lambda = Toy.lambda;

// Predefine some common constants.
var T = constify('T');
var F = constify('F');

var convert = Toy.convert;
var applyToFocalPart = Toy.applyToFocalPart;
var noSimplify = Toy.noSimplify;


//// Field laws

if (!Toy.deeperFieldAxioms) {

  declare
  (
     {statement: '@not (R none)', axiom: true,
      description: 'null value is not Real'},
     {statement: '@ strict2 (+)', axiom: true,
      description: 'real addition is strict'},
     {statement: '@ strict2 (*)', axiom: true,
      description: 'real multiplication is strict'}
  );

  definition('isAddIdentity = {x. R x & forall {y. R y => y + x = y}}');
  definition('isMulIdentity = {x. R x & forall {y. R y => y * x = y}}');

  declare
  (
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
     // TODO: Prove uniqueness from just existence.  Sketch is that if
     //   m and n are identities, then m + n = m and n + m = n.  By
     //   commutativity, m = n.  For non-commutative groups, the
     //   identity must be two-sided ("commutative"), so the proof
     //   still goes through.
     {statement: 'exists1 isAddIdentity', axiom: true,
      description: 'unique additive identity exists'
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
     {statement: 'exists1 isMulIdentity', axiom: true,
      description: 'unique multiplicative identity exists'
     },
     {statement: 'x * (y + z) = x * y + x * z', axiom: true,
      description: 'distributive law',
      labels: 'algebra',
      converse: { labels: 'algebra' }
     }
  );

  definition('0 = the1 isAddIdentity');
  definition('1 = the1 isMulIdentity');

  // These return a collection of inverses of a given value.
  definition('addInverses = [x. {y. R x & R y & x + y = 0}]');
  definition('mulInverses = [x. {y. R x & R y & x * y = 1}]');

  declare(
     {statement: '@ R x => exists1 (addInverses x)', axiom: true,
      description: 'unique additive inverses exist'
     },
     {statement: '@ R x & x != 0 => exists1 (mulInverses x)', axiom: true,
      description: 'unique multiplicative inverses exist'
     }
  );
}

declare(
   // Identity axioms

   // In Lay, this is part of axiom M4.
   {statement: '1 != 0', axiom: true,
    description: '1 and 0 are distinct'},

   // Theorems
   {statement: 'isAddIdentity 0',
    proof: function() {
       return (rules.fact('0 = the1 isAddIdentity')
               .andThen('rewrite', '',
                        'exists1 p => (x = the1 p == p x)')
               .andThen('trueBy0', '/left',
                        rules.fact('exists1 isAddIdentity'))
               .andThen('arrangeAsms'));
     }
   },

   {statement: 'R 0',
    proof: function() {
       return (rules.fact('(isAddIdentity 0)')
               .andThen('apply', '')
               .andThen('forwardChain', 'a & b => a'));
     }
   },

   {statement: 'isMulIdentity 1',
    proof: function() {
       return (rules.fact('1 = the1 isMulIdentity')
               .andThen('rewrite', '',
                        'exists1 p => (x = the1 p == p x)')
               .andThen('trueBy0', '/left',
                        rules.fact('exists1 isMulIdentity'))
               .andThen('simplifySite', ''));
     }
   },

   {statement: 'R 1',
    proof: function() {
       return (rules.fact('(isMulIdentity 1)')
               .andThen('apply', '')
               .andThen('forwardChain', 'a & b => a'));
     }
   },
   
   {statement: 'isAddIdentity x == x = 0',
    // TODO: Notice that using forwardChain here with step1 causes
    //   step1 to be displayed as if it were a recorded fact.  This
    //   issue can also occur with rewrites.  we should probably
    //   choose display style in such cases based on use of a recorded
    //   fact given as a statement versus using a proved step.  This
    //   would also let us eliminate some variants of rewrite rules.
    proof: function() {
       const step1 = (rules.fact('exists1 p => (p x == x = the1 p)')
                      .andThen('instMultiVars', {p: 'isAddIdentity'})
                      .andThen('rewrite', '/right/right/right',
                               'the1 isAddIdentity = 0'));
       return (rules.fact('exists1 isAddIdentity')
               .andThen('forwardChain', step1)
               .andThen('instForall', '', 'x'));
     }
   },
   {statement: 'isMulIdentity x == x = 1',
    proof: function() {
       const step1 = (rules.fact('exists1 p => (p x == x = the1 p)')
                      .andThen('instMultiVars', {p: 'isMulIdentity'})
                      .andThen('rewrite', '/right/right/right',
                               'the1 isMulIdentity = 1'));
       return (rules.fact('exists1 isMulIdentity')
               .andThen('forwardChain', step1)
               .andThen('instForall', '', 'x'));
     }
   }
);

definition('neg = {x. the1 (addInverses x)}');
definition('minv = {x. the1 (mulInverses x)}');

// Note that our axiom of arithmetic computes that neg 1 = -1, which
//   gives ability to prove things we prefer to prove from (other)
//   axioms.

declare(
   {name: 'negFact',
    statement: '@ R x & R y & x + y = 0 == R x & neg x = y',
    // TODO: Replace this proof as shown below.
    proof:
    [
     '(1 fact "exists1 (addInverses x)")',
     '(2 inverseFunLaw_old)',
     '(3 instantiateVar (s 2) (path "/left/left/right/arg/fn") (t addInverses))',
     '(4 instantiateVar (s 3) (path "/left/left/left/fn") (t neg))',
     '(5 fact "@ neg x = the1 (addInverses x)")',
     '(6 trueBy0 (s 4) (path "/left/left") (s 5))',
     '(7 rewrite (s 6) (path "/left") (t ((T & a) == a)))',
     '(8 trueBy1 (s 7) (path "/left") (s 1))',
     '(9 display (s 8))',
     '(10 rewrite (s 9) (path "/right/left") (t ((addInverses x y) = (((R x) & (R y)) & ((x + y) = 0)))))',
     '(11 rewrite (s 10) (path "") (t ((a => (((a & b) & c) == d)) == (((a & b) & c) == (a & d)))))'
     ]
   },

   /* TODO: Replace the proof of negFact with this or very similar:
(55 inverseFunLaw)
(56 instantiateVar (s 55) (path "/left/left/left") (t (neg y)))
(57 instantiateVar (s 56) (path "/left/left/right/arg") (t (addInverses y)))
(58 fact "@neg x = the1 (addInverses x)")
(59 trueBy0 (s 57) (path "/left/left") (s 58))
(60 simplifySite (s 59) "")
(61 fact "@(exists1 (addInverses y))")
(62 trueBy1 (s 59) (path "/left/right") (s 61))
(63 rewrite (s 62) (path "/right/left") (t ((addInverses x y) = (((R x) & (R y)) & ((x + y) = 0)))))
(64 assumed (s 63) (path "/right/left/left/left"))
(65 rewrite (s 64) (path "") (t ((a => (c == d)) == ((c & a) == (a & d)))))
(66 rewrite (s 65) (path "/main/left") (t (((a & b) & c) == ((a & c) & b))))
   */

   {name: 'minvFact',
    statement: '@ x != 0 & R x & R y & x * y = 1 == x != 0 & R x & minv x = y',
    // TODO: Replace this proof as shown above for negFact.
    proof:
    [
     '(1 fact "exists1 (mulInverses x)")',
     '(2 inverseFunLaw_old)',
     '(3 instantiateVar (s 2) (path "/left/left/right/arg/fn") (t mulInverses))',
     '(4 instantiateVar (s 3) (path "/left/left/left/fn") (t minv))',
     '(5 fact "@ minv x = the1 (mulInverses x)")',
     '(6 trueBy0 (s 4) (path "/left/left") (s 5))',
     '(7 rewrite (s 6) (path "/left") (t ((T & a) == a)))',
     '(8 trueBy1 (s 7) (path "/left") (s 1))',
     '(9 display (s 8))',
     '(10 rewrite (s 9) (path "/right/left") (t ((mulInverses x y) = (((R x) & (R y)) & ((x * y) = 1)))))',
     '(11 rewrite (s 10) (path "") (t (((a & b) => (((b & c) & d) == m)) == ((((a & b) & c) & d) == ((a & b) & m)))))'
     ]
   },

   {statement: '@ x != 0 & R x => R (minv x)',
    proof: 
    [
     '(1 minvFact)',
     '(2 forwardChain (s 1) (t (((((a & b) & c) & d) == g) => (g => c))))',
     '(3 assume (t (y = (minv x))))',
     '(4 rewriteFrom (s 2) (path "/right/arg") (s 3))',
     '(5 rewrite (s 4) (path "/left/left/left/right") (t ((x = y) == (y = x))))',
     '(6 removeLet (s 5) (path "/left/left/right"))'
     ]
   },

   {statement: '@ x != 0 & R x => x * minv x = 1',
    proof:
    [
     '(1 minvFact)',
     '(2 forwardChain (s 1) (t (((((a & b) & c) & d) == g) => (g => d))))',
     '(3 rewrite (s 2) (path "/left/right") (t ((x = y) == (y = x))))',
     '(4 assume (t (y = (minv x))))',
     '(5 display (s 3))',
     '(6 rewriteFrom (s 5) (path "/right/left/right") (s 4))',
     '(7 display (s 6))',
     '(8 removeLet (s 7) (path "/left/left/right"))'
     ]
   },

   {statement: 'minv 0 = none',
    proof:
    [
     '(1 definition "mulInverses" "")',
     '(2 applyBoth (s 1) (t 0))',
     '(3 apply (s 2) (path "/main/right"))',
     '(4 fact "0 != 1")',
     '(5 fact "0=0*x")',
     '(6 rewriteFrom (s 4) (path "/main/left") (s 5))',
     '(7 rewrite (s 6) (path "/right") (t ((a != b) == (not (a = b)))))',
     '(8 rewrite (s 7) (path "") (t ((a => (not b)) == ((a & b) == F))))',
     '(9 rewrite (s 3) (path "/main/right/body") (t (((a & b) & c) == (a & (b & c)))))',
     '(10 rewriteFrom (s 9) (path "/main/right/body/right") (s 8))',
     '(11 simplifySite (s 10) (path "/main/right/body"))',
     '(12 rewrite (s 11) (path "/main/right") (t ({x. F} = empty)))',
     '(13 applyToBoth (t the1) (s 12))',
     '(14 rewrite (s 13) (path "/main/left") (t ((the1 (mulInverses x)) = (minv x))))',
     '(15 rewrite (s 14) (path "/main/right") (t ((the1 empty) = none)))'
     ]
   }
);

definition('(-) = {x. {y. x + neg y}}');


//// Facts about fields

// TODO: Rename "/" to something like realDiv, and define "/"
//   conditionally for the real numbers, with values for non-real,
//   non-null inputs not defined.
// TODO: That will require an implementation of "conditional"
//   definitions that only specify the value of their "constant"
//   under certain conditions, such as the arguments having values
//   among the real numbers.
//
//   This definition then can serve as a witness that there exist
//   functions satisfying the conditional definition.

// TODO: Replace these two definitions, with recip based on
//   facts about fields and "/" based on recip.
definition('(/) = {x. {y. the1 {z. R x & R y & R z & x = y * z}}}');
definition('recip = {x. 1 / x}');

/**
 * We desire something like this, but it needs some supporting
 * theorems such as probably 5307.
 *
 * definex('quotient',
 * 'exists {q. strict2 q & (R x & R y => q x y = x / y');
 */


declare(
   {statement: 'not (x < x)', axiom: true,
    description: 'strict ordering axiom 1'
   },
   {statement: 'x < y => not (y < x)', axiom: true,
    description: 'strict ordering axiom 2'
   },
   {statement: 'x < y | y < x | x = y', axiom: true,
    description: 'strict ordering axiom 3'
   },
   {statement: 'x < y & y < z => x < z', axiom: true,
    description: 'strict ordering transitivity'
   },

   // Completeness:
   //
   // infix (x is_ub S)
   // define is_ub = [x ∈ ℝ, S ⊆ ℝ. ∀ y ∈ S. y ≤ x]
   // ∀ S ⊆ ℝ. (∃ z ∈ ℝ. z is_ub S) ⇒
   //          (∃ x ∈ ℝ. x is_ub S ∧ ∀ y ∈ ℝ. y is_ub S ⇒ x ≤ y)

   {statement: 'x < y => x + z < y + z', axiom: true,
    description: 'ordering of reals and addition'
   },
   // Steven Lay, Axiom O4.
   // Also like Wikibooks Real Analysis axiom.
   {statement: 'x < y & 0 < z => x * z < y * z', axiom: true,
    description: 'ordering of reals and multiplication'
   }
   // Similar to Wikipedia: "Real number"
   //
   // {statement: '0 < x & 0 < y => 0 < x * y', axiom: true,
   //  description: 'ordering of reals and multiplication'
   // }
);

declare(
   {statement: 'x = y => not (x < y)',
    proof: function() {
       const asm = rules.assume('x = y');
       return (rules.fact('not (x < x)')
               // OK to use replace here.  It merges assumptions.
               .andThen('replace', '/main/arg/right', asm));
     }
   },

   {statement: '@R x & x < y => x != y',
    proof: function() {
       return (rules.fact('x = y => not (x < y)')
               .andThen('extractHyp', 'x = y')
               .andThen('rewrite', '/main', 'a => not b == b => not a')
               .andThen('rewrite', 'not (x = y)', 'not (x = y) == x != y')
               .andThen('rewrite', '', 'a => (b => c) == a & b => c'));
     }
   }

);

// Lay 11.1
declare(
     // Lay 11.1a
     {name: 'abcPlus',
      statement: '@x + z = y + z & R x & R y & R z => x = y',
      proof:
      [
       '(1 assume (t ((x + z) = (y + z))))',
       '(2 applyToBoth (t {w. (w + (neg z))}) (s 1))',
       '(3 rewrite (s 2) (path "/right/left") (t ((((R x) & (R y)) & (R z)) => (((x + y) + z) = (x + (y + z))))))',
       '(4 rewrite (s 3) (path "/right/left/right") (t ((R x) => ((x + (neg x)) = 0))))',
       '(5 rewrite (s 4) (path "/right/left") (t ((R x) => ((x + 0) = x))))',
       '(6 rewrite (s 5) (path "/right/right") (t ((((R x) & (R y)) & (R z)) => (((x + y) + z) = (x + (y + z))))))',
       '(7 rewrite (s 6) (path "/right/right/right") (t ((R x) => ((x + (neg x)) = 0))))',
       '(8 rewrite (s 7) (path "/right/right") (t ((R x) => ((x + 0) = x))))'
       ]
     },

     // Lay 11.1b
     {statement: 'x * 0 = 0',
      simplifier: true,
      proof:
      [
       '(1 consider (t (x * 0)))',
       '(2 rewrite (s 1) (path "/main/right/right") (t (x = (x + 0))))',
       '(3 rewrite (s 2) (path "/main/right") (t ((((R x) & (R y)) & (R z)) => ((x * (y + z)) = ((x * y) + (x * z))))))',
       '(4 display (s 3))',
       '(5 rewrite (s 4) (path "/right/left") (t (x = (0 + x))))',
       '(6 abcPlus)',
       '(7 instantiateVar (s 6) (path "/left/left/left/left/left/left") (t 0))',
       '(8 instantiateVar (s 7) (path "/left/left/left/left/left/right") (t (x * 0)))',
       '(9 instantiateVar (s 8) (path "/left/left/left/left/right/left") (t (x * 0)))',
       // TODO: avoid dependence on order of assumptions.
       '(10 extractHypAt (s 9) (path "/left/left/left/left"))',
       '(11 simplifyAsms (s 10))',
       '(12 p2 (s 5) (s 11) (t (((a => b) & (a => (b => c))) => (a => c))))',
       '(13 rewrite (s 12) (path "/right") (t ((x = y) == (y = x))))'
       ],
      description: 'multiplication by zero'
     },

     // Lay 11.1c
     {statement: '(neg 1) * x = neg x',
      simplifier: true,
      proof:
      ['(1 consider (t (x + ((neg 1) * x))))',
       '(2 rewrite (s 1) (path "/main/right/right") (t (((R x) & (R y)) => ((x * y) = (y * x)))))',
       '(3 rewrite (s 2) (path "/right/right/left") (t (x = (x * 1))))',
       '(4 rewrite (s 3) (path "/right/right") (t ((((R x) & (R y)) & (R z)) => (((x * y) + (x * z)) = (x * (y + z))))))',
       '(5 rewrite (s 4) (path "/right/right/right") (t ((x + (neg x)) = 0)))',
       '(6 simplifyFocalPart (s 5))',
       '(7 display (s 6))',
       '(8 negFact)',
       '(9 rewrite (s 8) (path "/main") (t ((((a & b) & c) == (a & d)) == (a => ((b & c) == d)))))',
       '(10 assumeExplicitly (t (R ((neg 1) * x))))',
       '(11 simplifyAsms (s 10))',
       '(12 rewrite (s 7) (path "/right") (t (a == (T & a))))',
       '(13 replaceT (s 12) (path "/right/left") (s 11))',
       '(14 display (s 13))',
       '(15 rewriteFrom (s 14) (path "/right") (s 9))',
       '(16 rewrite (s 15) (path "/right") (t ((x = y) == (y = x))))'
       ]
     },
     // This uses the arithmetic fact that -1 is neg 1.  In principle
     // -1 is just an abbreviation for (neg 1), so it would not be
     // appropriate to define neg x = -1 * x, as "neg" appears in the
     // RHS of the definition.
     {statement: '-1 * x = neg x',
      proof: function() {
         return (rules.fact('(neg 1) * x = neg x')
                 .andThen('rewrite', '/main/left/left', 'neg 1 = -1'));
       }
     },

     // Lay 11.1d
     {statement: '@ R x & R y => (x * y = 0 == x = 0 | y = 0)',
      name: 'zeroProduct',
      proof:
      [
       '(1 fact "0=x*0")',
       '(2 instantiateVar (s 1) (path "/right/right/left") (t (minv x)))',
       '(3 fact "x!=0=>R(minv x)")',
       '(4 trueBy1 (s 2) (path "/left") (s 3))',
       '(5 assume (t (0 = (x * y))))',
       '(6 rewriteFrom (s 4) (path "/right/right/right") (s 5))',
       '(7 rewrite (s 6) (path "/right/right") (t ((((R x) & (R y)) & (R z)) => ((x * (y * z)) = ((x * y) * z)))))',
       '(8 rewrite (s 7) (path "/right/right/left") (t (((R x) & (R y)) => ((x * y) = (y * x)))))',
       '(9 rewrite (s 8) (path "/right/right/left") (t (((x != 0) & (R x)) => ((x * (minv x)) = 1))))',
       '(10 rewrite (s 9) (path "/right/right") (t ((R a) => ((1 * a) = a))))',
       '(11 display (s 10))',
       '(12 trueBy1 (s 11) (path "/left/left/left/right") (s 3))',
       '(13 rewrite (s 12) (path "/left/left/left/left") (t ((x != y) == (not (x = y)))))',
       // TODO: Disallow selection of asms by their location.
       '(14 rewrite (s 13) (path "") (t (((((p & (not q)) & a) & b) => r) == (((p & a) & b) => (q | r)))))',
       '(15 rewrite (s 14) (path "/left/left/left") (t ((x = y) == (y = x))))',
       '(16 assume (t (x = 0)))',
       '(17 rewrite (s 16) (path "/right") (t ((x = y) == (y = x))))',
       '(18 fact "0*y=0")',
       '(19 rewriteFrom (s 18) (path "/right/left/left") (s 17))',
       '(20 assume (t (y = 0)))',
       '(21 rewrite (s 20) (path "/right") (t ((x = y) == (y = x))))',
       '(22 fact "x*0=0")',
       '(23 rewriteFrom (s 22) (path "/right/left/right") (s 21))',
       '(24 extractHyp (s 19) (t (x = 0)))',
       '(25 extractHyp (s 23) (t (y = 0)))',
       '(26 p2 (s 24) (s 25) (t (((a => (p => r)) & (b => (q => r))) => ((a & b) => ((p | q) => r)))))',
       '(27 extractHyp (s 15) (t (x * y = 0)))',
       '(28 rewrite (s 27) (path "/right/right/right") (t ((x = y) == (y = x))))',
       '(29 rewrite (s 26) (path "/left") (t ((a & b) == (b & a))))',
       '(30 p2 (s 28) (s 29) (t (((a => (p => q)) & (a => (q => p))) => (a => (q == p)))))',
       '(31 rewrite (s 30) (path "/right") (t ((a == b) == (b == a))))',
       '(32 display (s 31))'
       ]
     },

     // Lay 11.1e
     {statement: '@ R x & R y => (x < y == neg y < neg x)',
      proof:
      [
       '(1 fact "x<y=>x+z<y+z")',
       '(2 instantiateVar (s 1) (path "/right/left/right") (t ((neg x) + (neg y))))',
       '(3 rewrite (s 2) (path "/right/left") (t ((((R x) & (R y)) & (R z)) => ((x + (y + z)) = ((x + y) + z)))))',
       '(4 rewrite (s 3) (path "/right/right/right") (t (((R x) & (R y)) => ((x + y) = (y + x)))))',
       '(5 rewrite (s 4) (path "/right/right") (t ((((R x) & (R y)) & (R z)) => ((x + (y + z)) = ((x + y) + z)))))',
       '(6 rewrite (s 5) (path "/right/left/left") (t ((R x) => ((x + (neg x)) = 0))))',
       '(7 rewrite (s 6) (path "/right/right/left") (t ((R x) => ((x + (neg x)) = 0))))',
       '(8 rewrite (s 7) (path "/right/right") (t ((R a) => ((0 + a) = a))))',
       '(9 rewrite (s 8) (path "/right/left") (t ((R a) => ((0 + a) = a))))',
       '(10 display (s 9))',
       '(11 tautology (t (((a & b) & c) == ((b & c) & a))))',
       '(12 rewriteOnlyFrom (s 10) (path "/left") (s 11))',
       '(13 instantiateVar (s 12) (path "/left/right/left") (t (neg x)))',
       '(14 instantiateVar (s 13) (path "/left/right/right") (t (neg y)))',
       '(15 rewrite (s 14) (path "/right/left") (t ((R a) => ((neg (neg a)) = a))))',
       '(16 rewrite (s 15) (path "/right/right") (t ((R a) => ((neg (neg a)) = a))))',
       '(17 display (s 16))',
       '(18 extractHypAt (s 17) (path "/left/left/left"))',
       '(19 extractHypAt (s 12) (path "/left/right"))',
       '(20 instantiateVar (s 18) (path "/right/left/left/arg") (t z))',
       '(21 instantiateVar (s 20) (path "/right/left/right/arg") (t x))',
       '(22 instantiateVar (s 21) (path "/right/left/left/arg") (t y))',
       '(23 rewrite (s 22) (path "/left") (t ((a & b) == (b & a))))',
       '(24 p2 (s 19) (s 23) (t (((a => (p => q)) & (a => (q => p))) => (a => (p == q)))))'
       ]
     },

     {statement: '@ neg 0 = 0',
      simplifier: true,
      proof:
      [
       '(1 fact "x + neg x = 0")',
       '(2 instantiateVar (s 1) (path "/right/left/left") (t 0))',
       '(3 rewrite (s 2) (path "/right/left") (t ((R a) => ((0 + a) = a))))'
       ]
     },

     {statement: '@ R x => (x < 0 == 0 < neg x)',
      proof:
      [
       '(1 fact "x<y==neg y < neg x")',
       '(2 instantiateVar (s 1) (path "/right/left/right") (t 0))',
       '(3 rewrite (s 2) (path "/right/right/left") (t ((neg 0) = 0)))'
       ]
     },

     {statement: '@ R x => (0 < x == neg x < 0)',
      proof:
      [
       '(1 fact "x<y==neg y < neg x")',
       '(2 instantiateVar (s 1) (path "/right/left/left") (t 0))',
       '(3 rewrite (s 2) (path "/right/right/right") (t ((neg 0) = 0)))',
       '(4 instantiateVar (s 3) (path "/right/right/left/arg") (t x))'
       ]
     },

     // Lay 11.1f
     {statement: '@ R x & R y & R z => (x < y & z < 0 => y * z < x * z)',
      proof:
      [
       '(1 fact "x < y & 0 < z => x * z < y * z")',
       '(2 instantiateVar (s 1) (path "/right/left/right") (t (neg z)))',
       '(3 rewrite (s 2) (path "/left/left/left/left/right") (t ((R x) => ((0 < (neg x)) == (x < 0)))))',
       '(4 rewrite (s 3) (path "/right/left/right") (t ((R x) => ((neg x) = (-1 * x)))))',
       '(5 rewrite (s 4) (path "/right/right/right") (t ((R x) => ((neg x) = (-1 * x)))))',
       '(6 rewrite (s 5) (path "/right/right") (t ((((R x) & (R y)) & (R z)) => ((x * (y * z)) = ((x * y) * z)))))',
       '(7 rewrite (s 6) (path "/right/right/left") (t (((R x) & (R y)) => ((x * y) = (y * x)))))',
       '(8 rewrite (s 7) (path "/right/right") (t ((((R x) & (R y)) & (R z)) => (((x * y) * z) = (x * (y * z))))))',
       '(9 rewrite (s 8) (path "/right/left") (t ((((R x) & (R y)) & (R z)) => ((x * (y * z)) = ((x * y) * z)))))',
       '(10 rewrite (s 9) (path "/right/left/left") (t (((R x) & (R y)) => ((x * y) = (y * x)))))',
       '(11 rewrite (s 10) (path "/right/left") (t ((((R x) & (R y)) & (R z)) => (((x * y) * z) = (x * (y * z))))))',
       '(12 rewrite (s 11) (path "/right/right") (t ((R x) => ((-1 * x) = (neg x)))))',
       '(13 rewrite (s 12) (path "/right/left") (t ((R x) => ((-1 * x) = (neg x)))))',
       '(14 rewrite (s 13) (path "/right") (t (((R x) & (R y)) => (((neg y) < (neg x)) == (x < y)))))',
       '(15 display (s 14))',
       '(16 tautology (t (((((a & b) & c) & d) => p) == (((b & c) & d) => (a => p)))))',
       '(17 rewriteOnlyFrom (s 15) (path "") (s 16))'
       ]
     }
);

declare(
  // Fake axioms.
   {statement: 'x != 0 => x * recip x = 1', axiom: true,
    simplifier: true,
    description: 'reciprocal'
   },
   {name: 'axiomReciprocal2',
    // TODO: Eliminate the two uses of this (both by name).
    statement: '@R (recip x) & recip x != 0 == R x & x != 0',
    description: 'reciprocals are nonzero'
   }
);


////
//// Inference rules
////

//
// Real numbers
// 

declare
  (
   {name: 'plusZero',
    statement: '@R x => x + 0 = x',
    simplifier: true,
    tooltip: 'x + 0 = x',
    description: 'additive identity',
    proof: function() {
      return (rules.fact('isAddIdentity 0')
              .andThen('apply', '')
              .andThen('simplifySite', '')
              .andThen('instForall', '', 'x'));
    }
   },

  {name: 'timesOne',
    statement: '@R x => x * 1 = x',
    simplifier: true,
    tooltip: 'x * 1 = x',
    description: 'multiplicative identity',
    proof: function() {
      return (rules.fact('isMulIdentity 1')
              .andThen('apply', '')
              .andThen('simplifySite', '')
              .andThen('instForall', '', 'x'));
    }
  },

  // TODO: Prove this.
  {name: 'uniqueQuotient',
    // This is provable:
    // If y = 0 and x = 0, z can be any real number.
    // If y = 0 and x != 0 there is no solution.
    // All others are OK.
    statement: 'y != 0 => exists1 {z. R x & R y & R z & x = y * z}',
    description: 'quotient is unique'
  },

  // This implies that 0 ** 0 = 1.  It is also legitimate to define
  // that 0 ** 0 is undefined.
  // TODO: Eventually prove these laws of powers as theorems.
  {name: 'axiomPower0',
    statement: '@R x => x ** 0 = 1',
    simplifier: true,
    description: 'real number to the zeroth power is 1'
  },

  // TODO: Eventually prove these laws of powers as theorems.
  {name: 'axiomNextPower',
   statement: '@R x & R y => x ** (y + 1) = (x ** y) * x', axiom: true,
   description: 'real number to the next power'
  },

  {statement: 'x ** y = x ** (y - 1) * x',
   name: 'prevPower',
   proof: function() {
     return (rules.axiomNextPower()
             .andThen('instVar', 'y - 1', 'y')
             .andThen('simplifyAsms')
             .andThen('simplifySite', 'y - 1 + 1')
            );
   }
  },

  // TODO: Prove this from x * y = 0 etc by deMorgan's Law.
  {name: 'factNonzeroProduct',
    statement: '@R x & R y => (x * y != 0 == x != 0 & y != 0)',
    simplifier: true  // Good mainly for simplifying assumptions.
  },

  // Closure properties

  {name: 'realNegClosed',
    statement: '@ R x => R (neg x)',
    simplifier: true,
    proof:
    [
     '(1 negFact)',
     '(2 forwardChain (s 1) (t ((a == b) => (b => a))))',
     '(3 instantiateVar (s 2) (path "/left/right/right") (t (neg x)))',
     '(4 rewrite (s 3) (path "/left/right") (t ((x = x) == T)))',
     '(5 fact "x+neg x = 0")',
     '(6 trueBy1 (s 4) (path "/right/right") (s 5))',
     '(7 assume (t (R x)))',
     '(8 trueBy1 (s 6) (path "/right/left/left") (s 7))',
     '(9 rewrite (s 8) (path "/right") (t (((T & a) & T) == a)))'
     ]
  },

  {name: 'realSubClosed',
    statement: '@R x & R y => R (x - y)',
    simplifier: true,
    proof: function() {
      return (rules.fact('R (x + y)')
              .andThen('instMultiVars', {y: 'neg y'})
              .andThen('rewrite', '/right/arg', '@ x + neg y = x - y'));
    }
  },

  {name: 'realDivClosed',
    statement: 'y != 0 => R (x / y)',
    simplifier: true,
    // TODO: Prove this.  We need to:
    // Prove that y != 0 => exists1 {z. x = y * z}
    // for real numbers, using full field axioms including
    // ordering laws.
  },

   {name: 'realDivNonzero',
    statement: '@R x & x !=0 => x / y != 0',
    // TODO: Prove this.
   },

  {name: 'realRecipClosed',
    statement: '@ x != 0 & R x => R (recip x)',
    simplifier: true,
    proof: function() {
      var step1 =  (rules.realDivClosed()
                    .andThen('instMultiVars', {x: '1', y: 'x'}));
      return (step1.andThen('rewrite', step1.find('1 / x'),
                            '@ 1 / x = recip x'));
    }
  },

  {name: 'divByZero',
    statement: '@R x => x / 0 = none',
    simplifier: true,
    // We know that:
    // 0 = 0 * 0, and
    // 0 = 0 * 1, two different values for z in the definition of "/".
    // So 0 / 0 = none
    //
    // R x => 0 = 0 * x
    // R x & y != 0 => x * 0 != y
    // So R x & y != 0 => x / y = none
    // 
    // So finally R x & y = 0 => x / y = none
  },

  // End of interim axioms.

  // Evaluates arithmetic expressions with operators: +, -, *, /, div,
  // mod, neg, =, !=, >, >=, <, <=, and the type operator "R".  Checks
  // that inputs are all numeric (exact integers by construction) and
  // that the result can be guaranteed to be a boolean or an exact
  // integer.
  //
  // Prefer rules.arithmetic to this in client code.
  //
  // Result is always an equation (or biconditional) with the given
  // term as the LHS, and the boolean or integer result as the RHS.
  // Returns null if the result is not boolean or an integer.
  //
  // TODO: Move handling of inequalities from here to rules.arithmetic
  // except "<", so others can be defined in terms of it; and division
  // by zero there also, to return "none".
  {name: 'axiomArithmetic',
    // This precheck does not guarantee success if it passes.
    precheck: function(term_arg) {
      var term = termify(term_arg);
      return Toy.isArithmetic(term);
    },
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
          if (right === 0) {
            return null;
          }
          value = left / right;
          // abs(value) <= abs(left) since abs(right) >= 1 so the
          // magnitude is not a problem.  The fractional part of a
          // result must have denominator no greater than MAX_INT,
          // so it should be distinguishable from an integer.
          if (value !== Math.floor(value)) {
            return null;
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
        // A programming error has occurred.
          err('Not an arithmetic expression: ' + term);
        }
        return rules.assert(Toy.infixCall(term, '=', rhs))
          .justify('axiomArithmetic', arguments);
      } else {
        // A programming error has occurred.
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

  //
  // Inference rules for real numbers
  //

  // Rewrites a simple arithmetic expression to its value.
  // Handles !=.
  // TODO: Handle other inequalities here also, except "<",
  //   in terms of "<".
  {name: 'arithmetic',
    action: function(step, path) {
      var term = step.get(path);
      var result;
      if (term.isCall2('!=') &&
          term.getLeft().isNumeral() &&
          term.getRight().isNumeral()) {
        const step1 = rules.apply(step, path);
        result = rules.simplifySite(step1, path);
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
    tooltip: 'arithmetic',
    labels: 'algebra'
  }
  );


// definition('isQuotient = {x. {y. {z. R x & R y & R z & x = y * z}}}');

declare
  (  
  // Division is an inverse of multiplication.
  {name: 'divisionIsInverse',
   statement: '@y != 0 & R x & R y => (R z & x = y * z == z = x / y)',
   // TODO: Consider using inverseFunLaw in the proof, especially once
   //   rewrites work with non-equational facts.
   proof: function() {
      var step1 = rules.uniqueQuotient();
      var step2 = (rules.exists1Law()
                   .andThen('instMultiVars', {x: 'z'}));
      var path = step2.find('p z');
      // TODO: Extend Expr.matchSchema to handle this.  (Rules.p2 uses
      //   matchSchema.
      var step3 = rules.instVar(step2, '{z. R x & R y & R z & x = y * z}', 'p');
      var step4 = rules.p2(step1, step3, '(a => b) & (b => c) => (a => c)');
      var step6 = rules.reduce(step4, path);
      var fml = '@ the1 {z. R x & R y & R z & x = y * z} = x / y';
      var divDefn = rules.fact(fml);
      var step7 = rules.rewriteFrom(step6, '/right/right/right', divDefn);
      var loc7 = Toy.path('/right').concat(step7.getRight().find('(R x)'));
      var step8 = rules.assumed(step7, loc7);
      var loc8 = Toy.path('/right').concat(step8.getRight().find('(R y)'));
      var step9 = rules.assumed(step8, loc8);
      var step10 = rules.simplifySite(step9, '/main/left');
      return step10;
    }
  }
  );

declare
  (
  // Add the given term to the equation in the step at the given path,
  // typically /right/right.
   {name: 'addToBoth',
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

   {name: 'subtractFromBoth',
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

   {name: 'multiplyBoth',
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

   {name: 'divideBoth',
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
   {name: 'addThisToBoth',
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
    menu: ' algebra: add {term} to both sides',
    description: 'add {site};; {in step siteStep}',
    labels: 'algebra'
  },

   {name: 'subtractThisFromBoth',
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
    menu: ' algebra: subtract {term} from both sides',
    description: 'subtract {site};; {in step siteStep}',
    labels: 'algebra'
  },

   {name: 'multiplyBothByThis',
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
    menu: ' algebra: multiply both sides by {term}',
    description: 'multiply by {site};; {in step siteStep}',
    labels: 'algebra'
  },

   {name: 'divideBothByThis',
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
    menu: ' algebra: divide both sides by {term}',
    description: 'divide by {site};; {in step siteStep}',
    labels: 'algebra'
  },

   {name: 'addEquationToThis',
    action: function(eqn1, eqn2) {
      var lhs = eqn2.getMain().getLeft();
      var step1 = rules.applyToBothWith(eqn1, '+', lhs);
      var step3 = rules.rewriteFrom(step1, '/main/right/right', eqn2);
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

   {name: 'subtractEquationFromThis',
    action: function(eqn1, eqn2) {
      var lhs = eqn2.getMain().getLeft();
      var step1 = rules.applyToBothWith(eqn1, '-', lhs);
      var step3 = rules.rewriteFrom(step1, '/main/right/right', eqn2);
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

  );

//// Fact lists

// This list may be added onto later.
Toy.asmSimplifiers.push
  (
   'R 0',  // Include R 0 and R 1 for direct use where applicable.
   'R 1',
   'R pi',
   'pi != 0',
   'R (x + y)',
   'R (x * y)',
   'R (x - y)',
   'y != 0 => R (x / y)',
   'R x & R y & y != 0 => R (x / y)',
   '@R x & x != 0 => x / y != 0',
   'x != 0 => x / x = 1',
   'R (neg x)',
   'R (x ** 2)',
   'R (x ** 3)',
   'R (x ** 4)',
   'R (x ** 5)',
   'x != 0 => R (recip x)',
   'x != 0 => recip x != 0',
   'x * y != 0 == x != 0 & y != 0',
   'x ** 1 = x',
   'x ** 2 != 0 == x != 0',
   'x ** 3 != 0 == x != 0',
   'x ** 4 != 0 == x != 0',
   'x ** 5 != 0 == x != 0',
   {apply: function(term, cxt) {
       return (isArithmetic(term) &&
               rules.axiomArithmetic(term));
     }
   }
   );

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
  // This and the next function avoid simplifying the entire
  // equation because that is liable to simply undo an inentional
  // addition or multiplication "to both".
  const right = eqnPath.concat('/right');
  const left = eqnPath.concat('/left');
  const step1 = (rules.arrangeTerm(step, right)
                 .andThen('simplifySite', right));
  const step2 = (rules.arrangeTerm(step1, left)
                 .andThen('simplifySite', left));
  return step2;
}

/**
 * This does the auto-simplification for add/subtract both sides.  It
 * tries regrouping and then possible simplification.
 *
 */
function simplifyAddSubBoth(step, eqnPath) {
  // See above.
  const right = eqnPath.concat('/right');
  const left = eqnPath.concat('/left');
  const step1 = (rules.arrangeSum(step, right)
                 .andThen('simplifySite', right));
  const step2 = (rules.arrangeSum(step1, left)
                 .andThen('simplifySite', left));
  return step2;
}

declare(
  // Move all negations in past additions and multiplications;
  // eliminate double negations.
  // TODO: Consider removing this as redundant.
   {name: 'simplifyNegations',
    action: function(step) {
      var facts = ['neg (a + b) = neg a + neg b',
                   'neg (neg a) = a',
                   'neg (a * b) = neg a * b',
                   {apply: tryArithmetic}
                  ];
      var simpler = applyToFocalPart(step, facts);
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
   {name: 'removeSubtraction',
    action: function(step) {
      var facts = ['@a - b = a + neg b'];
      var info = {facts: facts, searchMethod: 'searchTerms'};
      var converted = applyToFocalPart(step, info);
      var simplified = rules.simplifyNegations(converted);
      return simplified.justify('removeSubtraction', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Convert - to + in step <input name=step>'),
    menu: 'algebra: convert - to +',
    description: 'convert subtraction to addition',
    labels: 'algebra'
  },

  // TODO: Review the usefulness of this and possibly remove it.
   {name: 'cleanUpTerms',
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
      var result = applyToFocalPart(step, facts);
      return result.justify('cleanUpTerms', arguments, [step]);
    },
    inputs: {step: 1},
    form: ('Clean up the terms in step <input name=step>'),
    menu: 'algebra: clean up terms',
    description: 'clean up each term',
    labels: 'algebra'
  }
);


declare
  (
  // Uses the associative law to "flatten" an expression made
  // up of additions and subtractions.
   {name: 'flattenSum',
    action: function(data, step, path) {
      var context = {factLists: {flatteners: data.flatteners}};
      return convert(step, path, function(expr) {
          var arrangeRhs = Toy.arrangeRhs;
          var eqn = rules.consider(step.get(path));
          var flat = arrangeRhs(eqn, context, 'flatteners');
          return flat;
      }).justify('flattenSum', [step, path], [step]);  // Uses .bind.
    }.bind(null,
           {flatteners: [
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
           }),
    inputs: {site: 1},
    toOffer: function(step, term) {
      return (term.matchSchema('a + b') || term.matchSchema('a - b'));
    },
    menu: 'algebra: flatten {term}',
    description: 'flatten term;; {in step siteStep}',
    labels: 'algebra'
  },

  // In a flattened sequence of additions and subtractions, this moves
  // all the numeric terms to the end.  This might readily be extended
  // to organize terms according to the powers of variables in each.
   {name: 'arrangeSum',
    action: function(step, path) {
      var numeralBefore = '$.b.isNumeral() && !$.c.isNumeral()';
      var numRightMovers = [
        {stmt: 'a + b = b + a',
         where: '$.a.isNumeral() && !$.b.isNumeral()'},
        {stmt: '@a - b = neg b + a',
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
    menu: 'algebra: collect like terms in {term}',
    description: 'collect like terms;; {in step siteStep}',
    labels: 'algebra'
  },

  /**
   * Inline rule that converts negations into -1 * x within
   * a term of * and /.
   */
   {name: 'denegateTerm',
      action: function denegateTerm(data, step, path) {
        let eqn = rules.consider(step.get(path));
        return Toy.arrangeRhs(eqn, data.context, 'denegaters');
      }.bind(null,
             {context:
              {factLists:
	       {denegaters:
                [{stmt: 'neg a = -1 * a'},
	         {descend:
                  {schema: 'a * b',
                   parts: {a: 'denegaters', b: 'denegaters'}}},
                 {descend:
                  {schema: 'a / b',
                   parts: {a: 'denegaters', b: 'denegaters'}}}
	        ]}
              }
             })
   },

  /**
   * "Flattens" a term made up of "*", "/", and "neg".  Converts
   * uses of "neg" into multiplication by -1, then removes
   * parentheses, traversing uses of "*" and "/".
   */
   {name: 'flattenTerm',
    action: function flattenTerm(data, step, path) {
      var context = {factLists: {flatteners: data.flatteners}};
      return convert(step, path, function(expr) {
          var arrangeRhs = Toy.arrangeRhs;
          var eqn = rules.consider(step.get(path));
          var noneg = rules.denegateTerm(eqn, '/main/right');
          var flat = arrangeRhs(noneg, context, 'flatteners');
          return flat;
      }).justify('flattenTerm', [step, path], [step]);  // Uses .bind.
    }.bind(null,
           {flatteners: [
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
           ]}),
    inputs: {site: 1},
    menu: 'algebra: flatten {term}',
    description: 'flatten term;; {in step siteStep}',
    labels: 'algebra'
   },

    // This expects a reference to a "term", a composite of
    // multiplications and divisions.  It puts them in a form
    // with at most one division, and that at the top level of
    // of the tree.  Also flattens multiplications.
    {name: 'makeRatio',
     action: function(step_arg, path_arg) {
       const facts = [
         // These two reduce the number of divisions.
         '(x / y) / z = x / (y * z)',
         'x / (y / z) = (x * z) / y',
         // The next two move divisions toward the root of the
         // expression tree.
         'x * (y / z) = (x * y) / z',
         '(x / y) * z = (x * z) / y',
         // This one flattens multiplication, which is conceptually
         // distinct.
         'x * (y * z) = x * y * z',
       ];
       let result = Toy.repeatedly
       (step_arg, step => 
        Toy.withExit(
          exit => {
            function walkMulDiv(term, path) {
              const next = Toy.applyMatchingFact(step, path, facts);
              if (next) {
                Toy.exitFrom(exit, next);
              }
              const mulDiv = [
                {match: 'a * b', a: walkMulDiv, b: walkMulDiv},
                {match: 'a / b', a: walkMulDiv, b: walkMulDiv}
              ];
              term.walkPatterns(mulDiv, path);
            }
            walkMulDiv(step.get(path_arg), path_arg);
          })
       );
       return result.justify('makeRatio', arguments, [step_arg]);
     },
     inputs: {site: 1},
     menu: 'algebra: put in ratio form',
     description: 'to ratio form',
     labels: 'algebra'
    },

    {name: 'factorToRightmost',
     action: function(step_arg, path_arg) {
       const wff = step_arg.wff;
       const commute = rules.fact('x * y = y * x');
       const commove = 
             Object.assign({}, commute.wff.movement('x'), {fact: commute});
       const assoc = rules.fact('z * x * y = z * y * x');
       const assmove = 
             Object.assign({}, assoc.wff.movement('x'), {fact: assoc});
       const xformers = [commove, assmove];

       let nextPath = wff.mainify(wff.prettifyPath(path_arg));
       function xform(step) {
         for (const info of xformers) {
           const path = nextPath.upTo(info.from);
           if (path) {
             if (Toy.canRewrite(step, path, info.fact)) {
               nextPath = path.concat(info.to);
               return step.rewrite(path, info.fact);
             }
           }
         }
       }
       const result = Toy.repeatedly(step_arg, xform);
       return (result &&
               result.justify('factorToRightmost', arguments, [step_arg]));
     },
     inputs: {site: 1},
     menu: 'algebra: make rightmost',
     description: 'make rightmost',
     labels: 'algebra'
    },

    {statement: 'b != 0 & d != 0 => c / (b * d) = 1 / b * (c / d)',
     proof: function() {
       return (rules.consider('c / (b * d)')
               .rewrite('c', 'x = 1 * x')
               .rewrite('/main/right', 'a * c / (b * d) = a / b * (c / d)'));
     }
    },

    {statement: 'x != 0 & b != 0 => x / (b * x) = 1 / b',
     proof: function() {
       return (rules.consider('x / (b * x)')
               .rewrite('b * x', 'x * y = y * x')
               .rewrite('x / (x * b)', 'x / (x * b) = 1 / b'));
     },
     simplifier: true,
    },

    {name: 'cancelFactor',
     precheck: function(step, path_arg) {
       const ppath = step.prettifyPath(step.asPath(path_arg));
       const ancestors = step.wff.ancestors(ppath).reverse();
       const target = ancestors[0];
       for (let i = 1; i < ancestors.length; i++) {
         const term = ancestors[i];
         if (term.isCall2('/')) {
           return true;
         } else if (!term.isCall2('*')) {
           return false;
         }
       }
       return false;
     },
     action: function(step, path) {
       const wff = step.wff;
       const basePart = term => term.isCall2('**') ? term.getLeft() : term;
       const ppath = wff.mainify(wff.prettifyPath(path));
       const term = step.get(ppath);
       const termBase = basePart(term);
       // This is the path to the nearest enclosing division.
       const divPath =
             wff.mainify(wff.findParent(ppath, term => term.isCall2('/')));
       if (divPath) {
         // Flatten both sides of the ratio.
         const flattened = (step.andThen('flattenTerm',
                                         divPath.concat('/right'))
                            .andThen('flattenTerm',
                                     divPath.concat('/left')));
         // Get the ratio with the flattened parts (~same path)
         const div = step.get(divPath);
         // First segment toward the selected term.
         const thisSeg = ppath.remainder(divPath).segment;
         const thatSeg = thisSeg == 'left' ? 'right' : 'left';
         const thisChainPath = divPath.concat(new Path(thisSeg));
         const thisChain = flattened.get(thisChainPath);
         // Find term identical to the selected one on "this" side.
         const pathInChain = thisChain.prettyPathTo(term);
         const thisPath = thisChainPath.concat(pathInChain);
         // Move the selected term moved to rightmost position.
         const moved1 = rules.factorToRightmost(flattened, thisPath);

         // Division node after first phase of movement.
         const div1 = moved1.get(divPath);
         // Now find a path to a corresponding term on the other side.
         const thatChain = div.descend(thatSeg);
         const thoseTerms = thatChain.chainTerms('*');
         const thosePaths = thatChain.chainPaths('*');
         const thatIndex = thosePaths.findIndex(
           path => basePart(thatChain.revGet(path)).sameAs(termBase)
         );
         if (thatIndex >= 0) {
           //
           // Found a similar term to cancel with it.
           //
           const apply = Toy.applyMatchingFact;
           // Path in other side chain, to a corresponding term.
           const thatChainPath = thosePaths[thatIndex].reverse();
           const moved2 = rules.factorToRightmost(
             moved1,
             divPath.concat(new Path(thatSeg).concat(thatChainPath))
           );
           const arrangers = [
             '(a * c) / (b * d) = (a / b) * (c / d)',
             'c / (b * d) = (1 / b) * (c / d)',
             '(a * c) / d = a * (c / d)',
           ];
           let simpler = apply(moved2, divPath, arrangers) || moved2;
           const solo = simpler == moved2;

           // Factors to cancel are now c and d.
           const cdPath = solo ? divPath : divPath.concat('/right');
           // Now convert powers (up to 5) into multiplication.
           const powers = [
             'x ** 1 = x',
             'x ** 2 = x * x',
             'x ** 3 = x * x * x',
             'x ** 4 = x * x * x * x',
             'x ** 5 = x * x * x * x * x',
           ];
           for (const p1 of ['/left', '/right']) {
             const p = cdPath.concat(p1);
             simpler = apply(simpler, p, powers) || simpler;
           }

           // Cancel out common factors.
           const cancelers = [
             'a * x / (b * x) = a / b',
             'x / (b * x) = 1 / b',
             'a * x / x = a',
             'x / x = 1',
           ];
           simpler = Toy.repeatedly(simpler, step =>
                                    apply(step, cdPath, cancelers));

           // Now convert x * x etc. back into exponents.
           const mults = [
             'x * x = x ** 2',
             'x * x * x = x ** 3',
             'x * x * x * x = x ** 4',
             'x * x * x * x * x = x ** 5',
           ];
           if (simpler.get(cdPath).isCall2('/')) {
             for (const p1 of ['/left', '/right']) {
               const p = cdPath.concat(p1);
               simpler = apply(simpler, p, mults) || simpler;
             }
           } else {
             simpler = apply(simpler, cdPath, mults) || simpler;
           }

           if (!solo) {
             simpler = rules.makeRatio(simpler, divPath);
             simpler = (apply(simpler, divPath.concat('/left'),
                              [{apply: tryArithmetic}]) ||
                        simpler);
           }

           return simpler.justify('cancelFactor', arguments, [step]);

           // Move that one all the way to the right.
           // Use (a * b) / (c * d) = (a / c) * (b / d).
           // Cancel, reducing power(s).
           // Put any remaining term back in numerator or denominator.
           // Final facts:
           // (a / c) * b = a * b / c
           // (a / c) * (1 / d ) = a / (c * d)
           // (a / c) * 1 = a / c
           // Interconvert powers and multiplication.
         }
       }
     },
     inputs: {site: 1},
     menu: 'algebra: cancel by division',
     description: 'cancel by division',
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
   {name: 'arrangeRational',
    toOffer: function(step, expr) {
      return (expr.matchSchema('a * b') ||
              expr.matchSchema('a / b') ||
              expr.matchSchema('neg (a * b)') ||
              expr.matchSchema('neg (a / b)'));
    },
    action: function arrangeRational(data, step, path, numsLeft) {
      var context = data.context;
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
              resulted = (rules.rewrite(arithmetized, '/main/right',
                                        'a = a * 1')
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
          return rules.simplifySite(resulted, '/main/right')
          .justify('arrangeRational', [step, path, numsLeft], [step]);  // .bind
        });
    }.bind(null, (() => {
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
    })())
   },

  /**
   * Arrange a rational expression into "ratio form", [a / b], with
   * numeric coefficents on the left of "a" and "b".
   */
   {name: 'arrangeRatio',
    action: function arrangeRatio(step, path) {
      return (rules.arrangeRational(step, path, true)
              .justify('arrangeRatio', arguments, [step]));
    },
    inputs: {site: 1},
    toOffer: 'return term.isReal()',
    menu: 'algebra: term to form a / b',
    description: 'ratio form for term;; {in step siteStep}',
    labels: 'obsolete'
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
   {name: 'arrangeTerm',
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
	  {stmt: 'a * b / c = a / c * b',
	   where: '$.a.isNumeral() && $.c.isNumeral()'},
          {stmt: 'a * b / c = b * (a / c)',
           where: '$.b.isNumeral()'},
          {stmt: 'a / (b * c) = 1 / c * (a / b)',
           where: '$.c.isNumeral()'}
      ];
      return ((Toy.applyMatchingFact(step2, path, facts) || step2)
              .justify('arrangeTerm', arguments, [step]));
    },
    inputs: {site: 1},
    toOffer: 'return term.isReal()',
    menu: 'algebra: term to form a / b * x',
    description: 'term to form a / b * x;; {in step siteStep}',
    labels: 'algebra'
  },

  // Regrouping, but just for additions.
  // TODO: When there is a more suitable regrouping rule, remove this.
   {name: 'regroupAdditions',
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
      var visPath = step.pathToFocalPart();
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
   {name: 'regroup',
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
   }
);


let termRightData =
    {
      factsA: [
        'neg a + b = b - a',
        'a + b = b + a',
        '@a - b = neg b + a'
      ],
      factsB: [
        'a + b + c = a + c + b',
        'a + b - c = a - c + b',
        'a - b + c = a + c - b',
        'a - b - c = a - c - b'
      ]};


declare(
  /**
   * Moves a term to the right in a sequence of summed terms.
   * The sequence must be "flat", associated to the left.
   */
   {name: 'moveTermRight',
    toOffer: function(step, expr) {
      var path = step.pathTo(expr);
      var factsA = termRightData.factsA;
      var factsB = termRightData.factsB;
      // Truthy value if the given name in the LHS of the fact can
      // match the part of this at the selected path.
      function testFact(name, fact_arg) {
        var schema = Toy.resolveToFact(fact_arg).getMain().getLeft();
        var info = step.matchSchemaPart(path, schema, name);
        return info || undefined;
      }
      return (Toy.each(factsB, testFact.bind(null, 'b')) ||
              Toy.each(factsA, testFact.bind(null, 'a')));
    },
    action: function(step, path_arg) {
      var factsB = termRightData.factsB;
      var factsA = termRightData.factsA;
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
    menu: 'algebra: move {term} to the right',
    description: 'move term right',
    labels: 'algebra'
  },

  /**
   * Moves a term to the left in a sequence of summed terms.
   * The sequence must be "flat" (associated to the left).
   */
   {name: 'moveTermLeft',
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
        '@a - b = neg b + a'
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
    menu: 'algebra: move {term} to the left',
    description: 'move term left',
    labels: 'algebra'
  },

  /**
   * Rule to force association to the right for addition, subtraction,
   * multiplication, and division.  Does nothing if not applicable.
   */
   {name: 'groupToRight',
    toOffer: function(step, expr) {
      return Toy.matchFactPart(step, step.pathTo(expr), regroupingFacts, 'b');
    },
    autoSimplify: function(step) {
      // TODO: Consider renaming this flag as "focal part".
      if (Toy.autoSimplifyWholeStep) {
        return rules.simplifyFocalPart(step);
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
    menu: 'algebra: group {term} with {right}',
    description: 'group to the right',
    labels: 'algebra'
  },

  /**
   * Removes parentheses from an add/sub/mul/div expression that
   * needs them to force association to the right.  Uses converses
   * of regroupingFacts.
   */
   {name: 'ungroup',
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
      return ((Toy.applyMatchingFact(step, path, ungroupingFacts) || step)
              .justify('ungroup', arguments, [step]));
    },
    inputs: {site: 1},
    menu: 'algebra: ungroup {term}',
    description: 'ungroup',
    labels: 'algebra'
  },

  /**
   * Moves term to the left as needed until it does not necessarily
   * belong to the left of its left neighbor.
   * 
   */
   {name: 'placeTermLeftward',
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
    menu: 'algebra: move term left as needed',
    description: 'move term left as needed',
    // Could be algebra, but this rule seems better for more advanced
    // students.
    labels: ''
   },

  /* TODO: Choose a way to get varName into the "where" clauses,
   *   then finish this.
   {name: 'regroupBy',
    action: function(step, path, varName) {
      var facts = [{stmt: 'a + b = b + a',
                    where: '$.a.isNumeral() && !$.b.isNumeral()'},
                   {stmt: 'a + b + c = a + c + b',
                    where: '$.b.isNumeral() && !$.c.isNumeral()'}
                  ];
      var result = applyToFocalPart(step, facts);
      return result.justify('regroupBy', arguments, [step]);
    },
    inputs: {site: 1, varName: 3},
    form: 'Group terms with variable <input name=varName>',
    menu: 'algebra: group terms',
    description: 'group terms with {varName}'
  },
  */

  );


declare
  (
  /**
   * Reduces the selected fraction to lower terms using their least
   * common divisor (via Toy.npd).  No, not the greatest common
   * divisor, for pedagogical reasons.
   */
   {name: 'reduceFraction',
    action: function(step, path) {
      var expr = step.get(path);
      var lv = expr.getLeft().getNumValue();
      var rv = expr.getRight().getNumValue();
      var divisor = Toy.npd(lv, rv, 0);
      var fact = rules.fact('b != 0 & c != 0 => a / b = (a / c) / (b / c)');
      const map = {a: expr.getLeft(),
                   b: expr.getRight(),
                   c: Toy.numify(divisor)};
      const fact2 = rules.instMultiVars(fact, map);
      const fact3 = rules.arithmetic(fact2, '/main/right/right');
      const fact4 = rules.arithmetic(fact3, '/main/right/left');
      const replaced = rules.replace(step, path, fact4);
      const result = rules.simplifyAsms(replaced);
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
    menu: 'reduce fraction {term}',
    description: 'reduce fraction',
    labels: 'algebra'
  },

  /**
   * Reduces the selected fraction to the form 1/k in the case where
   * the numerator exactly divides the denominator.
   */
   {name: 'divideOutFraction',
    // TODO: Use the reciprocal if needed, then just rules.arithmetic.
    action: function(step, path) {
      var expr = step.get(path);
      var lv = expr.getLeft().getNumValue();
      var rv = expr.getRight().getNumValue();
      var divisor = Math.min(lv, rv);
      var fact = rules.fact('b != 0 & c != 0 => a / b = (a / c) / (b / c)');
      const map = {a: expr.getLeft(),
                   b: expr.getRight(),
                   c: Toy.numify(divisor)};
      const fact2 = rules.instMultiVars(fact, map);
      const fact3 = rules.arithmetic(fact2, '/main/right/right');
      const fact4 = rules.arithmetic(fact3, '/main/right/left');
      const replaced = rules.replace(step, path, fact4);
      const result = rules.simplifyAsms(replaced);
      return result.justify('divideOutFraction', arguments, [step]);
    },
    toOffer: function(step, expr) {
      if (expr.isCall2('/')) {
        var l = expr.getLeft();
        var r = expr.getRight();
        if (l.isNumeral() && r.isNumeral()) {
          var lv = l.getNumValue();
          var rv = r.getNumValue();
          // This enusres that lv and rv are both nonzero.
          return lv != 1 && rv != 1 && (lv % rv === 0 || rv % lv === 0);
        }
      }
    },
    inputs: {site: 1},
    description: 'divide out fraction',
    menu: 'divide out {term}',
    labels: 'algebra'
  },

  /**
   * Given a target expression which is the sum of two fractions (with
   * integer denominators) and a requested new denominator, this
   * produces a result with the fraction denominators changed to the
   * specified value, which must be an exact multiple of both.
   */
   {name: 'commonDenominator',
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
   * Given a numeric term (integer) that has prime factors, produce a
   * step that equates it to its prime factors.
   */
   {name: 'primeFactors',
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
    menu: 'prime factors of {term}',
    description: 'prime factors of {term}',
    labels: 'algebra',
    toOffer: function(step, expr) {
      return expr && expr.isNumeral();
    },
    autoSimplify: noSimplify
  }

  );


//// Algebra facts

declare(
   // A real number exists.  Equivalently exists {x. R x}.
   {statement: 'exists R',
    proof: function() {
       return (rules.fact('p x => exists p')
               .andThen('instMultiVars', {x: '0', 'p': 'R'})
               .andThen('simplifySite', ''));
     }
   },
  
   {statement: '@R a => a != none',
    proof: function() {
       var asm = rules.assume('a = none');
       return (rules.fact('not (R none)')
               .andThen('rewriteFrom', '/arg/arg', rules.eqnSwap(asm))
               .andThen('rewriteOnly', '', 'a => not b == b => not a')
               .andThen('simplifySite', '/right'));
     }
   },

   {statement: 'x + neg x = 0',
    simplifier: true,
    proof:
    ['(1 negFact)',
     '(2 forwardChain (s 1) (t ((((a & b) & c) == d) => (d => c))))',
     '(3 rewrite (s 2) (path "/left/right") (t ((x = y) == (y = x))))',
     '(4 assume (t (y = (neg x))))',
     '(5 display (s 3))',
     '(6 rewriteFrom (s 5) (path "/right/left/right") (s 4))',
     '(7 display (s 6))',
     '(8 removeLet (s 7) (path "/left/left"))'
     ]
   },

  // Addition
   {statement: 'a + b + c = a + c + b',
    proof: function() {
       var step = rules.consider('a + b + c')
       .rewrite('/main/right', 'a + b + c = a + (b + c)')
       .rewrite('/main/right/right', 'a + b = b + a')
       .rewrite('/main/right', 'a + (b + c) = a + b + c');
       return step;
     }
   },
   {statement: 'a + b + c = a + (c + b)',
    proof: function() {
       return rules.consider('a + b + c')
       .rewrite('/main/right', 'a + b + c = a + c + b')
       .rewrite('/main/right', 'a + b + c = a + (b + c)');
     }
   },

   // Multiplication
   {statement: 'a * b * c = a * c * b',
    proof: function() {
       var step = rules.consider('a * b * c')
       .rewrite('/main/right', 'a * b * c = a * (b * c)')
       .rewrite('/main/right/right', 'a * b = b * a')
       .rewrite('/main/right', 'a * (b * c) = a * b * c');
       return step;
     }
   },
   {statement: 'a * b * c = a * (c * b)',
    proof: function() {
       return (rules.fact('a * b * c = a * (b * c)')
               .rewrite('/main/right/right', 'a * b = b * a'));
     }
   }
);

// Distributivity
var distribFacts =
  [
   {statement: '(a + b) * c = a * c + b * c',
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
   {statement: 'a * b + b = (a + 1) * b',
    proof: function() {
      var step = rules.consider('a * b + b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
   {statement: 'b + a * b = (1 + a) * b',
    proof: function() {
      var step = rules.consider('b + a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c + b * c = (a + b) * c');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
   {statement: 'a + a = 2 * a',
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

   {statement: 'a * (b - c) = a * b - a * c',
    proof: function() {
      return rules.consider('a * (b - c)')
      .rewrite('/main/right/right', '@a - b = a + neg b')
      .rewrite('/main/right', 'a * (b + c) = a * b + a * c')
      .rewrite('/main/right/right', 'a * neg b = neg (a * b)')
      .rewrite('/main/right', '@a + neg b = a - b');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
   {statement: '(a - b) * c = a * c - b * c',
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
   {statement: 'a * b - b = (a - 1) * b',
    proof: function() {
      return rules.consider('a * b - b')
      .rewrite('/main/right/right', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  },
   {statement: 'b - a * b = (1 - a) * b',
    proof: function() {
      return rules.consider('b - a * b')
      .rewrite('/main/right/left', 'a = 1 * a')
      .rewrite('/main/right', 'a * c - b * c = (a - b) * c');
    },
    labels: 'algebra',
    converse: { labels: 'algebra' }
  }
   ];
declare.apply(null, distribFacts);

// TODO: Need distributivity of division over addition and subtraction.


// Private to isDistribFact.  A mapping from statement key to value
// that is truthy iff the statement is in distribFacts.
const _distribFacts = new Set();
for (const obj of distribFacts) {
  _distribFacts.add(Toy.resolveToFact(obj.statement));
}

/**
 * Returns a truthy value iff the statement is some version
 * of the distributed law in distribFacts.
 */
function isDistribFact(stmt) {
  return _distribFacts.has(Toy.resolveToFact(stmt));
}

declare(
  // Plus zero
  /* Omit from UI: somewhat redundant
     {statement: 'a = 0 + a',
   proof: function() {
     var step1 = rules.plusZero();
     var step2 = rules.eqnSwap(step1);
     var step3 = rules.rewrite(step2, '/main/right',
                               'a + b = b + a');
     return step3;
     }
   },
  */
   {statement: '0 + a = a',
    simplifier: true,
    proof: function() {
      var step1 = rules.plusZero();
      var step2 = rules.rewrite(step1, '/main/left',
                                'a + b = b + a');
      return step2;
    }
  },
   {statement: 'a - 0 = a',
    simplifier: true,
    proof: function() {
      var step1 = (rules.consider('a - 0')
                   .andThen('apply', '/main/right')
                   .andThen('arithmetic', '/main/right/right')
                   .rewrite('/main/right', 'a + 0 = a'));
      return step1;
    }
  },
   {statement: '0 - a = neg a',
    proof: function() {
      var step1 = (rules.consider('0 - a')
                   .andThen('apply', '/main/right')
                   .rewrite('/main/right', '0 + a = a'));
      return step1;
    }
  },
  // Times one
   {statement: '1 * a = a',
    simplifier: true,
    proof: function() {
      var step1 = rules.timesOne();
      var step2 = rules.rewrite(step1, '/main/left',
                                'a * b = b * a');
      return step2;
    }
  },

  // Zero times
   {statement: '0 * a = 0',
    simplifier: true,
    proof: function() {
      return rules.fact('x * 0 = 0')
      .rewrite('/main/left', 'a * b = b * a');
    }
  }
);

declare(
   {statement: 'a = b == a + c = b + c',
    desimplifier: true,
    proof:
    [
     '(1 abcPlus)',
     '(2 assume (t (x = y)))',
     '(3 applyToBoth (t {w. (w + z)}) (s 2))',
     '(4 andAssume (s 3) (t (((R x) & (R y)) & (R z))))',
     '(5 extractHypAt (s 4) (path "/left/left/left/left"))',
     '(6 extractHypAt (s 1) (path "/left/left/left/left"))',
     '(7 rewrite (s 6) (path "/right") (t (a == (a & T))))',
     '(8 replaceT (s 7) (path "/right/right") (s 5))',
     '(9 rewrite (s 8) (path "/right") (t (((a => b) & (b => a)) == (b == a))))'
     ]
  },

   {statement: 'a = b == a - c = b - c',
    desimplifier: true,
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '-', 'c')
                     .andThen('rewriteOnly', '', 'a == T => a'));
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
   {statement: 'c != 0 => (a * c = b * c => a = b)',
    // TODO: Figure out why the user must enter the c != 0 part
    //   when working interactively.
    proof: function() {
      var rewrite = rules.rewrite;
      var s1 = rules.assume('a * c = b * c');
      var s2 = rules.applyToBothWith(s1, '/', 'c');
      var s3 = rewrite(s2, '/main/right', 'a * b / c = a * (b / c)');
      var s6 = rewrite(s3, '/main/left', 'a * b / c = a * (b / c)');
      var s7 = rules.simplifySite(s6, '/right');
      var s8 = rules.extractHyp(s7, 'a * c = b * c');
      return s8;
    }
  },

   {statement: 'c != 0 => (a = b == a * c = b * c)',
    desimplifier: true,
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '*', 'c')
                     .andThen('rewriteOnly', '', 'a == T => a'));
      var back = rules.fact('c != 0 => (a * c = b * c => a = b)');
      var conj = rules.makeConjunction(forward, back);
      var taut = rules.tautology('(a => b) & (b => a) == (a == b)');
      var result = rules.rewriteOnly(conj, '/main', taut);
      return result;
    }
  },

  // This is primarily a lemma for the following equivalence.
   {statement: 'c != 0 => (a / c = b / c => a = b)',
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
              .andThen('simplifySite', '/right')
              .andThen('extractHyp', 'a / c = b / c'));
    }
  },

   {statement: 'c != 0 => (a = b == a / c = b / c)',
    desimplifier: true,
    proof: function() {
      var forward = (rules.assume('a = b')
                     .andThen('applyToBothWith', '/', 'c')
                     .andThen('rewriteOnly', '', 'a == T => a'));
      var back = rules.fact('c != 0 => (a / c = b / c => a = b)');
      var conj = rules.makeConjunction(forward, back);
      return rules.rewriteOnly(conj, '/main', '(p => q) & (q => p) == (p == q)');
    }
  }
);

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

declare(
  // With addition and subtraction

   {statement: '@a - b = a + neg b',
    proof: function() {
      var step1 = rules.consider('a - b');
      var step2 = rules.apply(step1, '/main/right');
      return step2;
    }
  },
   {statement: 'a - b = a + -1 * b',
    proof: function() {
      return (rules.fact('@a - b = a + neg b')
              .andThen('rewrite', '/main/right/right', 'neg x = -1 * x'));
    }
  },
   {statement: '@R b => a - neg b = a + b',
    proof: function() {
      return rules.consider('a - neg b')
      .andThen('apply', '/main/right')
      .rewrite('/main/right/right', 'neg (neg a) = a');
    }
  },
   {statement: 'neg a + b = b - a',
    simplifier: true,
    proof: function() {
      return rules.fact('@a + neg b = a - b')
        .rewrite('/main/left', 'a + b = b + a');
    }
  },
   {statement: '@a - b = neg b + a',
    proof: function() {
      return rules.fact('@a + neg b = a - b')
      .andThen('eqnSwap')
      .rewrite('/main/right', 'a + b = b + a');
    }
  },
   {statement: 'neg a + a = 0',
    proof: function() {
      return rules.fact('a + neg a = 0')
      .rewrite('/main/left', 'a + b = b + a');
    }
  },
   {statement: 'neg (neg a) = a',
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

  // Negation with multiplication.
  //
  // TODO: When negation gets a number-specific definition,
  // facts about it will become specific to (real) numbers.

   {statement: 'neg (a * b) = neg a * b',
    proof: function() {
      return rules.consider('neg (a * b)')
      .rewrite('/main/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * (b * c) = (a * b) * c')
      .rewrite('/main/right/left', '-1 * a = neg a');
    }
  },
   {statement: 'a * neg b = neg (a * b)',
    proof: function() {
      return rules.consider('a * neg b')
      .rewrite('/main/right/right', 'neg a = -1 * a')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right/left', 'a * b = b * a')
      .rewrite('/main/right', 'a * b * c = a * (b * c)')
      .rewrite('/main/right', '-1 * a = neg a');
    }
  },
   {statement: 'a * neg b = neg a * b',
    proof: function() {
      return rules.fact('a * neg b = neg (a * b)')
      .rewrite('/main/right', 'neg (a * b) = neg a * b');
    }
  },

  // Negation with division
   {statement: 'a / -1 = -1 * a',
    proof: function() {
      var fact = rules.axiomArithmetic('1 / -1');
      return (rules.consider('a / -1')
              .rewrite('/main/right/left', 'a = a * 1')
              .rewrite('/main/right', 'a * b / c = a * (b / c)')
              .rewrite('/main/right/right', fact)
              .rewrite('/main/right', 'a * b = b * a'));
    }
  },
   {statement: 'b != 0 => neg (a / b) = neg a / b',
    proof: function() {
      return (rules.consider('neg (a / b)')
              .rewrite('/main/right', 'neg a = -1 * a')
              .rewrite('/main/right', 'a * (b / c) = a * b / c')
              .rewrite('/main/right/left', '-1 * a = neg a'));
    }
  },

  // Other negation facts
   {statement: 'neg (a + b) = neg a + neg b',
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
   {statement: 'neg (a - b) = b - a',
    proof: function() {
      return rules.consider('neg (a - b)')
      .rewrite('/main/right/arg', '@a - b = a + neg b')
      .rewrite('/main/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right', 'neg (neg a) = a')
      .rewrite('/main/right', 'a + b = b + a')
      .rewrite('/main/right', '@a + neg b = a - b');
    }
  },
   {statement: 'neg (a - b) = neg a + b',
    proof: function() {
      return rules.consider('neg (a - b)')
      .rewrite('/main/right/arg', '@a - b = a + neg b')
      .rewrite('/main/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right', 'neg (neg a) = a');
    }
  },
   {statement: 'b != 0 => neg a / neg b = a / b',
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
);

declare(
  // Subtraction facts

  // Moving terms to the left
   {statement: 'a + b - c = a - c + b',
    proof: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', '@a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right/left', '@a + neg b = a - b');
    }
  },
   {statement: 'a - b + c = a + c - b',
    proof: function() {
      return rules.consider('a - b + c')
      .rewrite('/main/right/left', '@a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + c + b')
      .rewrite('/main/right', '@a + neg b = a - b');
    }
  },
   {statement: 'a - b + c = a + (c - b)',
    proof: function() {
      return rules.fact('a - b + c = a + c - b')
      .rewrite('/main/right', '@a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', '@a + neg b = a - b');
    }
  },
   {statement: 'a - (b - c) = a + (c - b)',
    proof: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right', '@a - b = a + neg b')
      .rewrite('/main/right/right', 'neg (a - b) = b - a');
    }
  },
   {statement: 'a - (b - c) = a + c - b',
    proof: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right', 'a - (b - c) = a + (c - b)')
      .rewrite('/main/right/right', '@a - b = a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', '@a + neg b = a - b');
    }
  },

  // Associativity: four cases: each operation can be + or -, and
  // initial association can be to the left or right.
   {statement: 'a + b - c = a + (b - c)',
    proof: function() {
      return rules.consider('a + b - c')
      .rewrite('/main/right', '@a - b = a + neg b')
      .rewrite('/main/right', 'a + b + c = a + (b + c)')
      .rewrite('/main/right/right', '@a + neg b = a - b');
    },
    labels: 'algebra2',
    converse: { labels: 'algebra' }
  },
   {statement: 'a - (b + c) = a - b - c',
    proof: function() {
      var step = rules.consider('a - (b + c)')
      .rewrite('/main/right', '@a - b = a + neg b')
      .rewrite('/main/right/right',
               'neg (a + b) = neg a + neg b')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right', '@a + neg b = a - b')
      .rewrite('/main/right/left', '@a + neg b = a - b');
      return step;
    },
    labels: 'algebra',
    converse: { labels: 'algebra2' }
  },  
   {statement: 'a - b - c = a - c - b',
    proof: function() {
      return rules.consider('a - b - c')
      .rewrite('/main/right/left', '@a - b = a + neg b')
      .rewrite('/main/right', 'a + b - c = a - c + b')
      .rewrite('/main/right', '@a + neg b = a - b');
    }
  },
   {statement: 'a - (b - c) = a - b + c',
    proof: function() {
      return rules.consider('a - (b - c)')
      .rewrite('/main/right/right', '@a - b = a + neg b')
      .rewrite('/main/right', '@a - b = a + neg b')
      .rewrite('/main/right/right', 'neg (a + b) = neg a + neg b')
      .rewrite('/main/right/right/right', 'neg (neg a) = a')
      .rewrite('/main/right', 'a + (b + c) = a + b + c')
      .rewrite('/main/right/left', '@a + neg b = a - b');
    },
    labels: 'algebra',
    converse: { labels: 'algebra2' }
  },

  // Simplification
   {statement: 'a - a = 0',
    simplifier: true,
    proof: function() {
      return (rules.eqSelf('a - a')
              .andThen('apply', '/right')
              .rewrite('/main/right', 'a + neg a = 0'));
    }
  },

   {statement: 'a + b - b = a',
    proof: function() {
      return (rules.consider('a + b - b')
              .rewrite('/main/right', 'a + b - c = a + (b - c)')
              .rewrite('/main/right/right', 'a - a = 0')
              .rewrite('/main/right', 'a + 0 = a'));
    }
  },

   {statement: 'a - b + b = a',
    proof: function() {
      return (rules.consider('a - b + b')
              .rewrite('/main/right', 'a - b + c = a + c - b')
              .rewrite('/main/right', 'a + b - b = a'));
    }
  },

   {statement: 'a + b - b = a',
    simplifier: true,
    proof: function() {
      return (rules.fact('a + b - c = a + (b - c)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyFocalPart'));
    }
  },

   {statement: 'a - b + b = a',
    simplifier: true,
    proof: function() {
      return (rules.fact('a - b + c = a - (b - c)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyFocalPart'));
    }
  }

);

declare(
  // Reciprocal facts

   {statement: 'x != 0 => recip x != 0',
    proof: function() {
      var step2 = rules.fact('1 != 0');
      var step3 = (rules.rewrite(step2, '/left', '1 = x * recip x')
                   .rewrite('/main', 'a * b != 0 == a != 0 & b != 0'));
      var step4 = rules.tautology('a => (b & c) => (a => c)');
      var step5 = rules.forwardChain(step3, step4);
      return step5;
    }
  },
   {statement: 'a / b = a * recip b',
    // TODO: Prove me!
  },
   {statement: 'a != 0 => recip (recip a) = a',
    simplifier: true,
    proof: function() {
      var rewrite = rules.rewrite;
      var step1 = rules.fact('a * recip a = 1');
      var step2 = rules.applyToBothWith(step1, '*', Toy.parse('recip (recip a)'));
      var step3 = rewrite(step2, '/main/right', '1 * a = a');
      var step4 = rewrite(step3, '/main/left', 'a * b * c = a * (b * c)');
      var step6 = rules.rewrite(step4, '/main/left/right', 'a * recip a = 1');
      var step7 = rewrite(step6, '/main/left', 'a * 1 = a');
      var step8 = rules.eqnSwap(step7);
      return step8;
    }
  },
   {statement: '@R (recip a) & recip a != 0 => R a & a != 0',
    proof: function() {
      var taut = rules.tautology('(a == b) => (a => b)');
      var fact = rules.axiomReciprocal2();
      return rules.forwardChain(fact, taut);
    }
  },
   {statement: '@R a & a != 0 => R (recip a) & recip a != 0',
    proof: function() {
      var taut = rules.tautology('(a == b) => (b => a)');
      var fact = rules.axiomReciprocal2();
      return rules.forwardChain(fact, taut);
    }
  },
   {statement: 'a != 0 & b != 0 => recip (a * b) = recip a * recip b',
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
);

declare(
  // Division rules

  {statement: 'c != 0 => a * b / c = a / c * b',
    proof: function() {
      var step = rules.consider('a * b / c')
      .rewrite('/main/right', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * b * c = a * c * b')
      .rewrite('/main/right/left', 'a * recip b = a / b');
      return step;
    }
  },
  {statement: 'b != 0 => a / b * c = a * c / b',
    proof: function() {
      var step = rules.consider('a / b * c')
      .rewrite('/main/right/left', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * b * c = a * c * b')
      .rewrite('/main/right', 'a * recip b = a / b');
      return step;
    }
  },
  {statement: 'b != 0 => a / b * c = a * (c / b)',
    proof: function() {
      var divFact = rules.fact('a * recip b = a / b');
      return (rules.fact('a * b * c = a * (c * b)')
              .andThen('instVar', 'recip d', 'b')
              .rewrite('/main/right/right', divFact)
              .rewrite('/main/left/left', divFact));
    }
  },
  {statement: 'b != 0 => a / b * b = a',
    simplifier: true,
    proof: function() {
      return (rules.fact('a / b * c = a * (c / b)')
              .andThen('instVar', 'b', 'c')
              .andThen('simplifyFocalPart'));
    }
  },
  {statement: 'b != 0 & c != 0 => a / (b * c) = a / b / c',
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
  {statement: 'b != 0 & c != 0 => a / b / c = a / c / b',
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
  {statement: 'b != 0 & c != 0 => a / (b / c) = a / b * c',
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
  {statement: 'b != 0 & c != 0 => a / (b / c) = a * c / b',
   proof: function() {
     const s1 = (rules.consider('a / (b / c)')
		 .andThen('simplifySite', '/right',
			  ['a / b = a * recip b',
			   'recip (a * b) = recip a * recip b',
			   'recip (recip a) = a',
			  ])
		 .rewrite('(recip b * c)', 'a * b = b * a')
		 .rewrite('/main/right', 'a * (b * c) = a * b * c')
		 .rewrite('/main/right', 'a * recip b = a / b')
		);
     return s1;
   }
  },
  {statement: 'a != 0 & b != 0 => a / (a * b) = 1 / b',
    simplifier: true,
    proof: function() {
      return (rules.fact('a / (b * c) = a / b / c')
              .andThen('instVar', 'a', 'b')
              .andThen('simplifyFocalPart'));
    }
  },
  {statement: 'c != 0 => a * (b / c) = a * b / c',
    proof: function() {
      var step = rules.consider('a * (b / c)')
      .rewrite('/main/right/right', 'a / b = a * recip b')
      .rewrite('/main/right', 'a * (b * c) = a * b * c')
      .rewrite('/main/right', 'a * recip b = a / b');
      return step;
    }
  },
  {statement: 'a != 0 => a / a = 1',
    simplifier: true,
    proof: function() {
      var fact = rules.fact('a / b = a * recip b').andThen('eqnSwap');
      return (rules.fact('a != 0 => a * recip a = 1')
              .rewrite('/main/left', fact));
    }
  },
  {statement: 'b != 0 => a * b / b = a',
   simplifier: true,
   proof: function() {
     return (rules.fact('a * b / c = a * (b / c)')
             .andThen('instVar', 'b', 'c')
             .andThen('simplifyFocalPart'));
   },
   simplifier: true,
  },
  // This is useful for converting a summand to a fraction like
  // its neighbor.
  {statement: '@R b & R c & c != 0 => a / c + b = a / c + b * c / c',
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a / c + b')
              .rewrite('/right/right', fact));
    },
    labels: 'algebra'
  },
  // Likewise useful for converting a summand to a fraction like
  // its neighbor.
  {statement: '@R a & R c & c != 0 => a + b / c = a * c / c + b / c',
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a + b / c')
              .rewrite('/right/left', fact));
    },
    labels: 'algebra'
  },
  // Similar to the above, but now for subtraction rather than addition.
  {statement: '@R b & R c & c != 0 => a / c - b = a / c - b * c / c',
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a / c - b')
              .rewrite('/right/right', fact));
    },
    labels: 'algebra'
  },
  // More of the same.
  {statement: '@R a & R c & c != 0 => a - b / c = a * c / c - b / c',
    proof: function() {
      var fact = rules.fact('a = a * b / b').andThen('instVar', 'c', 'b');
      return (rules.consider('a - b / c')
              .rewrite('/right/left', fact));
    },
    labels: 'algebra'
  },
  {statement: 'b != 0 & c != 0 => a / b = (a * c) / (b * c)',
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
   desimplifier: true,
  },
  {statement: 'b != 0 & c != 0 => a / b = (a / c) / (b / c)',
    proof: function() {
      return (rules.fact('a / b = (a * c) / (b * c)')
              .andThen('instVar', 'recip c', 'c')
              .rewrite('/right/right/left', 'a * recip b = a / b')
              .rewrite('/right/right/right', 'a * (recip b) = a / b'));
    }
  },
  {statement: 'c != 0 & d != 0 => (a * b) / (c * d) = (a / c) * (b / d)',
    proof: function() {
      return (rules.consider('a * b / (c * d)')
              .andThen('flattenTerm', '/main/right')
              .rewrite('/main/right/left', 'a * b / c = a / c * b')
              .rewrite('/main/right', 'a * b / c = a * (b / c)'));
    }
  },
  // Used in arrangeTerm.
  {statement: 'c != 0 & d != 0 => (a * b) / (c * d) = (b / d) * (a / c)',
    proof: function() {
      return (rules.fact('(a * b) / (c * d) = (a / c) * (b / d)')
              .rewrite('/main/right', 'a * b = b * a'));
    }
  },
  // Used in arrangeTerm.
  {statement: 'c != 0 => a * b / c = b * (a / c)',
    proof: function() {
      return (rules.consider('a * b / c')
              .rewrite('/main/right/left', 'a * b = b * a')
              .rewrite('/main/right', 'a * b / c = a * (b / c)'));
    }
  },
  // Used in arrangeTerm.
  {statement: 'b != 0 & c != 0 => a / (b * c) = 1 / c * (a / b)',
    proof: function() {
      return (rules.consider('a / (b * c)')
              .rewrite('/main/right/left', 'a = a * 1')
              .rewrite('/main/right', 'a * b / (c * d) = (b / d) * (a / c)'));
    }
  },
  // Distributivity:
  {statement: 'c != 0 => (a + b) / c = a / c + b / c',
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
  {statement: 'c != 0 => (a - b) / c = a / c - b / c',
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
);

declare(
   {statement: 'x ** 1 = x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '0', 'y')
               .andThen('rewrite', 'x ** 0', 'x ** 0 = 1')
               .andThen('rewrite', '1 * x', '1 * x = x')
               .andThen('rewrite', '0 + 1', '0 + x = x'));
     }
   },

   {statement: 'x ** 2 = x * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '1', 'y')
               .andThen('rewrite', 'x ** 1', 'x ** 1 = x')
               .andThen('rewrite', '1 + 1', '1 + 1 = 2'));
     }
   },

   {statement: 'x ** 3 = x ** 2 * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '2', 'y')
               .andThen('rewrite', '2 + 1', '2 + 1 = 3'));
     }
   },

   {statement: 'x ** 4 = x ** 3 * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '3', 'y')
               .andThen('rewrite', '3 + 1', '3 + 1 = 4'));
     }
   },

   {statement: 'x ** 5 = x ** 4 * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '4', 'y')
               .andThen('rewrite', '4 + 1', '4 + 1 = 5'));
     }
   },

   {statement: 'x ** 3 = x * x * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '2', 'y')
               .andThen('rewrite', 'x ** 2', 'x ** 2 = x * x')
               .andThen('rewrite', '2 + 1', '2 + 1 = 3'));
     }
   },

   {statement: 'x ** 4 = x * x * x * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '3', 'y')
               .andThen('rewrite', 'x ** 3', 'x ** 3 = x * x * x')
               .andThen('rewrite', '3 + 1', '3 + 1 = 4'));
     }
   },

   {statement: 'x ** 5 = x * x * x * x * x',
    proof: function() {
       return (rules.axiomNextPower()
               .andThen('instVar', '4', 'y')
               .andThen('rewrite', 'x ** 4', 'x ** 4 = x * x * x * x')
               .andThen('rewrite', '4 + 1', '4 + 1 = 5'));
     }
   },

   {statement: 'R (x ** 2)',
    proof: function() {
       return (rules.fact('R (x * y)')
               .andThen('instVar', 'x', 'y')
               .andThen('rewrite', 'x * x', 'x * x = x ** 2'));
     }
   },

   {statement: 'R (x ** 3)',
    proof: function() {
       return (rules.fact('R (x * y)')
               .andThen('instMultiVars', {x: 'x ** 2', y: 'x'})
               .andThen('rewrite', 'x ** 2 * x', 'x ** 2 * x = x ** 3'));
     }
   },

   {statement: 'R (x ** 4)',
    proof: function() {
       return (rules.fact('R (x * y)')
               .andThen('instMultiVars', {x: 'x ** 3', y: 'x'})
               .andThen('rewrite', 'x ** 3 * x', 'x ** 3 * x = x ** 4'));
     }
   },

   {statement: 'R (x ** 5)',
    proof: function() {
       return (rules.fact('R (x * y)')
               .andThen('instMultiVars', {x: 'x ** 4', y: 'x'})
               .andThen('rewrite', 'x ** 4 * x', 'x ** 4 * x = x ** 5'));
     }
   }
);

declare(

  {statement: '(x = y == u = v) == (x != y == u != v)',
   name: 'neqEquiv',
   proof: function() {
     return (rules.consider('x = y == u = v')
             .rewrite('/right', 'a == b == (not a == not b)')
             .andThen('simplifySite', '/right'));
   }
  },

);

declare(

  // TODO: These are all simplifiers, and can be applied to
  //   their own /right (consequent).  Consequently, . . .
  //   the simplification must only be applied to /right/right.
  //   Facts (such as these) need to be marked as inProgress
  //   when their proof begins, but are currently not.
    
  {statement: 'x ** 2 = 0 == x = 0',
   name: 'x2',
   proof: function() {
     return (rules.consider('x ** 2 = 0')
             .rewrite('x ** 2', 'x ** 2 = x * x')
             .rewrite('x * x = 0', 'x * y = 0 == x = 0 | y = 0')
             .andThen('simplifySite', '/right/right')
            );
   },
   simplifier: true,
  },

  {statement: 'x ** 2 != 0 == x != 0',
   proof: function() {
     return rules.fact('x2').rewrite('/main', 'neqEquiv');
   },
   simplifier: true,
  },

  {statement: 'x ** 3 = 0 == x = 0',
   name: 'x3',
   proof: function() {
     return (rules.consider('x ** 3 = 0')
             .rewrite('x ** 3', rules.fact('prevPower'))
             .andThen('simplifySite', '3 - 1')
             .rewrite('x ** 2 * x = 0', 'zeroProduct')
             .andThen('simplifySite', '/right/right')
            );
   },
   simplifier: true,
  },

  {statement: 'x ** 3 != 0 == x != 0',
   proof: function() {
     return rules.fact('x3').rewrite('/main', 'neqEquiv');
   },
   simplifier: true,
  },

  {statement: 'x ** 4 = 0 == x = 0',
   name: 'x4',
   proof: function() {
     return (rules.consider('x ** 4 = 0')
             .rewrite('x ** 4', rules.fact('prevPower'))
             .andThen('simplifySite', '4 - 1')
             .rewrite('x ** 3 * x = 0', 'zeroProduct')
             .andThen('simplifySite', '/right/right')
            );
   },
   simplifier: true,
  },

  {statement: 'x ** 4 != 0 == x != 0',
   proof: function() {
     return rules.fact('x4').rewrite('/main', 'neqEquiv');
   },
   simplifier: true,
  },

  {statement: 'x ** 5 = 0 == x = 0',
   name: 'x5',
   proof: function() {
     return (rules.consider('x ** 5 = 0')
             .rewrite('x ** 5', rules.fact('prevPower'))
             .andThen('simplifySite', '5 - 1')
             .rewrite('x ** 4 * x = 0', 'zeroProduct')
             .andThen('simplifySite', '/right/right')
            );
   },
   simplifier: true,
  },

  {statement: 'x ** 5 != 0 == x != 0',
   proof: function() {
     return rules.fact('x5').rewrite('/main', 'neqEquiv');
   },
   simplifier: true,
  },

);

// MOVING EXPRESSIONS AROUND

declare(
   {statement: 'a = neg b == a + b = 0',
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
   {statement: 'a = b == a - b = 0',
    proof: function() {
      return rules.fact('a = neg b == a + b = 0')
      .andThen('instVar', 'neg b', 'b')
      .rewrite('/main/left/right', 'neg (neg a) = a')
      .rewrite('/main/right/left', '@a + neg b = a - b');
     },
   }
);


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
  const status = Toy.withExit(exit => {
    function mustBeVariable(expr, revPath) {
      if (expr.isVariable()) {
        var value = info[expr.name] || 0;
        info[expr.name] = value + 1;
      } else if (!expr.isConst()) {
        Toy.exitFrom(exit, false);
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
    return addCounts(term, Toy.Path.empty);
  });
  return status ? info : null;
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
 * (with their new operator), then this does so, and returns a proved
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
            var step3 = rules.rewriteFrom(step2, '/main/right/right', eqn);
            return step3;
          }
        }
      }
    }
  }
}


var ungroupingFacts = regroupingFacts.map(function(fact) {
    return Toy.commuteEqn(Toy.resolveToFact(fact));
  });

//// Inequalities

// Define further inequalities in terms of "<".
//
// These definitions are universal, for variables of all types.
//
// TODO: At some point work out definitions that apply only
//   to certain sorts.

definition('(>) = {x. {y. y < x}}');
definition('(<=) = {x. {y. x < y | x = y}}');
definition('(>=) = {x. {y. x > y | x = y}}');

declare
  (
   {statement: 'R pi', axiom: true,
    description: 'Pi is a real number'},

   {statement: '0 < pi', axiom: true,
    description: 'Pi is a positive number'},

   {statement: '0 != pi',
    proof: function() {
       return (rules.fact('@R x & x < y => x != y')
               .andThen('instMultiVars', {x: '0', y: 'pi'})
               .andThen('rewrite', '0 < pi', '0 < pi'));
     }
   },

   {statement: 'pi != 0',
    proof: function() {
       return (rules.fact('0 != pi')
               .andThen('rewrite', '0 != pi', 'x != y == y != x'));
     }
   }
  );


//// Misc utilities

// A function that takes a boolean term as input and returns 1 if it
// is true, otherwise 0.
definition('true1 = {a. if a 1 0}');

//// Export public names.

Toy.distribFacts = distribFacts;
Toy.isDistribFact = isDistribFact;
Toy.termGetRightVariable = termGetRightVariable;
Toy.varFactorCounts = varFactorCounts;
Toy.termLeftThan = termLeftThan;
Toy.tryArithmetic = tryArithmetic;
Toy.isArithmetic = isArithmetic;


// From here is overall initialization for the complete system.

// This is an easy way to get arithRight into the list of simplifiers.
basicSimpFacts.push({apply: arithRight});

// For testing (computed value).
Toy._ungroupingFacts = ungroupingFacts;

})();
