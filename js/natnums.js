// Copyright Crispin Perdue.  All rights reserved.

'use strict';

// Set everything up immediately on load, avoiding changes to
// the global environment except through namespace "Toy".
+function() {

const assert = Toy.assertTrue;

const abort = Toy.abort;
const format = Toy.format;
const dom = Toy.dom;
const TermSet = Toy.TermSet;
const rules = Toy.rules;
const declare = Toy.declare;
const definition = Toy.definition;
const Expr = Toy.Expr;
const Atom = Toy.Atom;
const Call = Toy.Call;
const Lambda = Toy.Lambda;

Toy.exercise(
  'nat',

  // NN axioms; 1
  {statement: '@NN 0', axiom: true,
   simplifier: true,
   description: 'axiom: zero is a natural number'
  },

  // 2
  {statement: '@NN n => NN (succ n)', axiom: true,
   description: 'axiom: successor is closed over the natural numbers'
  },
  {statement: '@NN n => NN (succ n) == T',
   proof: function() {
     return (rules.fact('@NN n => NN (succ n)')
             .andThen('rewriteOnly', '', 'a == (a == T)'));
   }
  },

  // 3
  {statement: '@NN n & NN m & succ m = succ n => m = n', axiom: true,
   name: 'succInjective',
   description: 'if successors of two numbers are equal, the numbers are equal'
  },
  {statement: '@NN n & NN m & succ m = succ n => (m = n == T)', axiom: true,
   proof: function() {
     return rules.fact('succInjective')
       .andThen('rewriteOnly', '', 'a => b == a => (b == T)');
   }
  },

  // 4
  {statement: '@NN n => succ n != 0', axiom: true,
   description: 'axiom: zero is not a successor'
  },

  // 5 (induction)
  {statement: '@P 0 & (P n => P (succ n)) => (NN x => P x)', axiom: true,
   name: 'induction',
   description: 'axiom: induction for natural numbers'
  },
  {statement: '@P 0 & (P n => P (succ n)) & NN x => P x',
   name: 'induction2',
   description: 'convenient statement of induction for natural numbers',
   proof: `(1 induction)
           (2 rewriteOnly (s 1) (path "")
             (t (a => (b => c) == (a & b => c))))`},

  //
  // Recursive "definition" of "+":
  //

  {statement: '@NN a => a + 0 = a', axiom: true,
   simplifier: true,
  },
  {statement: '@NN a & NN d => a + succ d = succ (a + d)', axiom: true},

  {definition: '1 = succ 0', labels: 'basic'},

  // Tactics

  // Tactic.  Target is a boolean term with an individual variable to
  // try induction on.
  {name: 'induct',
   menuGen: function(ruleName, step, term, proofEditor) {
     if (term) {
       const path = step.prettyPathTo(term);
       const localFrees = term.freeVarSet();
       const items = [];
       for (const name of localFrees) {
         if (rules.induct.precheck(step.original, path, name)) {
           // TODO: Consider checking with the editor whether the goal
           //   says the variable could be NN.
           items.push({ruleName: ruleName,
                       ruleArgs: [step.original, path, name],
                       html: `  induction on ${name}`
                      });
         }
       }
       return items;
     }
   },
   // The term must be a boolean Call, the variable occurring free in
   // the term and globally free in the step.
   precheck: function(step, path_arg, v) {
     const path = step.asPath(path_arg);
     const term = step.get(path);
     if (term instanceof Call && term.isBoolean()) {
       const frees = term.freeVarsMap();
       const vbl = frees.get(v);
       /* Consider including these lines, which should probably
          also allow the type to be a type variable.
       if (!vbl || vbl.type !== Toy.individual) {
         return false;
       }
       */
       const pth = path.uglify(step.implies());
       const bindings = step.pathBindings(pth);
       if (bindings.has(v)) {
         return false;
       }
       return true;
     }
     return false;
   },
   action: function(step, path_arg, name) {
     const path = step.asPath(path_arg);
     const asm = step.get(path);

     // This equates a lambda call to the asm.
     const reducer = rules.axiom4(Toy.call(Toy.lambda(name, asm), name));
     // This replaces the assumption with the lambda call.
     const step2 = rules.r1(step, path, rules.eqnSwap(reducer));
     // Apply the induction2 fact to the modified assumption.
     // Do not reduce introduced lambdas.
     const step3 = rules.rewriteOnly(step2, path, 'induction2', false);
     // This has effect much like using plain rewrite in step3.
     const step4 = rules.simplifyAsms(step3);
     return rules.reduceAll(step4, '').justify('induct', arguments, [step]);
   },
   inputs: {site: 1},
   menu: 'induction on {term}',
   description: 'set up induction',
  },

  // Theorems

  {statement: 'exists NN',
   proof: function() {
     return (rules.fact('p x => exists p')
             .andThen('instMultiVars', {x: '0', 'p': 'NN'})
             .andThen('simplifySite', ''));
   }
  },

  {statement: '@NN n & NN m => (succ m = succ n => m = n)',
   proof: function() {
     return (rules.fact('@NN n & NN m & succ m = succ n => m = n')
             .andThen('extractHyp', 'succ m = succ n'));
   }
  },

  {statement: '@NN n => (succ n = 0 == F)',
   proof: function() {
     return (rules.fact('@NN n => succ n != 0')
             .andThen('rewrite', '/main', 'x != y == not (x = y)')
             .andThen('rewrite', '/main', 'not a == (a == F)'));
   }
  },

  // The exercises:

  {exertion: 'nat0', statement: '0 = 0'},

  {exertion: 'nat0.2',
   statement: 'f x = y & f y = z => z = f (f x)'},

  {exertion: 'nat0.3',
   statement: 'y = f x & z = f y => z = f (f x)',
  },

  {exertion: 'nat0.5', statement: '@NN (succ (succ 0))'},

  {exertion: 'nat0.6',
   statement:
   '@NN m & NN n & succ (succ (succ n)) = succ (succ m) => succ n = m'},

  {exertion: 'nat0.7',
   statement: '@NN m & NN n & succ m = succ (succ n) => succ n = m'},

  {exertion: 'nat0.8',
   statement:
   '@succ i = j & succ j = k => k = succ (succ i)'},

  {exertion: 'nat1',
   statement: '0 = x => x = 0'},

  {statement: '@succ a = b => succ (succ a) = succ b',
   proof:
   `(1 tautologous
      (t (((succ (succ a)) = (succ b)) => ((succ (succ a)) = (succ b)))))
    (2 rewrite (s 1) (path "/left") (t ((x = y) => (((f x) = (f y)) == T))))`},
  {exertion: 'nat2'},

  {statement: '@NN n => n + succ 0 = succ n',
   proof: `(1 tautologous
              (t (((NN n) & ((n + (succ 0)) = (succ n)))
                  => ((n + (succ 0)) = (succ n)))))
           (2 rewrite (s 1) (path "/left/right/left")
              (t (((NN n) & (NN d)) => ((n + (succ d)) = (succ (n + d))))))
           (3 rewrite (s 2) (path "/left/left/left/left/arg")
              (t ((NN n) => ((n + 0) = n))))
           (4 rewrite (s 3) (path "/left/left/left") (t ((x = x) == T)))
           (5 rewrite (s 4) (path "/left/left") (t (NN 0)))`},
  {exertion: 'nat4'},
  
  {statement: '@NN n => 0 + n = n',
   proof: `(1 goal (t ((0 + n) = n)))
           (2 induct (s 1) (path "/left") "n")
           (3 simplifySite (s 2) (path "/left/right"))
           (4 rewrite (s 3) (path "/left/right") (t (NN 0)))
           (5 rewrite (s 4) (path "/left/right/right/left")
              (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
           (6 rewrite (s 5) (path "/left/left/right")
              (t (((x = y) => ((f x) = (f y))) == T)))
           (7 rewrite (s 6) (path "/left/right") (t (NN 0)))`,
   simplifier: true,
  },
  {exertion: 'add1'},

  {statement: '@NN a & NN b => NN (a + b)',
   proof: `(1 goal (t (NN (a + b))))
           (2 induct (s 1) (path "/left") "b")
           (3 rewrite (s 2) (path "/left/left/right/right/arg")
              (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
           (4 rewrite (s 3) (path "/left/left/left/left/right")
              (t (((NN n) => (NN (succ n))) == T)))
           (5 rewrite (s 4) (path "/left/left/left/right/arg")
              (t ((NN a) => ((a + 0) = a))))
           (6 removeTypeAsm (s 5) (path "/left/right"))`},
  {exertion: 'add1.5'},

  {statement: '@NN x & NN y & NN z => (x + y) + z = x + (y + z)',
   proof:
   `(1 tautologous
      (t ((((x + y) + z) = (x + (y + z))) => (((x + y) + z) = (x + (y + z))))))
    (2 induct (s 1) (path "/left") "z")
    (3 rewrite (s 2) (path "/left/right/right/right")
      (t ((NN x) => ((x + 0) = x))))
    (4 rewrite (s 3) (path "/left/left/left/left/left")
      (t ((NN x) => ((x + 0) = x))))
    (5 rewrite (s 4) (path "/left/left/left/left/left") (t ((x = x) == T)))
    (6 rewrite (s 5) (path "/left/left/left/left/right/right/right")
      (t (((NN x) & (NN d)) => ((x + (succ d)) = (succ (x + d))))))
    (7 rewrite (s 6) (path "/left/left/left/left/left/right/right")
      (t (((NN x) & (NN d)) => ((x + (succ d)) = (succ (x + d))))))
    (8 rewrite (s 7) (path "/left/left/left/left/left/left/left/right/left")
      (t (((NN x) & (NN d)) => ((x + (succ d)) = (succ (x + d))))))
    (9 rewrite (s 8) (path "/left/left/left/left/left/left/left")
      (t (((x = y) => ((f x) = (f y))) == T)))
    (10 rewrite (s 9) (path "/left/left/left/left/left/right")
      (t (((NN x) & (NN y)) => (NN (x + y)))))
    (11 rewrite (s 10) (path "/left/left/left/left/left")
      (t (((NN x) & (NN y)) => (NN (x + y)))))
    (12 removeTypeAsm (s 11) (path "/left/right"))`},
  {exertion: 'add2'},

  {exertion: 'add3',
   statement: '@NN x & NN y => succ x + y = succ (x + y)'
  },

  {exertion: 'add4',
   statement: '@NN x & NN y => x + y = y + x'
  },

  {statement: '1 = succ 0', axiom: true, labels: 'basic'},

  {exertion: 'add5',
   statement: '@NN n => succ n = n + 1'
  },

  {exertion: 'add6',
   statement: '@NN x & NN y & NN z => x + y + z = x + z + y'
  },

  {exertion: 'addx4',
   statement: '@NN x & NN y => (succ x = succ y == x = y)',
   proof:
   `(1 goal (t (((succ x) = (succ y)) == (x = y))))
    (2 rewrite (s 1) (path "/left") (t ((a == b) == ((a => b) & (b => a)))))
    (3 rewrite (s 2) (path "/left/left")
      (t (((NN n) & (NN m)) => (((succ m) = (succ n)) => (m = n)))))
    (4 rewrite (s 3) (path "/left/left/left")
      (t (((x = y) => ((f x) = (f y))) == T)))`
  },

  {exertion: 'addx8',
   statement: '@NN x & NN y => (x + y = 0 => y = 0)',
   proof:
   `(1 goal (t (((x + y) = 0) => (y = 0))))
    (2 induct (s 1) (path "/left") "y")
    (3 rewrite (s 2) (path "/left/left/right/right/left/left")
       (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
    (4 rewrite (s 3) (path "/left/left/left/left/right/right/left")
       (t ((NN n) => (((succ n) = 0) == F))))
    (5 simplifySite (s 4) (path "/left"))
    (6 rewrite (s 5) (path "/left/right")
       (t (((NN a) & (NN b)) => (NN (a + b)))))
    (7 removeTypeAsm (s 6) (path "/left/left/right"))`
  },

  {exertion: 'addxbonus',
   statement: '@NN x & NN y => (x + y = 0 == x = 0 & y = 0)'
  },

  {exertion: 'CountryMusic',
   statement:
   'forall {x. Rock x | Country x} & exists {x. not (Rock x)} \
     => exists {x. Country x}',
   proof:
   `(1 goal (t (exists {x. (Country x)})))
    (2 rewrite (s 1) (path "/left")
       (t (((forall {x. ((p x) => (q x))}) & (exists p)) => (exists q))))
    (3 matchTerm (s 2) (path "/left/left")
       (t (exists {x. (not (Rock x))})))
    (4 rewrite (s 3) (path "/left/right/arg/body")
       (t (((not a) => b) == (a | b))))`,
  },

  {exertion: 'CountryForward',
   statement:
   'forall {x. Rock x | Country x} & exists {x. not (Rock x)} \
     => exists {x. Country x}'
  },
);

  /*
(steps
(1 goal (t (((x + y) = 0) == ((x = 0) & (y = 0)))))
(2 rewrite (s 1) (path "/left") (t ((a == b) == ((a => b) & (b => a)))))
(3 assumePart (s 2) (path "/left/left/right"))
(4 assumePart (s 2) (path "/left/left/left/left"))
(5 rewriteFrom (s 3) (path "/left/left/left") (s 4))
(6 rewriteFrom (s 5) (path "/left/left/left/right") (s 4))
(7 simplifySite (s 6) (path "/left/left/left"))
(8 rewrite (s 7) (path "/left/right") (t (NN 0)))
(9 rewrite (s 8) (path "") (t (a == (a == T))))
(10 rewriteFrom (s 2) (path "/left/left") (s 9))
(11 assumePart (s 10) (path "/left/right"))
(12 fact "@NN x & NN y => (x + y = 0 => y = 0)")
(13 andAssume (s 12) (t ((x + y) = 0)))
(14 assumed (s 13) (path "/right/left"))
(15 simplifySite (s 14) (path "/right"))
(16 rewrite (s 15) (path "/right") (t (a == (a == T))))
(17 display (s 16))
(18 rewriteFrom (s 11) (path "/left/right") (s 17))
(19 rewrite (s 17) (path "") (t (a == (a == T))))
(20 assumeExplicitly (t (((((y + x) = 0) & (NN y)) & (NN x)) => ((x = 0) == T))))
(21 rewriteFrom (s 20) (path "/left") (s 19))
(22 rewriteFrom (s 18) (path "/left/left/left/right") (s 21))
(23 rewrite (s 22) (path "/left/left/left/right/left") (t (((NN x) & (NN y)) => ((x + y) = (y + x)))))
(24 extractHyp (s 23) (t ((x + y) = 0)))
(25 rewriteFrom (s 10) (path "/left") (s 24))
)
*/
// Define 1 = succ 0

// Addition World levels:  

// 1: 0 + n = n                  (zero_add) (induction on n) add1
// 2: (a + b) + c = a + (b + c)  (add_assoc) (induction on c) add2
// 3: succ a + b = succ (a + b)  (succ_add) (induction on b)
// 4: a + b = b + a           (add_comm) (induction on b)
// 5: succ n = n + 1          (succ_eq_add_one)
// 6: a + b + c = a + c + b   (add_right_comm)

// Advanced Addition World levels:

// (1. succ_inj -- axiom for us)
// 2. succ (succ a) = succ (succ b) => a = b (not interesting)
// 3. a = b => succ a = succ b (explained in first induction proof)
// 4. succ a = succ b == a = b (uses biconditional)
// 5. a + t = b + t => a = b (induction on t)
// 6. t + a = t + b => a = b (boring?)
// 7. a + t = b + t == a = b (also boring?)
// 8. a + b = a => b = 0
// 9. 0 != succ a (just symmetry)
// 10. a + b = 0 => b = 0 (probably give some hints, uses cases)
// 11. a + b = 0 => a = 0 (add_comm)
// 12. d + 1 = succ d  (just symmetry)
// 13. n != succ n   (by induction)

// And this is the end of Advanced Addition World!

}();
