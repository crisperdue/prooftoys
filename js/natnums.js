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

  {statement: '@NN 0', axiom: true,
   simplifier: true,
   description: 'zero is a natural number'
  },
  {exertion: 'nat0'},
  {statement: '@NN n => NN (succ n)', axiom: true,
   description: 'successor is closed over the natural numbers'
  },
  {statement: '@NN n => NN (succ n) == T',
   proof: function() {
     return (rules.fact('@NN n => NN (succ n)')
             .andThen('rewriteOnly', '', 'a == (a == T)'));
   }
  },
  {statement: '@NN n & NN m & succ m = succ n => m = n', axiom: true,
   description: 'if successors of two numbers are equal, the numbers are equal'
  },
  {statement: '@NN n => 0 != succ n', axiom: true,
   description: 'zero is not a successor'
  },
  {statement: '@P 0 & (P n => P (succ n)) => (NN x => P x)', axiom: true,
   name: 'induction',
   description: 'induction for natural numbers'
  },
  {statement: '@P 0 & (P n => P (succ n)) & NN x => P x',
   name: 'induction2',
   proof: `(1 induction)
           (2 rewriteOnly (s 1) (path "") (t (a => (b => c) == (a & b => c))))`},


  // Recursive definition of "+":
  {statement: '@NN a => a + 0 = a', axiom: true},
  {statement: '@NN a & NN d => a + succ d = succ (a + d)', axiom: true},

  {definition: '1 = succ 0'},

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

  // Target is a boolean term with an individual variable to try
  // induction on.
  {name: 'induct',
   menuGen: function(ruleName, step, term, proofEditor) {
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

  {statement: '@x + y = x + y',
   proof: `(1 goal (t x + y = x + y))
           (2 rewrite (s 1) (path "/left") (t ((x = x) == T)))`
  },
  {exertion: 'nat1'},

  {statement: '@NN a & NN b & succ a = b => succ (succ a) = succ b',
   proof:
   `(1 tautologous
      (t (((succ (succ a)) = (succ b)) => ((succ (succ a)) = (succ b)))))
    (2 rewrite (s 1) (path "/left") (t ((x = y) => (((f x) = (f y)) == T))))`},
  {exertion: 'nat2'},

  {statement: '@NN a => a + succ 0 = succ a',
   proof: `(1 tautologous
              (t (((NN a) & ((a + (succ 0)) = (succ a)))
                  => ((a + (succ 0)) = (succ a)))))
           (2 rewrite (s 1) (path "/left/right/left")
              (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
           (3 rewrite (s 2) (path "/left/left/left/left/arg")
              (t ((NN a) => ((a + 0) = a))))
           (4 rewrite (s 3) (path "/left/left/left") (t ((x = x) == T)))
           (5 rewrite (s 4) (path "/left/left") (t (NN 0)))`},
  {exertion: 'nat4'},
  
  {statement: '@NN a => 0 + a = a',
   proof: `(1 tautologous (t (((0 + a) = a) => ((0 + a) = a))))
           (2 induct (s 1) (path "/left") "a")
           (3 rewrite (s 2) (path "/left/left/left/right/left")
             (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
           (4 rewrite (s 3) (path "/left/left/left/left/left/left")
             (t ((NN a) => ((a + 0) = a))))
           (5 rewrite (s 4) (path "/left/left/left/left/left")
             (t ((x = x) == T)))
           (6 rewrite (s 5) (path "/left/left/left/left")
             (t (((x = y) => ((f x) = (f y))) == T)))
           (7 rewrite (s 6) (path "/left/left/left") (t (NN 0)))
           (8 removeTypeAsm (s 7) (path "/left/right"))`},
  {exertion: 'add1'},

  {statement: '@NN a & NN b => NN (a + b)',
   proof: `(1 tautologous (t ((NN (a + b)) => (NN (a + b)))))
           (2 induct (s 1) (path "/left") "b")
           (3 rewrite (s 2) (path "/left/left/left/right/arg")
             (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
           (4 rewrite (s 3) (path "/left/left/left/left/right/arg")
             (t ((NN a) => ((a + 0) = a))))
           (5 rewrite (s 4) (path "/left/left/left/left")
             (t (((NN n) => (NN (succ n))) == T)))
           (6 removeTypeAsm (s 5) (path "/left/right"))`},
  {exertion: 'add1.5'},

  {statement: '@NN a & NN b & NN c => (a + b) + c = a + (b + c)',
   proof:
   `(1 tautologous
      (t ((((a + b) + c) = (a + (b + c))) => (((a + b) + c) = (a + (b + c))))))
    (2 induct (s 1) (path "/left") "c")
    (3 rewrite (s 2) (path "/left/right/right/right")
      (t ((NN a) => ((a + 0) = a))))
    (4 rewrite (s 3) (path "/left/left/left/left/left")
      (t ((NN a) => ((a + 0) = a))))
    (5 rewrite (s 4) (path "/left/left/left/left/left") (t ((x = x) == T)))
    (6 rewrite (s 5) (path "/left/left/left/left/right/right/right")
      (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
    (7 rewrite (s 6) (path "/left/left/left/left/left/right/right")
      (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
    (8 rewrite (s 7) (path "/left/left/left/left/left/left/left/right/left")
      (t (((NN a) & (NN d)) => ((a + (succ d)) = (succ (a + d))))))
    (9 rewrite (s 8) (path "/left/left/left/left/left/left/left")
      (t (((x = y) => ((f x) = (f y))) == T)))
    (10 rewrite (s 9) (path "/left/left/left/left/left/right")
      (t (((NN a) & (NN b)) => (NN (a + b)))))
    (11 rewrite (s 10) (path "/left/left/left/left/left")
      (t (((NN a) & (NN b)) => (NN (a + b)))))
    (12 removeTypeAsm (s 11) (path "/left/right"))`},
  {exertion: 'add2'},

// Define 1 = succ 0

// 1: 0 + n = n                  (zero_add) (induction on n) add1
// 2: (a + b) + c = a + (b + c)  (add_assoc) (induction on c) add2
// 3: succ a + b = succ (a + b)  (succ_add) (induction on b)
// 4: a + b = b + a           (add_comm) (induction on b)
// 5: succ n = n + 1          (succ_eq_add_one)
// 6: a + b + c = a + c + b   (add_right_comm)

);

}();
