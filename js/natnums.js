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
  {statement: 'exists NN',
   proof: function() {
     return (rules.fact('p x => exists p')
             .andThen('instMultiVars', {x: '0', 'p': 'NN'})
             .andThen('simplifySite', ''));
   }
  },
  {statement: '@NN n => NN (succ n) == T',
   proof: function() {
     return (rules.fact('@NN n => NN (succ n)')
             .andThen('rewriteOnly', '', 'a == (a == T)'));
   }
  },
  {statement: '@NN n & NN m => (succ m = succ n => m = n)',
   proof: function() {
     return (rules.fact('@NN n & NN m & succ m = succ n => m = n')
             .andThen('extractHyp', 'succ m = succ n'));
   }
  },

  // Uses a selected variable occurrence within an assumption.
  {name: 'induct3',
   precheck: function(step, path_arg) {
     const path = step.asPath(path_arg);
     if (!step.implies() && path.isLeft()) {
       return false;
     }
     const vbl = step.get(path);
     if (!vbl.isVariable()) {
       return false;
     }
     const name = vbl.name;
     if (step.wff.pathBindings(path.uglify(step.implies())).has(name)) {
       return false;
     }
     const asmsByPath = step.wff.asmMap();
     const here = step.wff.prettifyPath(path);
     let asm = null;
     let pstr;
     for (pstr of asmsByPath.keys()) {
       const pth = Toy.asPath(pstr);
       if (here.remainder(pth)) {
         asm = asmsByPath.get(pstr);
         break;
       }
     }
     if (!asm) {
       return false;
     }
     return {asm: asm, asmPath: Toy.asPath(pstr)};
   },
   action: function(step, path) {
     const vbl = step.get(path);
     const name = vbl.name;
     const {asm, asmPath} = Toy._actionInfo;

     // This equates a lambda call to the asm.
     const reducer = rules.axiom4(Toy.call(Toy.lambda(name, asm), name));
     // This replaces the assumption with the lambda call.
     const step2 = rules.r1(step, asmPath, rules.eqnSwap(reducer));
     // Apply the induction2 fact to the modified assumption.
     // Do not reduce introduced lambdas.
     const step3 = rules.rewriteOnly(step2, asmPath, 'induction2', false);
     // This has effect much like using plain rewrite in step3.
     const step4 = rules.simplifyAsms(step3);
     return rules.reduceAll(step4, '').justify('induct3', arguments, [step]);
   },
   inputs: {site: 1},
   menu: 'induction on {term}',
   description: 'set up induction',
  },

  // Induction on a variable; if given, the name, otherwise the
  // rightmost name declared/assumed to be NN.  It is possible to
  // induct on non-variable terms, but this does not handle that.
  // This takes the selection as the term to convert to application of
  // the lambda predicate to the desired induction variable.
  {name: 'induct2',
   precheck: function(step, path, name=null) {
     return false;  // XXX
     const term = step.get(path);
     // Slightly better than checking "sameAs" would be to check
     // whether the path is appropriate for an assumption.
     const asms = step.getAsms();
     return (term instanceof Call && asms &&
             asms.scanConj(t => t.sameAs(term)) &&
             term.freeVarSet().size > 0);
     // XXX also find and check the name if not given.
   },
   toOffer: function(step, term) {
     return true;  // XXX
     const path = step.prettyPathTo(term);
     // XXX Put this in menuGen, which has the needed information.
     return step.asmMap().has(path.toString());
   },
   action: function(step, path, name_arg=null) {
     const term = step.get(path);
     const findName = () => {
       let v = null;
       step.asmSet().scanConj(t => {
         const map = t.matchSchema('NN x');
         if (map && map.x.isVariable()) {
           v = map.x;
         }
       });
       return v && v.name;
     };
     const name = name_arg || findName();
     assert(name, 'No variable for induction');

     const reducer = rules.axiom4(Toy.call(Toy.lambda(name, A), name));
     const step2 = rules.r1(step, path, rules.eqnSwap(reducer));
     const step3 = rules.rewriteOnly(step2, '/left', 'induction2', false);
     // This has effect much like using plain rewrite in step2.
     const step4 = rules.simplifyAsms(step3);
     return rules.reduceAll(step4, '').justify('induct2', arguments, [step]);
   },
   inputs: {site: 1},
   menu: 'set up induction',
   description: 'set up induction',
  },

  {name: 'induct',
   precheck: function(step, path) {
     const term = step.get(path);
     return (term.matchSchema('NN x => P x') ||
             term.matchSchema('A & NN x => P x'));
    },
    action: function(step, path) {
      const term = step.get(path);
      const subst = (term.matchSchema('NN v => A') ||
                     term.matchSchema('A1 & NN v => A'));
      const {v, A} = subst;
      const reducer = rules.axiom4(Toy.call(Toy.lambda(v, A), v));
      const step2 = rules.r1(step, path.concat('/right'),
                             rules.eqnSwap(reducer));
      const step3 = rules.rewriteOnly(step2, '/left', 'induction', false);
      // This has effect much like using plain rewrite.
      const step4 = rules.simplifyAsms(step3);
      return rules.reduceAll(step4, '').justify('induct', arguments, [step]);
    },
    toOffer: (step, term) => step.implies() && step.prettyPathTo(term).isLeft(),
    inputs: {site: 1},
    menu: 'try induction',
   // labels: 'backward',
    description: 'apply induction',
  },

  // Target is a boolean term with an individual variable to try
  // induction on.
  {name: 'induct4',
   menuGen: function(ruleName, step, term, proofEditor) {
     const path = step.prettyPathTo(term);
     const localFrees = term.freeVarSet();
     const items = [];
     for (const name of localFrees) {
       if (rules.induct4.precheck(step.original, path, name)) {
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
       /*
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
     return rules.reduceAll(step4, '').justify('induct4', arguments, [step]);
   },
   inputs: {site: 1},
   menu: 'induction on {term}',
   description: 'set up induction',
  },

  {statement: '@x + 22 = x + 22',
   proof: `(1 assumeExplicitly (t ((x + 22) = (x + 22))))
           (2 rewrite (s 1) (path "/left") (t ((x = x) == T)))`},
  {exertion: 'nat1'},

  {statement: '@NN x & NN y & y = x + 7 => 2 * y = 2 * (x + 7)'},
  {exertion: 'nat2'},

  {statement: '@NN a & NN b & succ a = b => succ (succ a) = succ b'},
  {exertion: 'nat3'},

  // Recursive definition of "+":
  {statement: '@NN a => a + 0 = a', axiom: true},
  {statement: '@NN a & NN d => a + succ d = succ (a + d)', axiom: true},

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
  
  {statement: '@NN a => 0 + a = a'},
  {exertion: 'add1'},

  {statement: '@NN a & NN b => NN (a + b)'},
  {exertion: 'add1.5'},

  {statement: '@NN a & NN b & NN c => (a + b) + c = a + (b + c)'},
  {exertion: 'add2'},

// Define 1 = succ 0

// 1: 0 + n = n                  (zero_add) (induction on n)
// 2: (a + b) + c = a + (b + c)  (add_assoc) (induction on c)
// 3: succ a + b = succ (a + b)  (succ_add) (induction on b)
// 4: a + b = b + a           (add_comm) (induction on b)
// 5: succ n = n + 1          (succ_eq_add_one)
// 6: a + b + c = a + c + b   (add_right_comm)

);

}();
