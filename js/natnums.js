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

Toy.exercise(
  'nat',

  {statement: '@NN zero', axiom: true,
   description: 'zero is a natural number'
  },
  {exertion: 'nat0'},
  {statement: '@NN n => NN (succ n)', axiom: true,
   description: 'successor is closed over the natural numbers'
  },
  {statement: '@NN n & NN m & succ m = succ n => m = n', axiom: true,
   description: 'if successors of two numbers are equal, the numbers are equal'
  },
  {statement: '@NN n => zero != succ n', axiom: true,
   description: 'zero is not a successor'
  },
  {statement: '@P zero & (P n => P (succ n)) => (NN x => P x)', axiom: true,
   description: 'induction over the natural numbers'
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
  {statement: '@NN a => a + zero = a', axiom: true},
  {statement: '@NN a & NN d => a + succ d = succ (a + d)', axiom: true},

  {statement: '@NN a => a + succ zero = succ a'},
  {exertion: 'nat4'},
  
);

}();
