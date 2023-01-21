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

declare(
  // {theory: 'nat'},
  {statement: 'NN zero', axiom: true,
   description: 'zero is a natural number'
  },
  {statement: 'NN n => NN (succ n)', axiom: true,
   description: 'successor is closed over the natural numbers'
  },
  {statement: 'NN n & NN m & succ m = succ n => m = n', axiom: true,
   description: 'if successors of two numbers are equal, the numbers are equal'
  },
  {statement: 'NN n => zero != succ n', axiom: true,
   description: 'zero is not a successor'
  },
  {statement: 'P zero & (P n => P (succ n)) => (NN x => P x)', axiom: true,
   description: 'induction over the natural numbers'
  }
);

}();
