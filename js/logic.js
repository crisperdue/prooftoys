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

const identity = Toy.parse('{x. x}');
const allT = Toy.parse('{x. T}');

//// Rules needed to support definition

// simpleApply
// applyBoth

//// Definitions

define('not', '(=) F');
define('!=', '{x. {y. not (x = y)}}');
define('forall', '(=) {x. T}');
define('exists', '{p. p != {x. F}}');
define('exists1', '{p. exists {x. p = {y. y = x}}}');
defineCases('&', identity, '{x. F}');
defineCases('|', allT, identity);
defineCases('=>', identity, allT);

}();
  
