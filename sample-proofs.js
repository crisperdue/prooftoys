// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

YUI.add('sample-proofs', function(Y) {

  // Set up some useful constants and functions.

  // For convenience.
  var rules = Toy.rules;
  var infixCall = Toy.infixCall;
  var call = Toy.call;
  var equal = Toy.equal;
  var implies = Toy.implies;
  var lambda = Toy.lambda;

  var Var = Toy.Var;
  var a = new Var('a');
  var b = new Var('b');
  var c = new Var('c');
  var x = new Var('x');
  var y = new Var('y');
  var z = new Var('z');
  var f = new Var('f');
  var g = new Var('g');
  var h = new Var('h');
  var p = new Var('p');
  var q = new Var('q');
  var r = new Var('r');
  var T = new Var('T');
  var F = new Var('F');

  // Query string data.
  var queryData = Y.QueryString.parse(location.search.substring(1));

  // Node of dropdown control.
  var selector;

  // Container node to hold the proof display.
  var proofNode;

  function selectorChanged() {
    var selectorElt = Y.Node.getDOMNode(selector);
    var options = selectorElt.options;
    var ruleName = options[selectorElt.selectedIndex].value;
    displayProof(ruleName);
  }

  /**
   * Runs and displays a proof of the named rule (or theorem).
   * If there is no such rule, notifies the user that there is none.
   */
  function displayProof(name) {
    var ruleInfo = sampleProofs[name];
    if (ruleInfo == undefined) {
      alert('No example "' + name + '"');
    } else {
      var startMillis = new Date().getTime();
      var result;
      var ruleName = ruleInfo.ruleName || name;
      var args = ruleInfo.args;
      if (typeof args == 'function') {
        args = args();
      }
      var stepCounter = Toy.getStepCounter();
      try {
        result = Toy.rules[ruleName].apply(null, args || []);
      } catch(e) {
        console && console.log('Error in sample proof: ' + e);
      }
      var elapsed = new Date().getTime() - startMillis;
      // This is actually the number of steps needed to execute the
      // rule, not counting steps used in deriving argument steps.
      var nSteps = Toy.getStepCounter() - stepCounter;
      // For debugging.
      window.proved = result;
      proofNode.setContent('');
      if (result) {
        Toy.renderProof(result, proofNode, elapsed, nSteps);
      } else if (Toy.errors.length) {
        var last = Toy.errors[Toy.errors.length - 1];
        proofNode.append('<p><b>Errors: (' + Toy.errors.length
                         + ') ' + last.message + '</b></p>');
        if (last.step) {
          Toy.renderProof(last.step, proofNode);
        }
      }
    }
  }

  function setUpSampleProofs(selectorId, displayId, editable) {
    // Do we want sample proofs to be editable?
    // Controllable through the query string.
    editable = !!editable;

    proofNode = Y.one(displayId);

    // You can control which rule is displayed by including
    // "rule=<ruleName>" in the query string.
    var queryRuleName = queryData.rule;
    // You can make the displays label steps with their ordinals
    // using ordinals=1 in the query string.
    Toy.showOrdinals = queryData.ordinals;
    editable = queryData.edit != undefined;
    if (queryRuleName == undefined) {
      // Default to displaying instForall.
      queryRuleName = 'instForall';
    }
    displayProof(queryRuleName);
    var selectorHtml =
      '<select class=sampleSelector>\n<option value="">-- choose --';
    for (var name in sampleProofs) {
      if (name == queryRuleName || sampleProofs[name].level == 1) {
        var selected = (name == queryRuleName ? ' selected' : '');
        var sampleInfo = sampleProofs[name];
        var ruleName = sampleInfo.ruleName || name;
        var info = Toy.rules[ruleName].info;
        var display = info.hint || info.comment || name;
        selectorHtml +=
          '<option value="' + name + '"' + selected + '>' + display + '\n';
      }
    }
    selectorHtml += '</select>';
    selector = Y.Node.create(selectorHtml);
    Y.one(selectorId).setContent(selector);
    selector.on('change', selectorChanged);
  }

  // Map from example name to example configuration info, each of
  // which is also a map.  Configuration properties are:
  //
  // ruleName: name of the rule to run, defaults to the example name.
  // args: array of arguments to pass to the rule.  If a function, the
  //   function computes the arguments.
  // level: if 1 then offer this example in the dropdown control.
  var sampleProofs = {

    // PROOFS

    eqSelf: {
      args: [call(p, x)],
      level: 1
    },

    applyBoth: {
      args: [rules.assert(call('=', f, g), x)],
      level: 1
    },

    replaceWhole: {
      args: [rules.assert(call(p, x)),
             rules.assert(call('=', call(p, x), call(q, x)))],
    },

    eqnSwap: {
      args: [rules.assert(call('=', p, q))],
      level: 1
    },

    eqnChain: {
      args: [rules.assert(call('=', p, q)),
             rules.assert(call('=', q, r))],
    },

    applyBySides: {
      args: [rules.assert(call('=', p, q)),
             rules.assert(call('=', 'a', 'b'))]
    },
    
    applyBoth: {
      args: [rules.assert(call('=', p, q)), r],
      level: 1
    },
    
    applyToBoth: {
      args: [p, rules.assert(call('=', q, r))]
    },

    useDefinition: {
      args: [rules.assert(call('not', equal(p, call('not', p)))), '/fn'],
      level: 1
    },
    
    apply: {
      args: [rules.assert(equal(p, call(lambda(x, T), y))), '/right'],
      level: 1
    },

    changeVar: {
      args: [rules.assert(equal(lambda(z, z), lambda(z, z))), '/right', y],
      level: 1
    },

    bindEqn: {
      args: [rules.assert(call('=', f, g)), x],
    },
    
    instEqn: {
      args: [rules.assert(call('=', call(g, y), z)),
             call(f, x),
             y],
    },
    
    xAlwaysX: {},

    eqT: {
      args: [p]
    },
    
    r5211: {},

    r5211Book: {},
    
    t: {},
    
    r5212: {},
    
    r5212Book: {},
    
    toTIsEquation: {
      args: [rules.assert(call('=', p, q))]
    },
    
    r5213: {
      args: [rules.assert(call('=', p, q)),
             rules.assert(call('=', q, r))]
    },
    
    r5214: {},

    instForall: {
      args: function() {
        var step1 = rules.assume('forall {y. p y}');
        return [step1, call(f, x)];
      },
      level: 1
    },
    
    andTBook: {
      args: [p]
    },
    
    andT: {
      args: [p]
    },
    
    r5217Book: {},
    
    equationCases: {
      args: [rules.assert('T = p T'),
             rules.assert('T = p F'),
             'x']
    },

    r5218a: {},

    r5218: {
      args: [call(p, y)]
    },
    
    toTIsA: {
      args: [rules.assert(p)]
    },
    
    fromTIsA: {
      args: [rules.assert(call('=', T, p))]
    },
    
    addForall: {
      args: [rules.assert(call(p, y)), y],
      level: 1
    },
    
    instVar: {
      args: [rules.assert(call(p, y)), call(f, x), y],
      level: 1
    },
    
    instMultiVars: {
      args: [rules.assert(implies(p, call('|', T, q))),
             ({p: Toy.parse('forall {x. T | b}'),
               q: Toy.parse('forall {x. b}')
             })
            ],
      level: 1
    },

    makeConjunction: {
      args: function() {
        var step1 = Toy.rules.assume('p T');
        var step2 = Toy.rules.assume('p F');
        return [step1, step2];
      },
      level: 1
    },

    cases: {
      args: function() {
        var step1 = Toy.rules.assume('p T');
        var step2 = Toy.rules.assume('p F');
        return [step1, step2, 'x'];
      },
      level: 1
    },
    
    r5223: {},
    
    simpleModusPonens: {
      ruleName: 'modusPonens',
      args: [rules.assert(p), rules.assert(implies(p, q))],
      level: 1
    },
    
    modusPonens: {
      args: function() {
        var step1 = Toy.rules.assume('p');
        var step2 = Toy.rules.assume('p ==> q');
        return [step1, step2];
      },
      level: 1
    },

    r5225: {},

    r5227: {},

    r5230TF: {},
    
    r5230FT: {},
    
    r5230FTBook: {},

    r5230FT_alternate: {},
    
    r5231T: {},
    
    r5231F: {},
    
    falseEquals: {},
    
    trueEquals: {},
    
    evalBool: {
      args: [call('==>',
                  call('==>', F, call('not', F)),
                  call('not', F))]
    },
    
    tautology: {
      /* This tautology is already an equation, let's test one that is not.
      args: [equal(call('==>', call('&', p, q), r),
                   call('==>', p, call('==>', q, r)))],
      */
      args: [Toy.parse('(p ==> q) & (not p ==> q) ==> q')],
      level: 1
    },
    
    tautInst: {
      args: [Toy.parse('p ==> T | q'), ({
        p: Toy.parse('forall {x. T | p x}'),
        q: Toy.parse('forall {x. p x}')
      })],
      level: 1
    },


    r5235: {
      args: [x, p, call(q, x)]
    },

    implyForallThm: {
      args: [x, p, call(q, x)]
    },

    implyForallNoHyps: {
      ruleName: 'implyForall',
      args: [x, rules.assert(Toy.parse('p ==> q x'))],
    },

    implyForall: {
      args: function() {
        var step1 = Toy.rules.assume('y > 0');
        var step2 = Toy.rules.assert('y > 0 ==> (p ==> q x)');
        var step3 = Toy.rules.modusPonens(step1, step2);
	return [x, step3];
      },
      level: 1
    },

    implyForallBookHyps: {
      ruleName: 'implyForallBook',
      args: function() {
	var wff = Toy.parse('y > 0 ==> (p ==> q x)');
        wff.hasHyps = true;
	return [x, wff];
      },
    },

    forwardChain: {
      args: function() {
        var step1 = Toy.rules.assume('p x & (p x ==> q x)');
        var step2 = Toy.rules.tautology('a & (a ==> b) ==> b');
        return [step1, step2];
      },
      level: 1
    },

    r5238a: {
      args: [y, call(p, y), call(q, y)]
    },

    r5238: {
      args: [['x1', 'x2'], Toy.parse('p x1'), Toy.parse('p x2')]
    },

    r5239: {
      args: [equal(p, q), lambda(p, equal(q, p)), '/body/right']
    },

    replace: {
      args: function() {
        var step1 = Toy.rules.assume('x >= 0');
        var step2 = Toy.rules.assert('x >= 0 ==> (x = (abs x))');
        var step3 = Toy.rules.modusPonens(step1, step2);
        var step4 = Toy.rules.assert('x >= 0 ==> (x + x) >= x');
        var step5 = Toy.rules.modusPonens(step1, step4);
        return [step3, step5, '/main/right'];
      },
      level: 1
    },

    appendStepHyps: {
      args: function() {
        var step1 = Toy.rules.assume('p x');
        var step2 = Toy.rules.assume('q x');
        return [step1, step2];
      }
    },

    prependStepHyps: {
      args: function() {
        var step1 = Toy.rules.assume('p x');
        var step2 = Toy.rules.assume('q x');
        return [step1, step2];
      }
    },

    bubbleLeft: {
      args: function() {
        function less(a, b) {
          return a.toString() < b.toString();
        }
        return [Toy.rules.assert('lhs = (((b & a) & d) & a)'), less];
      }
    },

    mergeConjunctions: {
      ruleName: 'mergeConj',
      args: function() {
        function less(a, b) {
          return a.toString() < b.toString();
        }
        return [Toy.rules.assert('lhs = (a & b) & (c & d)'), less];
      }
    }

  };

Toy.setUpSampleProofs = setUpSampleProofs;

}, '0.1', {requires: ['array-extras', 'expr', 'proof']});
