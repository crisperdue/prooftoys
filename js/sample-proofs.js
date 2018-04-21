// Copyright 2011, 2012, 2013, 2014, 2015 Crispin Perdue.
// All rights reserved.

// Do the initializations here using the "$" function so that
// initialization of the Prooftoys engine can be completed first.
// (They also use "$", with handlers established before this one.)
$(function() {
  // Set up some useful constants and functions.

  // For convenience.
  var rules = Toy.rules;
  var infixCall = Toy.infixCall;
  var call = Toy.call;
  var equal = Toy.equal;
  var implies = Toy.implies;
  var lambda = Toy.lambda;

  var varify = Toy.varify;
  var a = varify('a');
  var b = varify('b');
  var c = varify('c');
  var x = varify('x');
  var y = varify('y');
  var z = varify('z');
  var f = varify('f');
  var g = varify('g');
  var h = varify('h');
  var p = varify('p');
  var q = varify('q');
  var r = varify('r');
  var T = Toy.constify('T');
  var F = Toy.constify('F');

  // Node of dropdown control.
  var selector;

  // Container node to hold the proof display.
  var proofNode;

  function selectorChanged() {
    var options = selector.options;
    var ruleName = options[selector.selectedIndex].value;
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
      $(proofNode).html('');
      if (result) {
        Toy.renderProof(result, proofNode, elapsed, nSteps);
      } else if (Toy.errors.length) {
        var last = Toy.errors[Toy.errors.length - 1];
        $(proofNode).append('<p><b>Errors: (' + Toy.errors.length
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

    proofNode = $(displayId)[0];

    // You can control which rule is displayed by including
    // "rule=<ruleName>" in the query string.
    var queryRuleName = Toy.queryParams.rule;
    // You can make the displays label steps with their ordinals
    // using ordinals=1 in the query string.
    Toy.showOrdinals = Toy.queryParams.ordinals;
    editable = Toy.queryParams.edit != undefined;
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
        var display = info.menu || info.tooltip || name;
        selectorHtml +=
          '<option value="' + name + '"' + selected + '>' + display + '\n';
      }
    }
    selectorHtml += '</select>';
    selector = $(selectorHtml)[0];
    $(selectorId).empty();
    $(selectorId).append(selector);
    $(selector).on('change', selectorChanged);
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

    // TODO: Use this in other examples.
    bindEqn: {
      args: [rules.assert(call('=', f, g)), x],
      level: 1
    },
    
    applyBoth: {
      args: [rules.assert(call('=', f, g), x)],
      level: 1
    },

    eqnSwap: {
      args: [rules.axiom4(Toy.parse('{x. x} (p = q)'))],
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

    r5211Unbook: {},
    
    t: {},
    
    r5212: {},
    
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
        return [step1, '/right', call(f, x)];
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
    
    toForall0: {
      args: [rules.assert(call(p, y)), y],
      level: 1
    },
    
    instVar: {
      args: [rules.assert(call(p, y)), call(f, x), y],
      level: 1
    },

    instMultiVars: {
      args: [rules.eqSelf('x + y'),
             {x: Toy.parse('x * y'),
              y: Toy.parse('x / y')}
             ],
      level: 1
    },
    
    instMultiVars2: {
      ruleName: 'instMultiVars',
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

    casesTF: {
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
        var step2 = Toy.rules.assume('p => q');
        return [step1, step2];
      },
      level: 1
    },

    r5225: {},

    r5227: {},

    r5230FTBook_almost: {},

    r5230FT_alternate: {},
    
    r5231T: {},
    
    r5231F: {},
    
    falseEquals: {},
    
    trueEquals: {},
    
    evalBool: {
      args: [call('=>',
                  call('=>', F, call('not', F)),
                  call('not', F))]
    },
    
    tautology: {
      /* This tautology is already an equation, let's test one that is not.
      args: [equal(call('=>', call('&', p, q), r),
                   call('=>', p, call('=>', q, r)))],
      */
      args: [Toy.parse('(p => q) & (not p => q) => q')],
      level: 1
    },
    
    tautInst: {
      args: [Toy.parse('p => T | q'), ({
        p: Toy.parse('forall {x. T | p x}'),
        q: Toy.parse('forall {x. p x}')
      })],
      level: 1
    },


    r5235: {
      args: [x, p, call(q, x)]
    },

    implyForallGen: {
      args: [x, p, call(q, x)]
    },

    implyForallNoHyps: {
      ruleName: 'implyForall',
      args: [x, rules.assert(Toy.parse('p => q x'))],
    },

    implyForall: {
      args: function() {
        var step1 = Toy.rules.assume('y > 0');
        var step2 = Toy.rules.assert('y > 0 => (p => q x)');
        var step3 = Toy.rules.modusPonens(step1, step2);
	return [x, step3];
      },
      level: 1
    },

    /*
    implyForallBookHyps: {
      ruleName: 'implyForallBook',
      args: function() {
	var wff = Toy.parse('y > 0 => (p => q x)');
        wff.hasHyps = true;
	return [x, wff];
      },
    },
    */

    forwardChain: {
      args: function() {
        var step1 = Toy.rules.assume('p x');
        var step2 = Toy.rules.assume('p x => q x');
        var step3 = Toy.rules.makeConjunction(step1, step2);
        var step4 = Toy.rules.tautology('a & (a => b) => b');
        return [step3, step4];
      },
      level: 1
    },

    r5238a: {
      args: [y, call(p, y), call(q, y)]
    },

    r5238: {
      args: [['y', 'z'], Toy.parse('y < z'), Toy.parse('z < y')]
    },

    r5239: {
      args: [lambda(p, equal(q, p)), '/body/right', equal(p, q)]
    },

    replace: {
      args: function() {
        var step1 = Toy.rules.assume('x >= 0');
        var step2 = Toy.rules.assert('x >= 0 => (x = (abs x))');
        var step3 = Toy.rules.modusPonens(step1, step2);
        var step4 = Toy.rules.assert('x >= 0 => (x + x) >= x');
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

});
