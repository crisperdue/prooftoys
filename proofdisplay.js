/* Copyright 2011 Crispin Perdue.  All rights reserved.  */

YUI.add('proofdisplay', function(Y) {

  //
  // ProofArea -- UI widget for a full top-level proof.
  //
  // This contains a top-level proof, which in turn can contain
  // subproofs.  In particular this defines event handlers that
  // are shared among all proofs and subproofs in it.
  //

  // TODO: explicitly include the input text field as part of the
  // ProofArea.

  function ProofArea(id, valueTarget) {
    var node = new Y.Node(document.getElementById(id));
    this._node = node;
    this._proof =
      new ProofDisplay(node.appendChild('<div class=proof></div>'), this);
    this._selectedLine = null;
    this._valueTarget = valueTarget;
    // Inserted after the DOM node of a ProofLine to provide 
    this._controlNode = Y.Node.create('<div class=lineControls></div>');
    // Set up handlers.
    Y.on('mouseover', handleOver, node);
    Y.on('mouseout', handleOut, node);
    Y.on('click', Y.bind('handleClick', this), node);
  };

  ProofArea.prototype.getMainProof = function() {
    return this._proof;
  };

  ProofArea.prototype.getSelectedLine = function() {
    return this._selectedLine;
  };

  ProofArea.prototype.selectNodeLine = function(lineNode) {
    var selected = this._selectedLine;
    this._selectedLine = this.getMainProof().selectNodeLine(lineNode);
    if (selected != this._selectedLine) {
      this._controlNode.remove();
    }
  };

  // A click deselects any selected parts of the current
  // formula.  If the clicked-on part was not selected,
  // selects the clicked-on part.
  ProofArea.prototype.handleClick = function(event) {
    var target = event.target;
    var lineNode = target.ancestor('.proofLine', true);
    if (!lineNode) {
      return;
    }
    if (target == lineNode || target.hasClass('lineSelector')) {
      this.selectNodeLine(lineNode);
      var selection = this.getSelectedLine();
      if (selection && selection.getText()) {
        // Don't push an empty value into the text entry field.
        this._valueTarget.set('value', selection.getText());
      }
    }
    if (target.get('tagName') != 'SPAN') {
      return;
    }
    event.stopPropagation();
    if (!target.hasClass('lineSelector')){
      // Toggle the target expression and deselect all others.
      var picked = target.hasClass('selectedExpr');
      lineNode.all('SPAN').each(function(span) {
        span.removeClass('selectedExpr');
      });
      if (!picked) {
        target.addClass('selectedExpr');
      }
    }
  };

  ProofArea.prototype.buttonClick = function(event) {
    var label = event.target.get('value');
    var lineNode = event.target.ancestor('.proofLine');
    var line = this._proof.findProofLine(lineNode);
    var proof = line.getProof();
    var hypIndex = Y.Array.indexOf(proof.getHyps(), line);
    var isHyp = hypIndex >= 0;
    var stepIndex = isHyp ? -1 : Y.Array.indexOf(proof.getSteps(), line);
    // var text = this._valueTarget.get('value')
    var text = '';
    switch (label) {
    case '+':
      var line;
      if (isHyp) {
        line = proof.addHyp(text, hypIndex);
      } else {
        line = proof.addStep(text, stepIndex);
      }
      this.selectNodeLine(line.getNode());
      break;
    case 'x':
      if (isHyp) {
        if (proof.getHyps().length > 1) {
          proof.removeHyp(hypIndex);
        }
      } else if (proof.getSteps().length > 1) {
        proof.removeStep(stepIndex);
      }
      break;
    case 'P':
      if (isHyp) break;
      var subproof = proof.addSubproof(stepIndex);
    case '...':
      if (!line.isSelected()) {
        this.selectNodeLine(line.getNode());
      }
      this._controlNode.remove();
      var html = makeControlText();
      this._controlNode.set('innerHTML', makeControlText());
      lineNode.insert(this._controlNode, 'after');
      break;
    default:
      Y.log('Unknown button clicked');
    }
  };

  // Handle mouseovers.
  function handleOver(event) {
    event.target.addClass('hovered');
  };
  // Handle mouseouts.
  function handleOut(event) {
    event.target.removeClass('hovered');
  };

  function makeControlText() {
    return (
      '&nbsp;&nbsp;&nbsp;<select><option> -- choose operation -- '
      + '<option>Modus ponens'
      + '<option>Rule P'
      + '<option>et cetera'
      + '</select>'
      + ' and means for supplying inputs here ... '
      );
  };

  Y.ProofArea = ProofArea;


  //
  // ProofDisplay -- proof or subproof
  //

  /**
   * The node should be a Node with an empty DIV, into which the
   * proof will place displays of its hypotheses and
   * proof steps.
   *
   * Inserts one empty hypothesis and one empty proof step.
   */
  function ProofDisplay(node, proofArea) {
    this._node = node;
    this._proofArea = proofArea;
    // Hypotheses, array of ProofLines.
    this._hyps = [];
    // Steps, array of ProofLine | ProofDisplay.
    this._steps = [];
    this._hypsNode = node.appendChild('<div class=hyps></div>');
    this._stepsNode = node.appendChild('<div class=steps></div>');
    this.addHyp('', 0);
    this.addStep('', 0);
    Y.log(this._stepsNode);
  };

  ProofDisplay.prototype.toString = function() {
    return '#{ProofDisplay hyps: ' + this._hyps.toString() +
    ' steps: ' + this._steps.toString() + '>';
  };

  ProofDisplay.prototype.getProofArea = function() {
    return this._proofArea;
  };

  ProofDisplay.prototype.getNode = function() {
    return this._node;
  };

  ProofDisplay.prototype.getHyps = function(pos) {
    return this._hyps;
  };

  ProofDisplay.prototype.addHyp = function(text, pos) {
    var line = new ProofLine(text, this);
    // Insert a new proof line into the hyps and its
    // node into the DOM.
    this._hyps.splice(pos, 0, line);
    this._hypsNode.insert(line.getNode(), pos);
    return line;
  };

  ProofDisplay.prototype.removeHyp = function(pos) {
    var hyps = this._hyps;
    hyps[pos].getNode().remove();
    hyps.splice(pos, 1);
  };

  ProofDisplay.prototype.getSteps = function() {
    return this._steps;
  };

  ProofDisplay.prototype.addStep = function(text, pos) {
    var line = new ProofLine(text, this);
    // Insert the new proof line into the proof steps and
    // its node into the DOM.
    this._steps.splice(pos, 0, line);
    this._stepsNode.insert(line.getNode(), pos);
    return line;
  };

  ProofDisplay.prototype.removeStep = function(pos) {
    var steps = this._steps;
    steps[pos].getNode().remove();
    steps.splice(pos, 1);
  };

  // TODO: debug me.
  ProofDisplay.prototype.addSubproof = function(pos) {
    var proofNode = new Y.Node.create('<div class=proof></div>');
    this._stepsNode.insert(proofNode, pos);
    var proof = new ProofDisplay(proofNode, this._proofArea);
    this._steps.splice(pos, 0, proof);
    return proof;
  }

  /**
   * Select the line of the proof belonging to the node, deselecting
   * any others.  If the line was already selected, deselect it.
   * Copies its text into the text input field on selection.  Searches
   * through lines in subproofs.
   *
   * Returns any newly-select ProofLine else null.
   */
  ProofDisplay.prototype.selectNodeLine = function(nodeToSelect) {
    // Newly-selected proof line if any.
    var selected = null;
    function updateLine(line) {
      if (line instanceof ProofDisplay) {
        selected = line.selectNodeLine(nodeToSelect) || selected;
      } else {
        var node = line.getNode();
        if (node == nodeToSelect) {
          node.toggleClass('selectedLine');
          if (node.hasClass('selectedLine')) {
            selected = line;
          }
        } else {
          node.removeClass('selectedLine');
        }
      }
    };
    // The code could include fast path for the case where the
    // node is currently selected.
    Y.Array.each(this._hyps, updateLine);
    Y.Array.each(this._steps, updateLine); 
    return selected;
  };

  /**
   * Searches for a ProofLine in this ProofDisplay, whose
   * node is the one given.  Returns the one found
   * or null.
   */
  ProofDisplay.prototype.findProofLine = function(node) {
    function checkLine(line) {
      return line instanceof ProofDisplay
        ? line.findProofLine(node)
        : line.getNode() == node ? line : null;
    };
    function searchLines(array) {
      for (var i = 0; i < array.length; i++) {
        var found = checkLine(array[i]);
        if (found) {
          return found;
        }
      }
      return null;
    }
    return searchLines(this._hyps) || searchLines(this._steps); 
  };

  Y.ProofDisplay = ProofDisplay;


  //
  // ProofLine -- represents one line of a ProofDisplay.
  //
  // May be a hypothesis or step.
  //

  function ProofLine(wffText, proof) {
    // Current text as supplied.
    this._text = wffText;
    // Containing ProofDisplay object.
    this._proof = proof;
    // Parse tree of the current text.
    this._formula = Y.WffParser.parse(this._text);
    // Node containing top DOM element for display of this line.
    this._node = this._makeNode();
    // Node containing this line's WFF display, replaceable
    // by setting innerHTML.
    this._topWff = this._node.one('.topWff');
  };

  ProofLine.prototype.getNode = function() {
    return this._node;
  };

  ProofLine.prototype.isSelected = function() {
    return this.getNode().hasClass('selectedLine');
  };

  /**
   * Create a Node suitable as the display of this ProofLine.
   */
  ProofLine.prototype._makeNode = function() {
    var lineControls =
      '<input type=button class=lineButton value="..."'
      + ' title="Additional operations">'
      + '<input type=button class=lineButton value="P"'
      + ' title="Insert subproof">'
      + '<input type=button class=lineButton value="+"'
      + ' title="Insert line">'
      + '<input type=button class=lineButton value="x"'
      + ' title="Delete line">';
    var selector = '<span class=lineSelector>&nbsp;&bull;&nbsp;</span>';
    var display =
      '<span class=topWff>' + htmlString(this.getParseTree()) + '</span>';
    var node =
      Y.Node.create(
        '<div class=proofLine>' + lineControls + selector
        + display + '</div>');
    Y.on('click', Y.bind('buttonClick', this._proof.getProofArea()),
         node.all('input.lineButton'));
    return node;
  };

  ProofLine.prototype.getParseTree = function() {
    return this._formula;
  };

  ProofLine.prototype.getText = function() {
    return this._text;
  };

  ProofLine.prototype.setText = function(text) {
    this._text = text;
    this._formula = Y.WffParser.parse(this._text);
    this._topWff.set('innerHTML', htmlString(this._formula));
  };

  ProofLine.prototype.getProof = function() {
    return this._proof;
  };

  /**
   * Given a formula represented as a string or nexted array of
   * strings, returns a string of HTML to display the given
   * WFF parse tree.
   */
  function htmlString(formula) {
    // See also "one dot leader": &#x2024;
    var mapping = {':and': '&and;',
                   ':or':  '&or;',
                   ':not': '&not;',
                   ':forall': '&forall;',
                   ':exists': '&exist;',
                   ':implies': '&sup;',
                   ':equiv': '&equiv;',
                   ':lambda': '&lambda;'
                   // Turnstile
                   // ':theorem': '&#8866;'
    };
    var parens = !formula.inline;
    if (Y.Lang.isArray(formula)) {
      var binder = mapping[formula[0]];
      if (formula.length == 3 && prefix[formula[0]] == 2) {
        return '<span class=expr>' + binder
          + '<span class=expr>' + formula[1] + '</span> '
          + htmlString(formula[2]) + '</span>';
      }
      var result = '<span class=expr>';
      if (parens) {
        result += '(';
      }
      Y.Array.each(formula, function(f, i) {
	if (i > 0) {
	  result += ' ';
	}
        result += htmlString(f);
      });
      if (parens) {
        result += ')';
      }
      result += '</span>';
      return result;
    } else {
      var entity = mapping[formula];
      if (entity) {
        formula = entity;
      }
      return '<span class=expr>' + formula + '</span>';
    }
  };

  Y.ProofLine = ProofLine;


  //
  // WffParser
  //

  Y.WffParser = function() {
    throw new Exception('Not instantiable');
  };

  // Precedence table for infix operators.
  var precedence = {
    ':equiv': 10,
    '=': 11,
    ':implies': 12,
    ':or': 13,
    ':and': 14,
    '<': 20,
    '=': 20,
    '>': 20,
    '+': 30,
    '-': 30,
    '*': 40,
    '/': 40
  };

  // Lookup table for detecting prefix operators.
  // These bind with a strength of 1000.  The value
  // represents the number of arguments for the operator.
  var prefix = {
    ':not': 1,
    ':forall': 2,
    ':exists': 2,
    ':lambda': 2
  };

  // Destructively parse all subparts of the
  // the given formula, recursively.
  function parseAll(formula) {
    if (Y.Lang.isArray(formula)) {
      Y.Array.each(formula, parseAll);
      parse(formula, 0, 0);
    }
  };

  // Input will be a tree in the form of a nested array
  // of strings and arrays.  Explicit parentheses in the
  // input become arrays in the input.  This parses prefix
  // and infix operators into additional trees.
  // This parses destructively, replacing structure in the
  // input.
  //
  // Parse a subexpression of "a" starting at "pos"
  // in the context of an operator to the left with a binding
  // power of "leftPower", replacing the token at "pos"
  // with a parsed tree.
  //
  // Reduces operators with greater than leftPower, replacing
  // the token at "a" with the parsed subtree.  Otherwise
  // leaves the token at "pos" unchanged.
  //
  // Marks any subtrees made during parsing with an "inline"
  // property.
  function parse(a, pos, leftPower) {
    var token = a[pos];
    var prefixArgs = prefix[token];
    if (prefixArgs && a.length >= pos + 2) {
      // Reduce the operand if it binds tighter than
      // the prefix operator.
      parse(a, pos + prefixArgs, 1000);
      // Reduce the operator and operand into a subtree.
      reducePrefix(a, pos, prefixArgs);
    }
    // Keep reducing leading parts into subtrees until the next
    // infix operator has no greater than leftPower.
    while (a.length >= pos + 3 && !(pos == 0 && a.length == 3)) {
      // Binding power of the upcoming operator
      var power = precedence[a[pos + 1]] || 1000;
      if (power > leftPower) {
        // First parse down the right operand
        parse(a, pos + 2, power);
        // then make the left, right, and operator into a subtree.
        reduceInfix(a, pos);
      } else {
        return;
      }
    }
  };

  // Reduce a prefix operator at i.
  // Changes a[i] and removes the operator and n operand(s).
  // from the list of tokens.
  // If it makes a new subtree, flags it as "inline"
  // (implicit parentheses).
  // The current code allows only individual tokens for any
  // arguments before the last one, e.g. "lambda x (expr)".
  function reducePrefix(a, i, n) {
    if (i == 0 && a.length == 1)
      return;
    a[i] = a.slice(i, i + n + 1);
    a[i].inline = true;
    a.splice(i + 1, n);
  };

  // Reduce an infix operator at i+1.
  // Changes a[i] and removes the operator and operands
  // from the list of tokens.
  // If it makes a new subtree, flags it as "inline"
  // (implicit parentheses).
  function reduceInfix(a, i) {
    a[i] = a.slice(i, i + 3);
    a[i].inline = true;
    a.splice(i + 1, 2);
  };

  // Cheap-o hack for "parsing" a sequence of s-expressions
  // into a nested array of strings.
  // Works by converting sequences of printing characters
  // into string literals and parentheses to square brackets,
  // embedding commas into sequences of whitespace,
  // then applying a JSON parser to the result, followed
  // by custom parsing using the "parse" function above.
  // Empty input yields an empty result array.
  Y.WffParser.parse = function(input) {
    input = input.replace(/[-+*/<=>:.a-zA-Z0-9]+/g, '"$&"');
    input = input.replace(/[(]/g, '[');
    input = input.replace(/[)]/g, ']');
    input = input.replace(/[ \t\n\r]+/g, ',');
    input = '[' + input + ']';
    var result = Y.JSON.parse(input);
    result.inline = true;
    parseAll(result);
    return result;
  };

  }, '0.1', {use: ['array-extras', 'expr']});

