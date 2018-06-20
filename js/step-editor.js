// Copyright 2011 - 2018 Crispin Perdue.
// All rights reserved.

// Set everything up immediately on load, avoiding changes to
// the global environment except through namespace "Toy".
(function() {

// Make application assertions available through "assert".
const assert = Toy.assertTrue;
const format = Toy.format;
const dom = Toy.dom;
const TermSet = Toy.TermSet;


//// PROOF EDITOR

// TODO: Use events and event handlers to make cleaner separation
//   between ProofEditor, ProofDisplay, and StepEditor.  StepEditor
//   needs some kind of access to the array of proof steps to
//   translate step numbers to steps.  Perhaps ProofDisplay can notify
//   when its list of steps changes.

// Each instance has a numeric ID.
var nextProofEditorId = 1;

/**
 * Construct a proof displayer/editor, which is a composite made from
 * a ProofDisplay.  User interaction may also create additional
 * subproof ProofDisplay objects within this.
 *
 * Public properties:
 *
 * proofDisplay: ProofDisplay for the proof being edited.
 * containerNode: jQuery object for outermost DOM node for the display.
 * stepEditor: StepEditor for the proof being edited.
 * proofEditorId: identifies this editor for purposes of restoring
 *   its operating state across visits / page loads.  Consists of the
 *   pathname part of the browser "location", "#", and an integer
 *   sequence number of the editor within the page.
 * givens: array of boolean terms defining the problem, often
 *   equations (not steps).  Should only be set when the proof is
 *   empty.  Read it as a TermSet.
 * givenVars: object/set keyed by names of variables free in the givens;
 *   read-only.
 * solutions: If any of these expressions (or strings) is an alphaMatch
 *   with a step, announce the step as a solution.
 * standardSolution: Boolean.  If no explicit solutions given, but the
 *   result of a step solves for a variable (equal to a numeral or
 *   fraction), announce that the problem is solved.
 * showRuleType: Selects type of rules to show, as determined by offerApproved.
 *   Takes effect when this editor is reset.
 * showRules: List of individual rules to show.  Takes effect when this
 *   editor is reset.
 */
function ProofEditor() {
  const self = this;
  self._givens = new TermSet();
  self.givenVars = {};
  self.solutions = [];
  self.standardSolution = true;
  self.showRuleType = 'general';
  self.showRules = [];
  // Set the ID.
  self.proofEditorId = window.location.pathname + '#' + nextProofEditorId++;
  const mainDisplay = new Toy.ProofDisplay();
  mainDisplay.proofEditor = self;
  self.proofDisplay = mainDisplay;
  self.steps = mainDisplay.steps;

  const stepEditor = new Toy.StepEditor(this);
  self.stepEditor = stepEditor;

  const proofButtons = buildProofButtons(self);
  self.$copyText = proofButtons.$copyText;
  self.$rulesMode = proofButtons.$rulesMode;

  self._wksControls = buildWksControls(self);

  var menu = new RuleMenu(self);
  // Suppress solution status display when the mouse is within the
  // menu, leaving more room for step suggestions.
  menu.onEnter(function() { proofEditor.requestStatusDisplay(false); });
  menu.onLeave(function() { proofEditor.requestStatusDisplay(true); });
  self.ruleMenu = menu;

  // The ruleStats are visible except when a proof is brand new and
  // there is nothing to show.
  var ruleStats = $('<div class="ruleStats invisible">Last rule ' +
                    '<span class=ruleTime></span> msec, ' +
                    '<span class=ruleSteps></span> steps</div>');
  // This element is for messages about status of solving the problem.
  var $status = $('<div class="solutionStatus transFade"/>');
  var $statusDisplay = $('<div class=solutionStatusDisplay/>');
  $status.append($statusDisplay);
  self.$status = $status;
  self.$statusDisplay = $statusDisplay;

  // The equations.html page "Try a different problem" button goes
  // at the end of this $header div.
  let $header =
    ($('<div class=proofEditorHeader>')
     .append('<b style="font-size:larger">Problem work area</b>'));
  let $readOnly =
    $('<p class=ifReadOnly><i><b style="color:red">Note:</b>' +
      ' This display is read-only due to editing' +
      ' in progress in another window or tab.</i></p>');

  // Top-level element of the proof editor display:

  const $node = this.containerNode = $('<div class=proofEditor></div>');
  this.containerNode
    .append($header)
    .append($readOnly)
    .append(mainDisplay.node)
    .append($status)
    .append(proofButtons.$node)
    .append(stepEditor.$node)
    .append(this._wksControls.node)
    .append(menu.$node)
    .append(ruleStats);
  this.setEditable(true);

  // Also append controls from the step editor object to the
  // container node, removing them from their initial site in the
  // step editor.
  //
  // TODO: Remove this ugly hack by consolidating the controls here
  //   and the step editor controls into a ProofControls object, all
  //   constructed together.  The step editor now seems to be reduced
  //   to the form for interactively supplying arguments to a rule.
  this.$advice = ($('<div class="advice hidden">')
                  .append('Select an expression or step.'));
  this.containerNode.append(this.$advice);

  // Restore editor state.
  const state = Toy.getSavedState(self);
  // The (default) name is the part between the last "/", if any, and
  // the first following "." or "#".
  const name = this.proofEditorId.replace(/^(.*[/])?(.*?)[.#]/, '$2');
  self.setDocumentName(state
                       ? state.docName
                       // By default set the document name according to the URI path,
                       // and the editor number if that is greater than one.
                       : name);

  // Prepare to write out proof state during refresh, so basically
  // whenever it changes.
  this._refresher = new Toy.Refresher(function() {
      self._updateGivens();
      self.saveProofState();
      // Set (or clear) the message in the $status box.
      var steps = mainDisplay.steps;
      var len = steps.length;
      if (len) {
        var step = steps[len - 1];
        var message = self.progressMessage(step.original);
        $statusDisplay.empty();
        $statusDisplay.append(message);
        $status.toggleClass('invisible', !message);
      } else {
        $status.toggleClass('invisible', true);
      }
    });

  // Restore proof state.
  const proofData = Toy.readDoc(self._documentName);
  if (proofData) {
    mainDisplay.setSteps(Toy.decodeSteps(proofData.proofState));
  }
  // If another ProofEditor is already holding the document,
  // make it read-only.  Otherwise reserve it for this one.
  if (Toy.isDocHeldFrom(self._documentName, self)) {
    self.setEditable(false);
  }

  // Event handlers

  $node.on('mouseenter', function() {
      // Stop overriding visibility of the rule menu.
      self.ruleMenu.$node.toggleClass('ultraInvisible', false);
    });
  $node.on('mouseleave', function() {
      // Temporarily override rule menu visibility.
      self.ruleMenu.$node.toggleClass('ultraInvisible', true);
      // Hide the worksheet controls.
      self._wksControls.hide();
    });

  // Document-level event handlers.

  // Returns a boolean indicating whether the given jQuery node
  // is within an element matching the selector.
  function within($node, selector) {
    return $node.closest(selector).length > 0;
  }
  // Click in most areas of the document removes any step or expr
  // selection.
  $(document).on('click', function(event) {
      if (!mainDisplay._selectLock) {
        // When a rule entry form is open, selection is locked.
        const $target = $(event.target);
        // TODO: Consider setting up click handlers for elements such as
        //   these so they add information to the event indicating for
        //   example "<editor> noDeselect" or below "<wksControls>
        //   noDismiss".  And check that data in code like this here.
        //
        // The following areas are intended targets for clicks and have
        // click handlers, so we prefer not to remove the selection in
        // these areas at this level.
        //   .stepAndNum is the main container for all exprs.
        //   .ruleMenu is the rules menu
        //   .above is the display of popups for quick access to rewrites
        //   .ruleName.link pops subproof displays up and down
        //   .input, .button, and .select are typical form controls
        //   .wksControlsOuter is the main box for worksheet controls
        const selectors = ('.stepAndNum, .ruleMenu, .above, ' +
                           '.ruleName.link, .inferenceDisplay, ' +
                           '.wksControlsOuter, input, button, select');
        // Mousedown in most places removes any step or expr selection.
        if (!within($target, selectors)) {
          mainDisplay.deselectStep();
        }
      }
    });
  // Click in most areas of the document hides the workspace controls.
  $(document).on('click', function(event) {
      const $target = $(event.target);
      if (!within($target, '.wksControlsOuter, .proofButtons')) {
        self._wksControls.hide();
      }
      if (!within($target, '.proofErrors')) {
        // Similarly, most clicks hide the proof errors display.
        // TODO: Toggle "hidden" rather than calling "hide".
        self.stepEditor.$proofErrors.hide();
      }
    });
}

/**
 * Builds and returns an object for the proofButtons DIV of the given
 * proof editor.  This is the block of controls with the "worksheet"
 * button.  The returned plain object has properties:
 *
 * $node: jQuery node of the DIV
 * $copyText: jQuery of the copyText input field
 * $rulesMode: jQuery of the rules mode selector
 */
function buildProofButtons(editor) {
  // Add the group of buttons.
  // The proofButtons class is used in some examples.
  const $proofButtons = $('<div class=proofButtons/>');

  const $clearProof = $('<input type=button value="Clear work">');
  const css = {float: 'right',
               backgroundColor: '#d9534f',
               color: 'white'
  };
  $clearProof.css(css);

  // Toggling the proof state display visibility with a button.
  const $wksButton = $('<input type=button value="Worksheet... ">');

  const $options = $('<select class=rulesToShow>' +
                     '<option value=algebra>algebra' +
                     '<option value=general>general reasoning' +
                     '<option value=all>all available' +
                     '</select>');

  // This holds textual representation of the latest selected term.
  // It is writable so the user can scroll it horizontally (using the
  // text cursor).
  const $copyText = $('<input class=copyText>');
  // The fa and fa-copy classes put a "copy" icon into the
  // text of the button.
  const $copyButton = $('<button class="fa fa-copy">');
  $copyButton.css({fontSize: '.8rem'});

  $proofButtons.append($wksButton, $('<s class=em>'));
  $proofButtons.append('Mode');
  $proofButtons.append($options, $('<s class=em>'));
  $proofButtons.append('Selection');
  $proofButtons.append($copyText);
  $proofButtons.append($copyButton);
  $proofButtons.append($clearProof);

  const $rulesMode = $proofButtons.find('.rulesToShow');

  // Main and worksheet controls event handlers

  $copyButton.on('click', function(event) {
      Toy.copyToClipboard($copyText.val());
      // I tried using the TOUCHDOWN event and event.preventDefault()
      // in Chrome, without success.
      $copyText.select();
    });

  $wksButton.on('click', function() {
      let wksControls = editor._wksControls;
      wksControls.toggle();
      // TODO: Move this action into setDocumentName or an observer.
      wksControls.setDocName(editor.getDocumentName());
    });
  $clearProof.on('click', function() {
      if (window.confirm('Do you really want to clear the proof?')) {
        editor.clear();
      }
    });
  // Step editor has state controlling whether to show all rules.
  $rulesMode.on('change', function(event) {
      const stepEditor = editor.stepEditor;
      editor.showRuleType = this.value;
      editor.ruleMenu.refresh();
      stepEditor.reset();
    });
  Toy.soonDo(function() { $rulesMode.trigger('change'); });
  const result = {
    $node: $proofButtons,
    $copyText: $copyText,
    $rulesMode: $rulesMode
  };
  return result;
}

/**
 * This builds and returns an object containing the full content of
 * the workspace-related controls.  The object has the following
 * properties and methods:
 *
 * node: DOM element for the controls.
 * hide(): Hides all of the controls.
 * show(): Shows the controls.
 * getProofText(): Returns the text content of the proof state area.
 * setProofText(text): Sets the text content of the proof state area.
 * setDocName(name): Sets the document name display in the controls area.
 */
function buildWksControls(editor) {
  const $outermost = $('<div class="wksControlsOuter transFade hidden">');
  const $controls = $('<div class="wksControls">');
  $outermost.append($controls);
  $controls.append('<div class=wksTitle>' +
                   'Current worksheet is "<span class=wksName></span>"</div>');
  $buttons = $('<div class=wksButtons>');
  $controls.append($buttons);

  $buttons.append(makeButton('Open... ', 'openButton'),
                  makeButton('Save as... ', 'saveAsButton'),
                  makeButton('Copy to... ', 'copyToButton'),
                  makeButton('Delete... ', 'deleteButton'),
                  makeButton('View as text', 'previewButton'));

  $inputs = $('<div class=wksInputs>');
  $controls.append($inputs);

  function makeEntryField(prefix, classes, action) {
    const html =
      '<div class="{2} hidden form">{1} ' +
      '<input type=text class=input size=30>' +
      '&nbsp;<input type=button class=go value="Go">' +
      '</div>';
    return $(Toy.format(html, prefix, classes));
  }
  const $saveAs = makeEntryField('Save worksheet as', 'saveAs');
  $inputs.append($saveAs);
  const $copyTo = makeEntryField('Copy worksheet to', 'copyTo');
  $inputs.append($copyTo);
  const $message = $('<div class="wksMessage hidden">');
  $inputs.append($message);

  const $openersArea = $('<div class="openersArea transFade hidden">');
  $outermost.append($openersArea);

  const $deletersArea = $('<div class="deletersArea transFade hidden">');
  $outermost.append($deletersArea);

  const stateDisplayHtml =
    '<div class="proofPreview transFade hidden">\n' +
    '<p style="text-align:center; margin-top:0">\n' +
    '<b>Proof State</b>\n' +
    '<p>\n' +
    'The text area below contains the current state of the proof in textual\n' +
    'form.  You can save the state of your work by copying this text into a\n' +
    'document of your choice.  To restore the state at some time in the\n' +
    'future, paste it back then press "Restore proof".\n' +
    '<p style="margin-bottom: 0">\n' +
    '<input class=restoreProof type=button value="Restore proof">\n' +
    '<input class=hideProofState type=button value="Close"><br>\n' +
    '<textarea class=proofStateArea rows=20></textarea>\n' +
    '</div>\n';
  $proofPreview = $(stateDisplayHtml);
  $outermost.append($proofPreview);

  // Elements to be hidden when the display is reset.
  const $resettables = ($saveAs
                       .add($copyTo)
                       .add($message)
                       .add($openersArea)
                       .add($deletersArea)
                       .add($proofPreview));

  // Closes all of the "resettables" and clears the content of the text
  // fields in the worksheet control panel.
  function resetDisplay() {
    $resettables.toggleClass('hidden', true);
    $saveAs.find('.input').val('');
    $copyTo.find('.input').val('');
  }

  // Toggles the display in the given area, hiding all of the other
  // exclusive displays to keep the displays tidy and help keep the
  // user focused.  This is implemented as a toggle especially to
  // support the toggling worksheet buttons.  If it unhides an area,
  // attempts to focus on a node with class "input", for the benefit
  // of areas with a text field.
  function toggleControl($area) {
    const wantHidden = !$area.hasClass('hidden');
    resetDisplay();
    $area.toggleClass('hidden', wantHidden);
    if (!$area.hasClass('hidden')) {
      // :visible is not needed here, but it would be enough, without
      // the "hidden" check if we guaranteed that the area would be
      // hidden using display:none.
      $area.find('input:text:visible:first').focus();
    }
  }

  // Toggles the document list display in the given area,
  // presumably either $openersArea or $deletersArea,
  // hiding all the other controls.
  function toggleDocs($area) {
    toggleControl($area);
    if (!$area.hasClass('hidden')) {
      showDocs($area);
    }
  }

  // Renders a list of all documents within the .docList portion of
  // the given area, removing any prior content.  Omits the current
  // document.
  function showDocs($area) {
    $area.empty();
    const $docList = $('<div class=docList>');
    $area.append($docList);
    // Then add back names of all documents.
    Toy.lsDocs().sort().forEach(function(name) {
        if (name === editor._documentName) {
          return;
        }
        const $div = $('<div class=docName>');
        $div.append(name);
        $docList.append($div);
      });
  }

  // Checks whether the given name is valid as a worksheet name,
  // returning a boolean indication.  If the name is not valid,
  // also sets a message about the issue.
  function checkName(name) {
    if (Toy.checkDocName(name)) {
      return true;
    } else {
      $message.toggleClass('hidden', false);
      $message.text('Invalid worksheet name: "' + name + '"');
      return false;
    }
  }

  // Event handlers

  // Hovers in the openers and deleters areas.
  $openersArea.on('mouseenter mouseleave', '.docName', function(event) {
      $(this).toggleClass('hover');
    });
  $deletersArea.on('mouseenter mouseleave', '.docName', function(event) {
      $(this).toggleClass('hover');
    });

   
  // Handler for the "restore proof" button.  Restores proof state from
  // the text area.
  function restoreProof() {
    Toy.withErrorReporting(function() {
        editor.restoreState();
        result.hide();
      });
  }
  $outermost.find('.restoreProof').on('click', restoreProof);

  // Closing the state display:
  $outermost.find('.hideProofState').on('click', function() {
      $outermost.find('.proofPreview').addClass('hidden');
    });

  // Buttons that open up the ultimate action UIs.
  $controls.find('.openButton').on('click', function() {
      toggleDocs($openersArea);
    });
  $controls.find('.saveAsButton').on('click', function() {
      toggleControl($saveAs);
    });
  $controls.find('.copyToButton').on('click', function() {
      toggleControl($copyTo);
    });
  $controls.find('.deleteButton').on('click', function() {
      toggleDocs($deletersArea);
    });

  // This opens up the proof state "preview".
  $controls.find('.previewButton')
    .on('click', function() {
        toggleControl($proofPreview);
        if (!$proofPreview.hasClass('hidden')) {
          $outermost.find('.proofStateArea').select();
        }
      });

  // Main action functions are in this section.
  $saveAs.on('click', '.go', function() {
      const name = $($(this).closest('div.form')).find('.input').val();
      if (checkName(name)) {
        editor.setDocumentName(name);
        Toy.writeDoc(name, {proofState: editor.getStateString()});
        $message.text('Saved worksheet as "' + name + '"');
        toggleControl($message);
        // TODO: Move this line into setDocumentName or an observer.
        $controls.find('.wksName').text(editor.getDocumentName());
      }
    });
  $copyTo.on('click', '.go', function() {
      const name = $($(this).closest('div.form')).find('.input').val();
      if (checkName(name)) {
        Toy.writeDoc(name, {proofState: editor.getStateString()});
        $message.text('Copied worksheet to "' + name + '"');
        toggleControl($message);
      }
    });
  $openersArea.on('click', '.docName', function() {
      const text = $(this).text();
      const success = editor.openDoc(text);
      if (success) {
        // In principle this would be triggered by observation of
        // of the document name.
        $controls.find('.wksName').text(editor.getDocumentName());
        $openersArea.toggleClass('hidden', true);
      } else {
        window.alert('Could not open worksheet ' + text);
      }
    });
  $deletersArea.on('click', '.docName', function() {
      const name = $(this).text();
      if (name === this._documentName) {
        $message.text('Cannot delete the current document.');
      } else {
        Toy.rmDoc(name);
        $message.text('Deleted "' + name + '"');
        toggleControl($message);
      }
    });

  // Responses to pressing "enter" in an action text field:
  $copyTo.on('keydown', function(event) {
      if (event.keyCode === 13) {
        $copyTo.find('.go').trigger('click');
      }        
    });
  $saveAs.on('keydown', function(event) {
      if (event.keyCode === 13) {
        $saveAs.find('.go').trigger('click');
      }        
    });

  // "Input" handlers to clear the message whenever a
  // text field with document name changes its value.
  $copyTo.on('input', function() {
      $message.toggleClass('hidden', true);
      $message.empty();
    });
  $saveAs.on('input', function() {
      $message.toggleClass('hidden', true);
      $message.empty();
    });

  // Methods

  $stateArea = $outermost.find('.proofStateArea');

  const result = {
    node: dom($outermost),
    hide: function() {
      $outermost.toggleClass('hidden', true);
      resetDisplay();
    },
    show: function() {
      $outermost.toggleClass('hidden', false);
    },
    toggle: function() {
      $outermost.hasClass('hidden') ? this.show() : this.hide();
    },
    getProofText: function() {
      return $stateArea.val();
    },
    setProofText: function(text) {
      $stateArea.val(text);
    },
    setDocName: function(name) {
      $outermost.find('.wksName').text(editor.getDocumentName());
    }
  };

  return result;
}

/**
 * Simple utility that makes HTML text for a button.
 */
function makeButton(label, classes) {
  return Toy.format('<button type=button class="{2}">{1}</button>',
                    label, classes || '');
}

/**
 * Sets the name of this editor's worksheet, and does associated
 * bookkeeping.  This does not load or save any proof state.  (In most
 * use cases one or the other should also be done.)
 */
ProofEditor.prototype.setDocumentName = function(name) {
  const self = this;
  self._documentName = name;
  // Remember the state of this editor.
  // TODO: Replace the following with some form of state observation.
  if (self.proofDisplay.isEditable()) {
    // Only note the state within this context if editing the proof,
    // so that otherwise the document can be edited by other editors.
    // (See Toy.isDocHeldFrom.)
    Toy.noteState(self, {docName: self._documentName});
  }
  Toy.saveState(self, {docName: self._documentName});
};

/**
 * Attempts to open the named document in this proof editor, setting
 * the editor's document name and loading its proof state.  Returns
 * true iff the document is successfully loaded, else false.
 */
ProofEditor.prototype.openDoc = function(name) {
  const proofData = Toy.readDoc(name);
  if (proofData) {
    this.setDocumentName(name);
    this.setSteps(Toy.decodeSteps(proofData.proofState));
    return true;
  } else {
    return false;
  }
};

/**
 * Returns the name of the editor's current document.
 */
ProofEditor.prototype.getDocumentName = function() {
  return this._documentName;
};

/**
 * Empties the proof and problem statement for a fresh start.
 */
ProofEditor.prototype.clear = function() {
  this.showRules = [];
  this.stepEditor.reset();
  this.proofDisplay.setSteps([]);
};

/**
 * Requests status display on or off.  Regardless of the request,
 * status is only ever displayed if it contains text.  (Status change
 * methods modify its visibility directly.)
 */
ProofEditor.prototype.requestStatusDisplay = function(vis) {
  var $display = this.$statusDisplay;
  var text = $display.text()
  // $display.toggleClass('hidden', !(text && vis));
};

/**
 * Define the "givens" property as a virtual property.  Setting it has
 * the side effect of modify the "givenVars" property as well, which
 * should be treated as readonly.  If not set explicitly through the
 * setter, givens will come from uses of the "given" rule.
 */
Object.defineProperty(ProofEditor.prototype, "givens", {
    get: function() { return this._givens; },
    set: function(g) {
      assert(this.proofDisplay.steps.length == 0, 'Proof is not empty');
      var wff;
      for (var i = 0; i < g.length; i++) {
        var g1 = Toy.termify(g[i]);
        this._givens.add(g1);
        wff = (wff ? Toy.infixCall(wff, '&', g1) : g1);
      }
      if (wff) {
        this.addStep(Toy.rules.given(wff));
      }
      this._updateGivenVars();
    }
  });

/**
 * Recompute the problem givens from the first proof step
 * if its rule name is "given".
 */
ProofEditor.prototype._updateGivens = function() {
  var self = this;
  var steps = self.proofDisplay.steps;
  self._givens.clear();
  function add(given) { self._givens.add(given); }
  if (steps.length > 0) {
    var step = steps[0];
    if (step.ruleName === 'given') {
      step.wff.getMain().getRight().scanConjuncts(add);
    }
  }
  self._updateGivenVars();
};

/**
 * Update the givenVars to match the (possibly changed) set of givens
 * of this problem.
 */
ProofEditor.prototype._updateGivenVars = function() {
  // An object/set with names of all variables in any of the
  // givens:
  var vars = {};
  this._givens.each(function(g) { $.extend(vars, g.freeVars()); });
  this.givenVars = vars;
};

/**
 * Public interface to set the rule and fact offerability mode
 * of this ProofEditor.
 */
ProofEditor.prototype.setRulesMode = function(mode) {
  this.$rulesMode.val(mode);
  if (this.$rulesMode.val() != mode) {
    Toy.err('Bad rules mode setting: ' + mode);
  }
  this.$rulesMode.trigger('change');
};

/**
 * Add a step to the proof.
 */
ProofEditor.prototype.addStep = function(step) {
  this.proofDisplay.addStep(step);
};

/**
 * Gets the state of the proof, in string form.
 */
ProofEditor.prototype.getStateString = function() {
  return Toy.encodeSteps(this.proofDisplay.steps)
};

/**
 * Sets the state of the proof from a string as returned by
 * getStateString.
 */
ProofEditor.prototype.setStateFromString = function(encoded) {
  // TODO: Rename to setProofFromString.
  var steps = encoded ? Toy.decodeSteps(encoded) : [];
  this.proofDisplay.setSteps(steps);
};

/**
 * Sets the steps to the given array of non-renderable steps.
 */
ProofEditor.prototype.setSteps = function(steps) {
  this.proofDisplay.setSteps(steps);
};

/**
 * Save the proof state to the the worksheet controls text area and
 * the document's data store.  Normally use the proofChanged method
 * rather than calling this directly, to avoid redundant work.
 */
ProofEditor.prototype.saveProofState = function() {
  var text = this.getStateString();
  this._wksControls.setProofText(text);
  Toy.writeDoc(this._documentName, {proofState: text});
};

/**
 * Attempts to restore the proof state from the worksheet controls
 * text area.
 */
ProofEditor.prototype.restoreState = function() {
  var string = this._wksControls.getProofText();
  this.setStateFromString(string);
};

/**
 * Returns true iff this is editable.
 */
ProofEditor.prototype.isEditable = function() {
  return this.proofDisplay.isEditable();
};

/**
 * Turns editability of the proof editor on or off, currently
 * affecting only the UI.
 */
ProofEditor.prototype.setEditable = function(value) {
  this.containerNode.toggleClass('editable', value);
  // The following set the state of the display and hide or show the
  // step editor.
  this.proofDisplay.setEditable(value);
  this.stepEditor.$node.toggle(value);
};

/**
 * Toggles display of the proof buttons on or off according to the
 * given value.
 */
ProofEditor.prototype.showProofButtons = function(value) {
  this.proofButtons.$node.toggle(value);
};


//// PROOF STEP EDITOR

// CSS class names beginning with "sted-" are reserved to
// the step editor.  Access to nodes through their class
// should always work in the context of the step editor's node.

// All types that can be entered in a form.  Omits site, bindingSite,
// and reducible, which are currently not supported in forms.  See
// See comments for ruleInfo in engine.js for details on the types.
var formTypes = {
  term: true,
  varName: true,
  string: true,
  step: true,
  equation: true,
  implication: true
};

// Datatypes that refer to proof steps.
var stepTypes = {
  step: true,
  equation: true,
  implication: true
};

// Datatypes that refer to sites within a step.  None of these are
// in formTypes.
var siteTypes = {
  site: true,
  bindingSite: true,
  reducible: true
};


// TODO: Support rules that need multiple selectable inputs by
//   using a selection and following steps as inputs.  If multiple
//   selections are needed, the step editor can use "consider"
//   to pick a term from a step, and if necessary, look back to
//   the origin site of the term to use it as a selection.
//   Probably only fill in rule arguments from steps at the end
//   of the current proof, and remove steps added by copying
//   or use of "consider"
//
//   Another way to collect multiple steps as inputs would be to
//   (temporarily) create a conjunction of steps and use the
//   conjunction as a single input.
//
//   Also, for rules that do matching, such as rewrite rules,
//   the editor could scan the current proof for matching steps
//   and offer the results as suggestions.

/**
 * A ProofDisplay can have only one StepEditor.  It appears at the end
 * of an editable proof.
 *
 * TODO: Support essential step editing such as justification of an assumed
 * step, for steps that already exist.  Also rearranging proofs.
 *
 * Fields:
 * $node: DIV with the step editor's HTML, has class stepEditor.
 * ruleName: name of rule selected from the RuleMenu; used with form
 *   information in tryExecuteRule.
 * form: jQuery SPAN to hold the argument input form.
 * proofDisplay: ProofDisplay to edit
 * lastRuleTime: Milliseconds consumed by last execution of tryRule.
 * lastRuleSteps: Steps used by last execution of tryRule.
 *
 * TODO: Continue cleaning up this class, removing detritus and
 *   moving the proofErrors display into the ProofEditor.
 */
function StepEditor(proofEditor) {
  // Make this available to all inner functions.
  var self = this;

  // TODO: Reconsider the distinction and the relationship between the
  // StepEditor and ProofEditor.
  self._proofEditor = proofEditor;
  self.proofDisplay = proofEditor.proofDisplay;
  self.lastRuleTime = 0;
  self.lastRuleSteps = 0;
  self.ruleName = '';

  // Create a DIV with the step editor content.
  var $div = $('<div class=stepEditor/>');

  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<button class="fa fa-times-circle-o sted-clear" title="Clear the input">');
  self.clearer.addClass('hidden');
  self.form = $('<span class=sted-form></span>');
  // Proof errors display.
  self.$proofErrors = $('<div class="proofErrors hidden"></div>');
  self.$node = $div;

  $div.append(self.clearer, self.form, self.$proofErrors);
  // Install event handlers.
  self.clearer.on('click', function() { self.reset(); });
  // Keyboard events bubble to here from the inputs in the form.
  self.form.on('keydown', function(event) {
    if (event.keyCode == 13) {
      // <enter> key was hit
      self.tryExecuteRule(true);
    }
  });
  self.form.on('click', 'button', function() { self.tryExecuteRule(true); });
  // Always clear the errors when clicked.
  self.$proofErrors.on('click', '.clearer', function() {
      self.$proofErrors.hide();
    });
}

/**
 * Marks this StepEditor as busy or not in the UI.  See also
 * StepEditor.reset.
 */
// TODO: Split this, with a "StepEditor.clear" method.
StepEditor.prototype._setBusy = function(busy) {
  const editor = this._proofEditor;
  // TODO: Consider doing more of this work through CSS rules.
  this.$node.toggleClass('busy', busy);
  if (busy) {
    editor.ruleMenu.$node.toggleClass('hidden', true);
  } else {
    // TODO: Consider adding hide / unhide methods to RuleMenu
    //   instead of this rather crude dependency on their
    //   lengths.  The "unhide" would not necessarily remove the
    //   "hidden" style class, just set its visibility to "normal".
    editor.ruleMenu.$node.toggleClass('hidden', editor.ruleMenu.length === 0);
  }
  // Clear the form.
  // TODO: Make these actions into a function/method, see "reset".
  this.clearer.addClass('hidden');
  this.form.html('');
  editor.proofDisplay.setSelectLock(false);
};

/**
 * Reports the HTML message as an error in the step editor.
 */
StepEditor.prototype.error = function(message) {
  this.report('<b>' + message + '</b>');
};

/**
 * Report the error through the DOM and help the user debug in case it
 * has a "step" property.  The argument should be an Error object or
 * an HTML string.
 */
StepEditor.prototype.report = function(error) {
  var $proofErrors = this.$proofErrors;
  assert($proofErrors.length, 'proofJQ?');
  // Clicking _anywhere_ will actually clear the message.
  $proofErrors.show();
  $proofErrors.html('<button class=clearer>X</button>');
  if (error instanceof Error) {
    $proofErrors.append('<b>Error: ' + error.message + '</b>');
    if (error.step) {
      Toy.renderProof(error.step, $proofErrors);
    }
  } else {
    // It should be a string.
    $proofErrors.append(error);
  }
};

/**
 * Puts the step editor back in the initial state from the user's
 * point of view: visible with empty input, no rule-specific form,
 * available rules visible.  Does not clear any selection, and does
 * not affect the rules offered.  See also StepEditor._setBusy.
 */
StepEditor.prototype.reset = function() {
  this.clearer.addClass('hidden');
  this.form.html('');
  this.proofDisplay.setSelectLock(false);
  this._setBusy(false);
};

/**
 * Check that the given args Array is filled in with values that are
 * not instances of Error, and that up to minArgs, the values are not
 * the undefined value.  If reportError is true, report the problem in
 * the StepEditor, and in any case return true iff all is OK, else
 * false.  If the values are OK and some optional args are undefined,
 * truncate the args array to omit the unneeded undefined values.
 */
StepEditor.prototype.checkArgs = function(args, minArgs, reportError) {
  // Check that the args are all filled in.
  var required = (typeof minArgs == 'number'
                  ? minArgs
                  : args.length);
  for (var i = 0; i < args.length; i++) {
    var value = args[i];
    if (value === undefined && i < required) {
      if (reportError) {
        this.error('Undefined argument ' + i);
      }
      return false
    } else if (value instanceof Error) {
      if (reportError) {
	this.error(value.message);
      }
      return false;
    }
  }
  // Truncate the args array to omit optional args not supplied,
  // in case the rule looks at its arguments array.
  for (var i = required; i < args.length; i++) {
    if (args[i] === undefined) {
      args.length = i;
      break;
    }
  }
  return true;
};

/**
 * Computes whether a rule needs a "site" type as an input.
 */
function usesSite(rule) {
  var inputs = rule.info.inputs;
  for (var type in inputs) {
    if (type in siteTypes) {
      return true;
    }
  }
  return false;
}

/**
 * Adds class=step, class=term, etc. to each form element according
 * to its name -- same as the name, but stripping off any numeric suffix,
 * e.g. step2 => step.  Also prevents autocompletion, basically because
 * some sites add autosuggest entries to fields named "term".
 */
function addClassInfo(form) {
  form.find('input').each(function() {
      // Note: the pattern matches any string.
      var className = this.name.match(/^(.*?)\d*$/)[1];
      $(this).addClass(className);
      $(this).attr('autocomplete', 'off');
    });
}

/**
 * Try to fill in a field of the form with the selection.  For
 * steps this will be a reference to the step, and for terms it
 * will be a textual rendering of the selected expression.
 *
 * Only call this if the rule does not use a site (usesSite).
 */
StepEditor.prototype.addSelectionToForm = function(rule) {
  var proofDisplay = this.proofDisplay;
  var step = proofDisplay.selection;
  if (step) {
    var expr = step.selection;
    var form = this.form;
    var n = step.stepNumber;
    // Search for the first input field that is compatible with the
    // selection and fill it in with selection information.
    form.find('input').each(function() {
      var fieldType = this.name.match(/^(.*?)\d*$/)[1];
      if (expr) {
	// TODO: Don't use the selection as a term if it will be used
	// by the rule as a site.
	if (fieldType == 'term') {
          // TODO: Use printing that is guaranteed reversible.
	  this.value = expr.toString();
          // Stop iteration.
	  return false;
	}
      } else {
	if (fieldType == 'step'
	    || (fieldType == 'equation' && step.unHyp().isCall2('='))
	    || (fieldType == 'implication' && step.unHyp().isCall2('=>'))) {
	  this.value = n;
          // Stop iteration.
	  return false;
	}
      }
    });
  }
};

/**
 * Fill in arguments for the rule named by the ruleMenu from the
 * current selection and the rule's input form, and if successful set
 * up actual execution and redisplay to occur after the UI has
 * opportunity to repaint.  If reportFailure is true, shows the
 * user any error message from calling fillFromForm.  Otherwise
 * just leaves the form up for the user to complete.
 */
StepEditor.prototype.tryExecuteRule = function() {
  // TODO: Get it together on failure reporting here.
  var ruleName = this.ruleName;
  var rule = Toy.rules[ruleName];
  var minArgs = rule.info.minArgs;
  var args = this.argsFromSelection(ruleName);
  this.fillFromForm(args);
  if (this.checkArgs(args, minArgs, true)) {
    tryRuleSoon(this, rule, args);
  }
};

/**
 * Turns on the editor's busy indicator and sets the rule up to run
 * with the given args as soon as the UI has opportunity to repaint.
 */
function tryRuleSoon(stepEditor, rule, args) {
  args.forEach(function(arg) {
      if (Toy.isProved(arg) && arg.isRendered()) {
        // Really all step arguments to all steps everywhere should be
        // non-renderable in the current implementation, but this situation
        // is arguably a greater risk than others.
        Toy.logError('Argument step ' + arg.stepNumber + ' is renderable.');
      }
    });
  stepEditor._setBusy(true);
  // Try running the rule once the UI shows it is working.
  Toy.afterRepaint(stepEditor._tryRule.bind(stepEditor, rule, args));
}

/**
 * Tries to run the given rule (function) with the given rule
 * arguments, adding the result to this step editor's proof.  Catches
 * and reports any errors.  Returns true if the rule succeeded, false
 * if it catches an error.  Reports there was nothing to do if the
 * rule returns its input or a null value.
 *
 * Use this only in tryRuleSoon.
 */
StepEditor.prototype._tryRule = function(rule, args) {
  var self = this;
  var result = null;
  var startTime = Date.now();
  var startSteps = Toy.getStepCounter();
  try {
    if (Toy.profileName) {
      // Collect CPU profiling information.
      console.profile(Toy.profileName);
    }
    // Applies the rule here.
    result = rule.apply(null, args);
  } catch(error) {
    this._setBusy(false);
    this.report(error);
    return;
  } finally {
    if (Toy.profileName) {
      console.profileEnd();
    }
    // Update the rule stats and show them.
    this.lastRuleTime = Date.now() - startTime;
    this.lastRuleSteps = Toy.getStepCounter() - startSteps;
    // TODO: Consider providing an event with info the ProofEditor can
    //   use to display this info -- and move this code into handler.
    this._proofEditor.containerNode
      .find('.ruleTime').text(Math.ceil(this.lastRuleTime));
    this._proofEditor.containerNode
      .find('.ruleSteps').text(Math.ceil(this.lastRuleSteps));
    // Clear the initial invisible state.
    this._proofEditor.containerNode
      .find('.ruleStats').toggleClass('invisible', false);
  }
  if (!result) {
    // Certain rules may return null indicating failure, such
    // as a rule that attempts to prove a statement.
    // The work is done, show that the prover is not busy.
    this._setBusy(false);
    this.report('Rule failed');
  } else if (result.rendering) {
      // The work is done, show that the prover is not busy.
      this._setBusy(false);
      // If there is already a rendering, Expr.justify must have found
      // that the "new" step was identical to one of its dependencies,
      // so don't try to add it.  The implementation only currently
      // supports one render per step anyway.
      this.report('nothing done');
  } else {
    // TODO: Trigger an event and let the proofDisplay show the step,
    //   removing most of this code.  It may be desirable for the
    //   proof display to trigger another event after the step is
    //   successfully rendered, triggering auto-simplification.
    try {
      var top = $(window).scrollTop();
      this.proofDisplay.addStep(result);
    } catch(error) {
      this._setBusy(false);
      Toy.logError(error);
      error.message = 'Error rendering step ' + result + ': ' + error.message;
      this.report(error);
      debugger;
      return;
    }
    this.proofDisplay.deselectStep();
    // Make sure the proof errors field is cleared.
    this.$proofErrors.hide();
    // After the browser repaints, try simplifying the step
    // and adding the result to the proof if simplification
    // has any effect.
    Toy.afterRepaint(function() {
        var trial = autoSimplify(result);
        // If autoSimplify is a no-op, do not display the result.
        var simplified = (trial.sameAs(result)
                          ? result
                          : trial);
        self._setBusy(false);
        var steps = Toy.unrenderedDeps(simplified);
        var top2 = $(window).scrollTop();
        steps.forEach(function(step) {
            self.proofDisplay.addStep(step);
          });
        checkTop(top2);
      });
  }
  checkTop(top);
};

/**
 * Supply this with an actual proof step.  If the rule has property
 * 'autoSimplify', this applies the value of the property to the step
 * as the auto-simplification.  If it returns a falsy value it will be
 * treated as a no-op (identity function).
 *
 * Otherwise if the step's rule has a "site" argument and global
 * variable Toy.autoSimplifyWholeStep is false, this simplifies the
 * site, otherwise it simplifies the whole step.
 */
function autoSimplify(step) {
  if (step.ruleArgs.length === 0) {
    // It is an axiom or theorem without parameters.
    // Simplification does not make sense, so don't do it.
    return step;
  }
  var simplifier = Toy.getRuleInfo(step).autoSimplify;
  if (simplifier) {
    // Call the rule's simplifier.  To suppress simplification,
    // supply a simplifier that does nothing.
    return simplifier(step) || step;
  }
  var path = Toy.getStepSite(step);
  if (path && !Toy.autoSimplifyWholeStep) {
    return Toy.rules.simplifySite(step, path) || assert(false);;
  } else {
    return Toy.rules.simplifyStep(step) || assert(false);
  }
}

/**
 * Returns the 1-based index of the position in the proof display
 * where the next step would be placed.  For automatic generation of
 * abbreviation variable names.
 */
StepEditor.prototype.slotIndex = function() {
  // New steps are always appended.
  return this.proofDisplay.steps.length + 1;
};

StepEditor.prototype.genAbbrevName = function() {
  return '$_' + this.slotIndex();
};

/**
 * Create and fill in part of the args array with the step or step and
 * path of the UI's selection if there is one, using the input
 * descriptor of of the StepEditor's current rule.  Currently not
 * picky about the detailed requirements of the various kinds of site
 * and step arguments.  Relies on other components to do these checks.
 */
StepEditor.prototype.argsFromSelection = function(ruleName) {
  var rule = Toy.rules[ruleName];
  var nargs = Math.max(rule.length, rule.info.maxArgs || 0);
  var args = new Array(nargs);
  var step = this.proofDisplay.selection;
  if (!step) {
    return args;
  }
  var expr = step.selection;
  var rule = Toy.rules[ruleName];
  var inputs = rule.info.inputs;
  // Fill in args information from a selection.
  if (expr) {
    var isSite = false;
    for (var type in siteTypes) {
      var input = inputs[type];
      if (input) {
        var position = Array.isArray(input) ? input[0] : input;
        args[position - 1] = step.original;
        args[position] = step.prettyPathTo(expr);
        isSite = true;
        // Only fill in one argument (pair) from the selection.
        break;
      }
    }
    if (!isSite && inputs.term) {
      var terms = inputs.term;
      var position = Array.isArray(terms) ? terms[0] : terms;
      args[position - 1] = expr;
    }
  } else {
    for (var type in stepTypes) {
      var input = inputs[type];
      if (input) {
        var position = Array.isArray(input) ? input[0] : input;
        args[position - 1] = step.original;
        // Only fill in one step.
        break;
      }
    }
  }
  return args;
};

/**
 * Fills in the arguments array with information from the form.
 */
StepEditor.prototype.fillFromForm = function(args) {
  var self = this;
  var rule = Toy.rules[this.ruleName];
  $(this.form).find('input').each(function() {
    // The "name" attribute of the input element should be the name of
    // an input type, possibly followed by some digits indicating
    // which rule argument it will supply.
    var name = this.name;
    var match = name.match(/^(.+?)(\d*)$/);
    if (match) {
      var type = match[1];
      // Non-empty when referring to one of multiple args of the same
      // type.  Then the value of the entry in rule.info.inputs is a
      // list.
      var which = match[2];
      var inputs = rule.info.inputs;
      var argNum = which ? inputs[type][which - 1] : inputs[type];
      if (!argNum) {
	throw new Error('Internal error: no input descriptor for type ' + type);
      }
      // Fill in the actual argument.
      args[argNum - 1] = self.parseValue(this.value, type);
    } else {
      Toy.logError('Unrecognized input name: ' + name);
    }
  });
};

/**
 * Parses the string value according to its type, which can
 * be any of the formTypes.  Returns an Expr for step or term
 * types.  Returns an Error if it detects the input is not valid.
 * (Does not throw.)
 */
StepEditor.prototype.parseValue = function(value, type) {
  switch (type) {
  case 'step':
  case 'equation':
  case 'implication':
    if (!value.match(/^\d+$/)) {
      return new Error('Not a step number: ' + value);
    }
    var index = Number(value) - 1;
    if (index < 0 || index >= this.proofDisplay.steps.length) {
      return new Error('No such step: ' + value);
    }
    return this.proofDisplay.steps[Number(value) - 1].original;
  case 'bool':
    var expr = Toy.parse(value);
    var type = Toy.findType(expr);
    if (!(type === Toy.boolean || type instanceof Toy.TypeVariable)) {
      // Since variables do not have known types, some expressions may
      // have unknown types, and we allow that here.
      return new Error('Not a true/false expression:' + value);
    }
    return expr;
  case 'term':
    var expr = Toy.parse(value);
    var binOps = {'+': true, '-': true, '*': true, '/': true};
    // TODO: Change all infix parsing so the following hack
    //   becomes superfluous.
    // The following is just a hack so you can type "- <expr>" as
    // input to e.g. rules.applyToBoth with the usual meaning.
    if (expr.isCall1() && expr.fn.name in binOps) {
      var x = Toy.parse('x');
      expr = Toy.lambda(x, Toy.infixCall(x, expr.fn, expr.arg));
    }
    return expr;
  case 'varName':
    if (Toy.isVariableName(value)) {
      return value;
    } else {
      return new Error('Illegal variable name: ' + value);
    }
  case 'path':
    return Toy.path(value);
  case 'string':
    if (value.length) {
      return value;
    } else {
      return new Error('Empty field');
    }
  case 'optString':
    return value;

  default:
    return new Error('Type not parseable: ' + type);
  }
};



//// RULEMENU

/**
 * Widget that displays a list of rules for the user to try
 * if desired. Constructor argument is the StepEditor it
 * applies to when updating itself.
 *
 * Public properties:
 *
 * stepEditor: StepEditor as passed to the constructor.
 * length: current number of items in the menu.
 * changed: true iff its refresh has been activated, but
 *   the update has not yet run.
 *
 * onEnter, method: pass a function to call when the mouse enters.
 * onLeave, method: pass a function to call when the mouse leaves.
 *
 * Internal-ish properties:
 * hovering: DOM node under mouse or null.
 */
function RuleMenu(proofEditor) {
  var self = this;
  self.proofEditor = proofEditor;
  self._refresher = new Toy.Refresher(self._update.bind(self));
  self.length = 0;
  self.changed = false;
  // A rule menu item node or null.  If the mouse is hovering over an
  // item at any given time, this will be it.
  self.hovering = null;

  // Rule chooser:
  var $node = ($('<div class=ruleMenu>')
               .append('<div class=ruleMenuTitle>Actions to try:</div>'));
  self.$node = $node;
  self.$items = $('<div class=rulesItems/>');
  // An intermediate DIV.  This one is set to have vertical scrolling,
  // and the rulesItems div can be inline-block to shrink-wrap itself
  // around the individual items.
  var $scrollArea = $('<div class=scrollingMenu/>');
  $scrollArea.append(self.$items);
  $node.append($scrollArea);

  // Concise code to set up pseudo-events for "enter" and "leave".
  // Note that the methods are on the instance, not the prototype.
  // Invoke via onEnter and onLeave methods.  Note: leavers are also
  // called when the menu is hidden.
  var enters = $.Callbacks();
  self.onEnter = enters.add.bind(enters);
  $scrollArea.on('mouseenter', function() {
      enters.fire();
    });
  var leavers = $.Callbacks();
  self.onLeave = leavers.add.bind(leavers);
  $scrollArea.on('mouseleave', function() {
      leavers.fire();
    });
  // Make the leavers available from methods.
  self._leavers = leavers;

  $node.on('click', '.ruleItem', function(event) {
      handleMouseClickItem(self, this, event);
      // Run the step editor's ruleChosen method with
      // the ruleName of the menu item.
      // self.stepEditor.ruleChosen($(this).data('ruleName'));
    });

  // Here are handlers for "enter" and "leave".  This code avoids
  // assuming that these events come in pairs.
  $node.on('mouseenter', '.rulesItems', function(event) {
      proofEditor.$status.toggleClass('invisible', true);
    });
  $node.on('mouseleave', '.rulesItems', function(event) {
      const visible = proofEditor.$statusDisplay.text().length > 0;
      proofEditor.$status.toggleClass('invisible', !visible);
    });
  $node.on('mouseenter', '.ruleItem', function(event) {
      handleMouseEnterItem(self, this, event);
    });
  // When the mouse leaves an item, hide any suggested step.  If a
  // request has been issued for an appropriate suggestion, but is
  // still waiting in the queue, remove it from the queue and note
  // that no request is pending.
  $node.on('mouseleave', '.ruleItem', function(event) {
      self.hovering = null;
      var $this = $(this);
      proofEditor.proofDisplay.hideSuggestion();
      var promise = $this.data('promise');
      if (promise && promise.dequeue()) {
        $this.removeData('promise');
      }
    });
}

/**
 * Handler for ruleMenu selection of a rule name.  Overall purpose is
 * to run the rule from information already available, otherwise to
 * display the input form.
 */
function handleMouseClickItem(ruleMenu, node, event) {
  // TODO: Consider generating an event here and moving
  //   much of this code elsewhere.
  const ruleName = $(node).data('ruleName');
  const proofEditor = ruleMenu.proofEditor;
  const stepEditor = proofEditor.stepEditor;
  // This code runs from a click, so a suggestion may well
  // be active.  Make sure it is not displayed.
  proofEditor.proofDisplay.hideSuggestion();
  proofEditor.stepEditor.ruleName = ruleName;
  var rule = Toy.rules[ruleName];
  if (rule) {
    var args = stepEditor.argsFromSelection(ruleName);
    if (stepEditor.checkArgs(args, rule.info.minArgs, false)) {
      tryRuleSoon(stepEditor, rule, args);
      return;
    }

    // Some args still need to be filled in; just show the rule's
    // form.

    var template = rule.info.form;
    // TODO: In the proof editor set up an event handler so the step editor
    //   can be aware of selections in the proof display (and also suppress
    //   selections instead of "selectLock").
    var step = stepEditor.proofDisplay.selection;
    var term = step && step.selection;
    var formatArgs = {term: (term && term.toHtml()) || '{term}'};
    if (template) {
      // Make this block of code into a step editor method.
      // The template is not just an empty string.
      // Note that reset of the step editor will return the hidden
      // status back to normal.
      ruleMenu.$node.toggleClass('hidden', true);
      stepEditor.clearer.removeClass('hidden');
      stepEditor.form.html(format(template, formatArgs));
      stepEditor.proofDisplay.setSelectLock(true);
      stepEditor.form.append(' <button>Go</button>');
      addClassInfo(stepEditor.form);
      if (!usesSite(rule)) {
	stepEditor.addSelectionToForm(rule);
      }
      // Focus the first empty text field of the form.
      stepEditor.form.find('input[type=text],input:not([type])').each(function() {
          if (!this.value) {
            this.focus();
            // Abort the loop.
            return false;
          }
        });
    } else {
      stepEditor.error(format('Rule needs a form: {1}', ruleName));
    }
  } else if (ruleName.slice(0, 5) === 'fact ') {
    // Values "fact etc" indicate use of rules.rewrite, and
    // the desired fact is indicated by the rest of the value.
    var siteStep = stepEditor.proofDisplay.selection;
    if (!siteStep || !siteStep.selection) {
      stepEditor.error('No selected site');
    }
    tryRuleSoon(stepEditor,
                 Toy.rules.rewrite,
                 [siteStep.original,
                  siteStep.prettyPathTo(siteStep.selection),
                  // Parsing here will cause the wff to be taken literally
                  // without potential addition of type assumptions.
                  Toy.parse(ruleName.slice(5))]);
  } else {
    assert(false, format('No such rule: {1}', ruleName));
  }
};

/**
 * Event handler for mouseenter events on RuleMenu items.
 */
function handleMouseEnterItem(ruleMenu, node, event) {
  const proofEditor = ruleMenu.proofEditor;
  const stepEditor = proofEditor.stepEditor;
  var display = proofEditor.proofDisplay;
  // Note that this item is currently hovered.
  ruleMenu.hovering = node;
  var $node = $(node);
  // The "suggestion" data property indicates that a suggestion has
  // been computed for this menu item.  It is a DOM node that may
  // have a proofStep in it.
  var working = display.suggestionMessage('Working . . . ');
  display.suggest(working);
  var suggestion = $node.data('suggestion');
  if (suggestion) {
    // A suggestion is already computed; show it.
    display.suggest(suggestion);
  } else if (!$node.data('promise')) {
    // The "promise" data property indicates that a request for a
    // step has been issued.
    var ruleName = $node.data('ruleName');
    var promise;
    if (ruleName.slice(0, 5) === 'fact ') {
      // See StepEditor.ruleChosen for essentially the same code.
      // Values "fact etc" indicate use of rules.rewrite, and
      // the desired fact is indicated by the rest of the value.
      var siteStep = display.selection;
      if (!siteStep || !siteStep.selection) {
        stepEditor.error('No selected site');
      }
      promise = sendRule('rewrite', 
                         [siteStep.original,
                          siteStep.prettyPathTo(siteStep.selection),
                          // Parsing here prevents the goal from being
                          // expanded during later parsing.
                          Toy.parse(ruleName.slice(5))]);
    } else if (Toy.rules[ruleName]) {
      // It is a rule other than a rewrite with fact.
      var rule = Toy.rules[ruleName];
      var args = stepEditor.argsFromSelection(ruleName);
      if (stepEditor.checkArgs(args, rule.info.minArgs, false)) {
        promise = sendRule(ruleName, args);
      } else {
        display.suggest(display.suggestionMessage('(needs user input)'));
      }
    } else {
      console.warn('No such rule:', ruleName);
    }
    if (promise) {
      $node.data('promise', promise);
      promise.then(function(info) {
          // The rule has successfully run.
          // First tidy up a little.
          $node.removeData('promise');
          var step = info.result.step;
          // Make note of the result, remembering its node.
          if (ruleMenu.hovering === $node[0]) {
            // At this point in time after the rule has run, if this
            // item is hovered, show the result.  Treat a null result
            // as failure of the rule.
            var node = (step
                        ? display.stepSuggestion(step)
                        : display.suggestionMessage('failed'));
            $node.data('suggestion', node);
            display.suggest(node);

          }
        })
        .catch(function(info) {
            // If the "then" throws an error, that becomes the info.
            $node.removeData('promise');
            var messageNode = display.suggestionMessage('not applicable');
            $node.data('suggestion', messageNode);
            display.suggest(messageNode);
            if (info.result) {
              console.error('Rule menu error:', info.result.message);
            } else {
              console.error('Rule menu internal error:', info);
            }
          });
    }
  }
}

/**
 * Call this any time this object's display might need to be updated.
 * The display update will occur when the event loop becomes idle.
 */
RuleMenu.prototype.refresh = function() {
  this.changed = true;
  this._refresher.activate();
};

/**
 * Updates the step suggestions and rule menu to offer items
 * reflecting the currently-selected step or term, if any.
 */
RuleMenu.prototype._update = function() {
  var self = this;
  var stepEditor = self.proofEditor.stepEditor;
  // Clear any message displays whenever this changes, as when
  // the user selects an expression or step.
  stepEditor.$proofErrors.hide();
  var $items = self.$items;
  // Remove data and event handlers from suggestions.  They have
  // not been previously removed.
  $items.find('.ruleItem').each(function() {
      var suggestion = $(this).data('suggestion');
      suggestion && $(suggestion).remove();
    });
  $items.empty();
  var step = stepEditor.proofDisplay.selection;
  var term = step && step.selection;
  // Plain object describing each menu item.
  var itemInfos = [];
  self.offerableRuleNames().forEach(function(name) {
      var ruleName = name.replace(/^xiom/, 'axiom');
      // Info is a string or array of strings.
      var info = ruleMenuInfo(ruleName, step, term,
                              stepEditor._proofEditor);
      if (Array.isArray(info)) {
        // An array occurs when a rule may be used in multiple ways,
        // notably where there are multiple possible replacements of
        // a term by equal terms.
        info.forEach(function(msg) {
            itemInfos.push({ruleName: ruleName, html: msg});
          });
      } else if (info) {
        itemInfos.push({ruleName: ruleName, html: info});
      }
    });
  
  self.offerableFacts().forEach(function(info) {
      let statement = info.goal;
      var text = statement.toString();
      var resultTerm = statement;
      if (statement.isEquation()) {
        if (statement.isCall2('=>')) {
          // Make the statement be the fact's equation.
          resultTerm = statement = statement.getRight();
        }
        // If as usual the LHS of the equation matches the selection,
        // set resultTerm to the result of substituting into the RHS.
        var step = self.proofEditor.proofDisplay.selection;
        var selection = step && step.selection;
        if (selection) {
          var subst = selection.matchSchema(statement.getLeft());
          if (subst) {
            resultTerm = statement.getRight().subFree(subst);
          }
        }
      }
      var display = '= <span class=menuResult></span>';
      if (subst) {
        // TODO: Consider using the length of the unicode in deciding
        //   what message to generate here.
        // const unicode = statement.toUnicode();
        const html = (info.definitional
                      ? 'definition of ' + statement.getLeft().func().name
                      : 'using ' + Toy.trimParens(statement.toHtml()));
        display += (' <span class=description>' + html + '</span>');
      }
      // Value of the option; format of "fact <fact text>"
      // indicates that the text defines a fact to use in
      // rules.rewrite.
      var info = {ruleName: 'fact ' + text,
                  html: display,
                  result: resultTerm};
      itemInfos.push(info);
    });
  itemInfos.sort(function(a, b) {
      return a.html.localeCompare(b.html);
    });
  var items = itemInfos.map(function(info) {
      var $item = $('<div class="ruleItem noselect"/>');
      $item.html(info.html);
      if (info.result) {
        $item.find('.menuResult').append(info.result.renderTerm());
      }
      $item.data('ruleName', info.ruleName);
      return $item
    });
  self.length = items.length
  self.changed = false;
  $items.append(items);
  if (term) {
    // If there is a selected term, render it and any right neighbor term,
    // and insert the renderings into their slots in menu items.
    var $term = $(term.copyForRendering().renderTerm());
    $items.find('.menuSelected').append($term);
    var rightTerm = Toy.getRightNeighbor(step, term);
    var $right = '?';
    if (rightTerm) {
      var $right = $(rightTerm.copyForRendering().renderTerm());
    }
    $items.find('.menuRightNeighbor').append($right);
  }
  self.$node.toggleClass('hidden', items.length === 0);
  if (items.length === 0) {
    // The menu can be hidden by clicks within it, and that does not
    // trigger a mouse leave event.
    self._leavers.fire();
  }

  // TODO: Consider updating the advice using Promises.
  proofEditor.$advice.toggleClass('hidden', self.length != 0);
};

/**
 * Returns a list of names of rules that are "offerable" in the
 * sense of "offerable" returning true and offerApproved returning true.
 */
RuleMenu.prototype.offerableRuleNames = function() {
  var matches = [];
  for (var name in Toy.rules) {
    if (this.offerable(name) && this.offerApproved(name)) {
      matches.push(name);
    }
  }
  matches.sort();
  return matches;
};

/**
 * Policy-based rule offering policy function based on this.showRules
 * and rule labels.  Returns a truthy value iff current policy is to
 * show the rule.
 */
RuleMenu.prototype.offerApproved = function(name) {
  const editor = this.proofEditor;
  var labels = Toy.rules[name].info.labels;
  if (editor.showRules.indexOf(name) >= 0) {
    return true;
  }
  const selStep = editor.proofDisplay.selection;
  switch (editor.showRuleType) {
  case 'all':
    return true;
  case 'algebra':
    var expr = selStep && selStep.selection;
    return (expr && !expr.isReal()
            ? false
            : labels.algebra || labels.display);
  case 'general':
    return labels.general || labels.basic || labels.display || labels.algebra;
  default:
    throw new Error('Bad rule policy value: ' + editor.showRuleType);
  }
};

/**
 * Returns true iff the rule name can be offered by the UI.
 * Only rules with a "form" property are offerable at all.  If so --
 *
 * If the rule has a precheck and a single "inputs" declaration
 * of a kind that works with a selection, run the precheck and
 * return false if it is falsy.
 *  
 * Else if the proof has a current selection, the rule is offerable if
 * acceptsSelection returns true given the selected step and rule
 * name.
 *
 * Otherwise only rules that take no step and no site are offerable.
 */
RuleMenu.prototype.offerable = function(ruleName) {
  var rule = Toy.rules[ruleName];
  var info = rule.info;
  // TODO: Test and then hopefully remove this test, which looks
  //   obsolete.
  if (!('form' in info)) {
    return false;
  }
  const editor = this.proofEditor;
  var step = editor.proofDisplay.selection;
  if (step) {
    // Something is selected.
    var precheck = rule.precheck;
    var term = step.selection;
    var inputs = info.inputs;
    // See if the rule has a precheck that can "rule it out".
    // The rule must have a single input of a site or step type.
    if (precheck && Toy.mapSize(info.inputs) == 1 &&
        (term
         // This list needs to match siteTypes.
         ? (inputs.site || inputs.bindingSite || inputs.reducible ||
            inputs.term)
         // This list needs to match stepTypes.
         : inputs.step || inputs.equation || inputs.implication)) {
      var ok = (inputs.term
                ? precheck(term)
                : term
                ? precheck(step, step.pathTo(term))
                : precheck(step));
      if (!ok) {
        return false;
      }
    }
    // Check if the rule accepts the selection.
    if (acceptsSelection(step, ruleName)) {
      // If the rule has a "toOffer" property, apply it as a further
      // test of offerability.
      var offerTest = info.toOffer;
      if (info.toOffer) {
        return offerTest(step, step.selection);
      }
      return true;
    }
  } else if (!info.form) {
    // The form property is present, but nothing in it, so
    // arguments cannot come from the form.
    return false;
  } else {
    // No selection, the rule must not require a step or site.
    for (type in info.inputs) {
      // Use "in", the type will not be an object method name.
      if (type in stepTypes || type in siteTypes) {
        return false;
      }
    }
    return true;
  }
};

/**
 * Returns a list of fact info objects for facts that are offerable
 * in the UI, currently all equational facts whose LHS matches the
 * currently selected term.
 *
 * In algebra mode, if the LHS is atomic, does not offer unless the
 * fact has the "algebra" label.
 */
RuleMenu.prototype.offerableFacts = function() {
  var self = this;
  var facts = [];
  var step = self.proofEditor.proofDisplay.selection;
  if (step) {
    var expr = step.selection;
    var TypeConstant = Toy.TypeConstant;
    // Returns true (a mismatch) iff both Exprs have types that
    // are type constants (in practice real or boolean), and the
    // types are not the same.  This is a crude check, but covers
    // the cases of usual interest.
    // TODO: Properly unify the types, probably as part of schema
    //   matching, and eliminate this hack function.
    function typesMismatch(e1, e2) {
      var e1Type = e1.hasType();
      var e2Type = e2.hasType();
      return (e1Type instanceof TypeConstant &&
              e2Type instanceof TypeConstant &&
              // Perhaps compare the names of the type constants?
              e1Type != e2Type);
    }
    if (expr) {
      var mode = self.proofEditor.showRuleType;
      Toy.eachFact(function(info) {
          var goal = info.goal;
          if (!goal.isRewriter()) {
            return;
          }
          var lhs = goal.eqnLeft();
          if (typesMismatch(expr, lhs)) {
            return;
          }
          if (info.labels.higherOrder && mode != 'all') {
            // Do not offer facts with higher-order variables until
            // we can match them properly when generating the menu.
            return;
          }
          if (expr.matchSchema(lhs)) {
            if (mode == 'algebra') {
              if (info.labels.algebra) {
                facts.push(info);
              }
              // Otherwise don't show the fact in algebra mode.
            } else if (mode == 'general') {
              // Only show desimplifiers in "everything" mode.
              // TODO: Include them as "introducers" in both "general"
              //   mode and "everything" modes.
              if (!info.desimplifier) {
                facts.push(info);
              }
            } else {
              assert(mode == 'all', 'Invalid mode {1}', mode);
              facts.push(info);
            }
          }
      });
    }
  }
  return facts;
};

/**
 * This matches a step against the inputs descriptor of an inference
 * rule.  The step is the selected proof step, ruleName is the name of
 * the rule to match against.  Only call this if a step or part of a
 * step is selected.
 *
 * If something is selected, this accepts rules that can use that input
 * as an argument.
 */
function acceptsSelection(step, ruleName) {
  var info = Toy.rules[ruleName].info;
  var argInfo = info.inputs;
  if (!argInfo) {
    // If there is no information about arguments, fail.
    return false;
  }
  // Selected expression (within a step).
  var expr = step.selection;
  if (expr) {
    if (info.isRewriter && info.using) {
      // The rule has a "rewriting template", given as the name
      // of the fact to use in rewriting.
      assert(typeof argInfo.site === 'number',
             function() {
               return 'Rule ' + ruleName + ' must use exactly 1 site.';
             });
      // Check that the expression matches the LHS of the template.
      return !!expr.findSubst(info.using.unHyp().getLeft());
    } else {
      // Otherwise OK if it takes a site, or is a proper binding site
      // or a beta-reducible expression.
      // 
      // TODO: prevent selection of bound variables as terms.
      return (argInfo.site
              || argInfo.term
              || (argInfo.bindingSite && expr instanceof Toy.Lambda)
              || (argInfo.reducible
                  && expr instanceof Toy.Call
                  && expr.fn instanceof Toy.Lambda));
    }
  } else {
    // If the rule needs a site, do not accept just a step.
    return (!argInfo.site &&
            (argInfo.step
             || (argInfo.equation && step.unHyp().isCall2('='))
             || (argInfo.implication && step.unHyp().isCall2('=>'))));
  }
}

/**
 * Produces a rule menu entry from a ruleName, with "axiom"
 * potentially shortened to "xiom".  Called with a (rendered) step if
 * there is a selection, the selected term if a term is selected, and
 * the menu's ProofEditor.
 *
 * This returns either a falsy value (including the empty string),
 * indicating the rule will not be offered, or a string with the menu
 * HTML, or an array of strings, indicating multiple menu items for
 * this rule with the possibly selected step and term.  Returned
 * strings should be HTML text.
 *
 * If there is a selected term, it can be formatted using {term} in
 * the rule's "menu" format string, or {right} for the term's
 * right-hand neighbor when there is one.
 */
function ruleMenuInfo(ruleName, step, term, proofEditor) {
  ruleName = ruleName.replace(/^xiom/, 'axiom');
  var info = Toy.rules[ruleName].info;
  if (info.menuGen) {
    var gen = info.menuGen;
    return gen(ruleName, step, term, proofEditor);
  }
  if (Toy.isEmpty(info.inputs)) {
    // It is an axiom or theorem with no inputs.
    if (info.menu) {
      return info.menu;
    }
    var thm = Toy.getTheorem(ruleName);
    var thmText = Toy.trimParens(thm.unHyp().toHtml());
    if (ruleName.substring(0, 5) === 'axiom') {
      return 'axiom ' + thmText;
    } else {
      return 'theorem ' + thmText;
    }
  } else {
    // If there are inputs uses info.menu or some fallback.  This
    // defers the rendering work to the RuleMenu code where it is more
    // convenient and the HTML has been converted to DOM structure.
    var formatArgs = {term: '<span class=menuSelected></span>',
                      right: '<span class=menuRightNeighbor></span>'};
    if (info.menu) {
      return Toy.format(info.menu, formatArgs);
    } else {
      // TODO: Reconcile use of math markup here vs. non-use in menus.
      return Toy.mathMarkup(info.basicTooltip || 'menu?');
    }
  }
}

/**
 * Ensures that the page's scrollTop (pageYOffset) remains at the
 * level given by its argument, recorded previously.  This helps work
 * around undesirable and weird scrolling induced by inserting or
 * deleting flexbox nodes in the DOM.  There is also one similar
 * workaround in rendering.js.
 */
function checkTop(oldTop) {
  function reset() {
    var top = $(window).scrollTop();
    if (top !== oldTop) {
      /*
      console.log(Toy.format('Resetting scrolltop from {1} to {2} at {3}.',
                             top, oldTop, new Date().toISOString()));
      */
      $(window).scrollTop(oldTop);
    }
  }
  reset();
  // Uncomment this to reset again a little bit later.
  // window.setTimeout(reset, 100);
}

/**
 * Enqueue an RPC message to an inference worker, returning a Promise
 * to receive the result.
 */
function sendRule(name, args) {
  return Toy.rpcQueue.enqueue({action: 'runRule', name: name, args: args});
}


//// INITIALIZATION

/**
 * RPC setup for Mathtoys:
 */
$(function () {
    var receiver = {
      actions: {
        // The "rule" action returns a resulting step as its "step"
        // property, or standard error information in case of error.
        runRule: function(message) {
          var step = Toy.rules[message.name].apply(null, message.args);
          return {step: step};
        }
      }
    };
    var fakeWorker = new Toy.FakeRpcWorker(receiver);
    var queue = new Toy.MessageQueue();
    queue.addWorker(fakeWorker);
    // This is the endpoint for accessing worker threads via RPC.
    Toy.rpcQueue = queue;
  });


// For testing:
Toy.autoSimplify = autoSimplify;

// Global variable, name to use for CPU profiles, or falsy to disable:
Toy.profileName = '';

// Global setting controlling auto-simplification.
Toy.autoSimplifyWholeStep = true;

// Export public names.
Toy.stepTypes = stepTypes;
Toy.siteTypes = siteTypes;

Toy.ProofEditor = ProofEditor;
Toy.StepEditor = StepEditor;

Toy.tryRuleSoon = tryRuleSoon;

})();
