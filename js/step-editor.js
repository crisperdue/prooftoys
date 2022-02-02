// Copyright Crispin Perdue.  All rights reserved.

// Set everything up immediately on load, avoiding changes to
// the global environment except through namespace "Toy".
(function() {

'use strict';

// Make application assertions available through "assert".
const assert = Toy.assertTrue;

const abort = Toy.abort;
const format = Toy.format;
const dom = Toy.dom;
const TermSet = Toy.TermSet;
const rules = Toy.rules;


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
 * If this is the first proof editor created on the page, loads all
 * documents named "Theory *", in alphabetical order by name before
 * any document specified by docName.  If the docName is one of those
 * "theory" documents, only loads them up to that one.  The effect is
 * to load the "theory" documents automatically into the page.
 *
 * Optional argument "options", plain object with properties:
 * 
 * docName: if given, overrides the default document name.
 * loadDoc: if false, suppresses initial loading of the document.
 *
 * Public properties:
 *
 * proofDisplay: ProofDisplay for the proof being edited.
 * containerNode: jQuery object for outermost DOM node for the display.
 * $proofButtons: jQuery object for the row of "proof buttons".
 * stepEditor: StepEditor for the proof being edited.
 * proofEditorId: identifies this editor for purposes of restoring its
 *   operating state from localstorage across visits / page loads.
 *   Consists of the pathname part of the browser "location", "#", and
 *   an integer sequence number of the editor within the page.  In
 *   principle an editor could also be assigned an ID explicitly during
 *   editor initialization immediately after creation.
 * fromDoc: boolean, true if state loaded from a document in constructor.
 * initialSteps: string with initial steps to reset to on "clear proof".
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
 * showRuleType: Selects type of rules to show, as determined by labelApproved.
 *   Takes effect when this editor is reset.
 * showRules: List of individual rules to show.  Takes effect when this
 *   editor is reset.
 */
function ProofEditor(options_arg) {
  const self = this;
  const options = Object.assign({loadDoc: true}, options_arg);
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

  // Top-level element of the proof editor display:
  const $node = this.containerNode =
    $('<div class="proofEditor logicZone"></div>');

  const stepEditor = new StepEditor(this);
  self.stepEditor = stepEditor;
  // This provides a coordinate system for absolute positioning.
  const $formParent = $('<div style="position: relative">');
  $formParent.append(stepEditor.form);

  const proofButtons = buildProofButtons(self);
  self.$copyText = proofButtons.$copyText;
  self.$proofButtons = proofButtons.$node;

  self._wksControls = buildWksControls(self);

  var menu = self.ruleMenu = new RuleMenu(self);

  // This element is for messages about status of solving the problem.
  // It always occcupies space, but can be hidden by CSS rules.  It
  // can have an "empty" class if the text is cleared, i.e. when there
  // is no progress to report.  It is hidden when empty or when the
  // mouse pointer is within the rule menu, to stay out of the way of
  // step suggestions.
  var $status = $('<div class="solutionStatus">');
  var $statusDisplay = $('<div class=solutionStatusDisplay>');
  $status.append($statusDisplay);
  self.$status = $status;
  self.$statusDisplay = $statusDisplay;

  // The equations.html page "Try a different problem" button goes
  // at the end of this $header div.
  let $header =
    ($('<div class=proofEditorHeader>')
     .append('<b>Worksheet "<span class=wksName></span>"</b>'));
  let $readOnly =
    $(`<p class=ifProofLoadError><i><b style="color:red">
      An error occurred executing the proof.</b><br>
      View the workspace as text to see steps not executed.<br>
      For safety this worksheet is read-only.</i></p>`);
  this.containerNode
    .append($header)
    .append($readOnly)
    .append(mainDisplay.node)
    .append($status)
    .append($formParent)
    .append(proofButtons.$node)
    .append(this._wksControls.node)
    .append(stepEditor.$proofErrors)
    .append(menu.$node);
  this.setEditable(true);

  // Restore editor state.
  const state = Toy.getSavedState(self);
  // The (default) document name is the proofEditorId.
  self.setDocumentName(options.docName ||
                       (state
                        ? state.docName
                        // By default set the document name according
                        // to the URI path, and the editor number if
                        // that is greater than one.
                        : this.proofEditorId));

  // Prepare to write out proof state during refresh, so basically
  // whenever it changes.
  this._refresher = new Toy.Refresher(function() {
      self._updateGivens();
      if (self.isEditable()) {
        self.saveProofState();
      }
      // Set (or clear) the message in the $status box.
      var steps = mainDisplay.steps;
      var len = steps.length;
      if (len) {
        var step = steps[len - 1];
        var message = self.progressMessage(step.original);
        $statusDisplay.empty();
        $statusDisplay.append(message || '&nbsp;');
        $status.toggleClass('empty', !message);
      } else {
        $status.toggleClass('empty', true);
      }
    });

  // Restores proof state if possible from the recorded document name,
  // but only after a short delay.  The delay causes this to honor
  // any setting of the editor document name, and is conceptually compatible
  // with data stores that may return data asynchronously.
  if (Toy.isDocHeldFrom(self._documentName, self)) {
    // Caution the user.  The isDocHeldFrom test seems to be unreliable,
    // at least during development, so just caution rather than
    // setting editable to false.
    //
    // TODO: Consider actively helping the user avoid problems instead of
    //   cautioning.  Probably use IndexedDB via idb or idb-keyval to
    //   store editor state; and either auto-update proofs as needed
    //   on window focus, or perhaps auto-create new "branches" if
    //   inconsistent changes are detected, e.g. append -1, -2, ...
    //   to the document name.
    //
    //   All of this would imply ditching the heartbeat mechanism, which
    //   is inherently unreliable anyway.
    //
    //   In the future when there are remote stores it probably makes
    //   sense to check if a document has changed before writing it
    //   remotely.  And writing remotely would probably be explicit,
    //   e.g.  with a "Save" command.
    Toy.alert('Caution: editing may be in progress in another tab/window');
  }
  if (options.loadDoc) {
    const docName = self._documentName;
    let names = [docName];
    if (nextProofEditorId <= 2) {
      // In other words, this is the first proof editor on this page.
      const theories = (Toy.lsDocs()
                        .filter(nm => nm.startsWith('Theory '))
                        .sort());
      const index = theories.indexOf(docName);
      if (index >= 0) {
        // This removes everything starting at the index.
        theories.splice(index);
      }
      names = theories.concat(docName);
    }
    for (const nm of names) {
      if (self.openDoc(nm)) {
        self.fromDoc = true;
      } else {
        break;
      }
    }
  }

  //// Event handlers

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
      if (!within($target, '.proofErrors, .stepEditor, .ruleForm')) {
        // Similarly, most clicks hide the proof errors display.
        self.containerNode.removeClass('proofErrorsVisible');
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
 */
function buildProofButtons(editor) {
  // Add the group of buttons.
  // The proofButtons class is used in some examples.
  const $proofButtons = $('<div class="proofButtons">');

  const $clearProof = $('<input type=button value="Clear work">');
  const css = {float: 'right',
               backgroundColor: '#d9534f',
               color: 'white'
  };
  $clearProof.css(css);

  // Toggling the proof state display visibility with a button.
  const $wksButton = $('<input type=button value="Worksheets... ">');

  // This holds textual representation of the latest selected term.
  // It is writable so the user can scroll it horizontally (using the
  // text cursor).  Alternatively could be readonly.
  const $copyText = $('<input class=copyText disabled>');
  // The fa and fa-copy classes put a "copy" icon into the
  // text of the button.
  const $copyButton = $('<button class="fa fa-copy">');
  $copyButton.css({fontSize: '.8rem'});

  // The ruleStats are visible except when a proof is brand new and
  // there is nothing to show.
  const $ruleStats = $('<span class="ruleStats invisible">' +
                       '<span class=ruleSteps></span> steps, ' +
                       '<span class=ruleTime></span> msec</span>'
                       );

  $proofButtons.append('Selection');
  $proofButtons.append($copyText);
  $proofButtons.append($copyButton);
  $proofButtons.append($wksButton, $('<s class=em>'));
  $proofButtons.append($ruleStats, $('<s class=em>'));
  $proofButtons.append($clearProof);

  // Main and worksheet controls event handlers

  $copyButton.on('click', function(event) {
      Toy.copyToClipboard($copyText.val());
      // I tried using the TOUCHDOWN event and event.preventDefault()
      // in Chrome, without success.
      $copyText.select();
    });

  $wksButton.on('click', function() {
      editor._wksControls.toggle();
    });
  $clearProof.on('click', function() {
      if (window.confirm('Do you really want to clear your work?')) {
        editor.clear();
      }
    });
  const result = {
    $node: $proofButtons,
    $copyText: $copyText,
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
 *
 * Pressing the Worksheet button brings up the controls.
 * They stay up until you leave the area.
 * The Open and Delete buttons also leave their document lists
 * up until you leave the area, so you can swiftly delete multiple
 * files or browse from one to another in a minimal number of steps.
 */
function buildWksControls(editor) {
  const $outermost = $('<div class="wksControlsOuter transFade hidden">');
  const $controls = $('<div class="wksControls">');
  $outermost.append($controls);
  $controls.append('<div class=wksTitle>' +
                   'Current worksheet is "<span class=wksName></span>"</div>');
  const $buttons = $('<div class=wksButtons>');
  $controls.append($buttons);

  $buttons.append(makeButton('Open... ', 'openButton'),
                  makeButton('Save as... ', 'saveAsButton'),
                  makeButton('Copy to... ', 'copyToButton'),
                  makeButton('Delete... ', 'deleteButton'),
                  makeButton('View as text', 'previewButton'));

  const $inputs = $('<div class=wksInputs>');
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
    '<p>\n' +
    'The text area below contains the current state of the proof in textual\n' +
    'form.  You can save the state of your work by copying this text into a\n' +
    'document of your choice.  To restore the state at some time in the\n' +
    'future, paste it back then press "Restore proof".\n' +
    '<p style="margin-bottom: 0">\n' +
    '<input class=restoreProof type=button value="Restore proof">\n' +
    '<input class=hideProofState type=button value="Close"><br>\n' +
    '<textarea class=proofStateArea rows=15></textarea>\n' +
    '</div>\n';
  const $proofPreview = $(stateDisplayHtml);
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
    if (!wantHidden) {
      resetDisplay();
    }
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
    const docs = Toy.lsDocs();
    const slash = docs.filter(nm => nm.startsWith('/')).sort();
    const noslash = docs.filter(nm => !nm.startsWith('/')).sort();
    // Display names not starting with "/" before the rest.
    noslash.concat(slash).forEach(function(name) {
        if (name === editor.getDocumentName()) {
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

  $outermost.on('mouseenter', function(event) {
    $outermost.toggleClass('hidden', false);
  });
  $outermost.on('mouseleave', function(event) {
    $outermost.toggleClass('hidden', true);
  });
  $openersArea.on('mouseenter', function(event) {
    $openersArea.toggleClass('hidden', false);
  });
  $openersArea.on('mouseleave', function(event) {
    $openersArea.toggleClass('hidden', true);
  });

  $deletersArea.on('mouseenter', function(event) {
    $deletersArea.toggleClass('hidden', false);
  });
  $deletersArea.on('mouseleave', function(event) {
    $deletersArea.toggleClass('hidden', true);
  });

   
  // Handler for the "restore proof" button.  Restores proof state from
  // the text area.
  function restoreProof() {
    if (Toy.catchAborts(() => {
          editor.restoreState();
          result.hide();
        })) {
      // For some reason the reporting gets undone unless deferred.
      Toy.soonDo(() => editor.stepEditor.report(Toy.thrown));
    }
  }
  $outermost.find('.restoreProof').on('click', restoreProof);

  // Closing the state display:
  $outermost.find('.hideProofState').on('click', function() {
      $outermost.find('.proofPreview').addClass('hidden');
    });

  // Buttons that open up the ultimate action UIs.
  $controls.find('.openButton').on('click', function() {
      resetDisplay();
      showDocs($openersArea);
      $openersArea.toggleClass('hidden', false);
    });
  $controls.find('.saveAsButton').on('click', function() {
      toggleControl($saveAs);
    });
  $controls.find('.copyToButton').on('click', function() {
      toggleControl($copyTo);
    });
  $controls.find('.deleteButton').on('click', function() {
      resetDisplay();
      showDocs($deletersArea);
      $deletersArea.toggleClass('hidden', false);
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
      if (!success) {
        Toy.alert('Could not open worksheet ' + text);
      }
    });
  $deletersArea.on('click', '.docName', function() {
      const name = $(this).text();
      if (name === editor.getDocumentName()) {
        $message.text('Cannot delete the current document.');
      } else {
        if (window.confirm('Do you really want to delete ' + name + '?')) {
          Toy.rmDoc(name);
          $message.text('Deleted "' + name + '"');
          toggleControl($message);
        }
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

  const $stateArea = $outermost.find('.proofStateArea');

  // Methods

  const result = {
    node: dom($outermost),
    hide: function() {
      $outermost.toggleClass('hidden', true);
     },
    show: function() {
      resetDisplay();
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
  // Set the document name into all nodes of class wksName.
  self.containerNode.find('.wksName').text(name);
  // Remember the state of this editor.
  // TODO: Replace the following with some form of state observation.
  if (self.proofDisplay.isEditable()) {
    // Only note the state within this context if editing the proof,
    // so that otherwise the document can be edited by other editors.
    // (See Toy.isDocHeldFrom.)
    Toy.noteState(self, {docName: self._documentName});
  }
  // Visiting the same page in another tab then will cause its proof
  // editor to visit the same document as this one.
  Toy.saveState(self, {docName: self._documentName});
};

/**
 * Attempts to open the named document in this proof editor, setting
 * the editor's document name and loading its proof state.  Returns
 * true iff the document is successfully loaded, else false.
 */
ProofEditor.prototype.openDoc = function(name) {
  const proofData = Toy.readDoc(name);
  // TODO: Check for possible active editing in another tab/window.
  if (proofData) {
    this.setEditable(true);
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
  this.stepEditor.hideForm();
  const stepsInfo = this.initialSteps;
  const steps = (stepsInfo ? Toy.decodeSteps(stepsInfo) : []);
  // TODO: Respond in some way to any error in decoding.
  this.proofDisplay.setSteps(steps);
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
  // TODO: Reimplement this.
  console.log('Unimplemented setRulesMode');
};

/**
 * Add a step to the proof.
 */
ProofEditor.prototype.addStep = function(step) {
  this.proofDisplay.addStep(step);
};

ProofEditor.prototype.getLastStep = function() {
  return this.proofDisplay.getLastStep();
};

/**
 * Gets the state of the proof, in string form.
 */
ProofEditor.prototype.getStateString = function() {
  return Toy.encodeSteps(this.proofDisplay.steps);
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
  if (steps instanceof Error) {
    this.proofDisplay.setSteps(steps.steps);
    this.setEditable(false);
    this.toggleClass('proofLoadError', true);
  } else {
    this.proofDisplay.setSteps(steps);
    this.toggleClass('proofLoadError', false);
    Toy.soonDo(() => this.containerNode.find('.proofSteps').scrollTop(1e9));
  }
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
  this.toggleClass('editable', value);
  // The following set the state of the display and hide or show the
  // step editor.
  this.proofDisplay.setEditable(value);
};

/**
 * Toggles a CSS class on the main node of this proof editor.
 */
ProofEditor.prototype.toggleClass = function(className, truthy) {
  this.containerNode.toggleClass(className, truthy);
};


//// PROOF STEP EDITOR

// CSS class names beginning with "sted-" are reserved to
// the step editor.  Access to nodes through their class
// should always work in the context of the step editor's node.

// All types that can be entered in a form.  Omits site, bindingSite,
// and reducible, which are currently not supported in forms.  See
// See comments above addRule in engine.js for details on the types.
//
// TODO: Make this a Set.
var formTypes = {
  term: true,
  bool: true,
  path: true,
  varName: true,
  string: true,
  optString: true,
  step: true,
  equation: true,
  implication: true
};

// Datatypes that refer to proof steps.
//
// TODO: Make this a Set.
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
 * form: jQuery DIV containing the entire input form
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

  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<button class="fa fa-times-circle-o sted-clear" title="Clear the input">');
  const $form = self.form = $('<div class="ruleForm hidden"></div>');

  $form.append(self.clearer, '<span class=customForm></span>');
  // Install event handlers.
  self.clearer.on('click', function() {
    self.hideForm();
    self._proofEditor.ruleMenu.suppressing = false;
  });

  $form.append(' <button class=go>Go</button>');
  self.form.on('click', 'button.go', function() {
    self.tryRuleFromForm();
  });

  // Keyboard events bubble to here from the inputs in the form.
  self.form.on('keydown', function(event) {
    if (event.keyCode == 13) {
      // <enter> key was hit
      self.tryRuleFromForm();
    }
  });

  self.$proofErrors = $('<div class="proofErrors hidden"></div>');
  // Always clear the errors when clicked.
  self.$proofErrors.on('click', '.clearer', function() {
    self.$proofErrors.hide();
  });
}

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
  $proofErrors.html('<button class=clearer>X</button>');
  $proofErrors.show();
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
 * Hides the error display.
 */
StepEditor.prototype.clearError = function() {
  this.$proofErrors.hide();
};

/**
 * Shows the form for entering info for the selected rule.
 */
StepEditor.prototype.showForm = function() {
  this.form.show();
  this.formShowing = true;
  this.proofDisplay.setSelectLock(true);
  this._proofEditor.containerNode.addClass('ruleFormVisible');
  this._proofEditor.ruleMenu.suppressing = true;
};

/**
 * Hides the rule entry form.
 */
StepEditor.prototype.hideForm = function() {
  this.form.hide();
  this.formShowing = false;
  this.proofDisplay.setSelectLock(false);
  this._proofEditor.containerNode.removeClass('ruleFormVisible');
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
 * Adds class=step, class=term, etc. to each form element according to
 * its name -- same as the name, but stripping off any numeric suffix,
 * e.g. step2 => step.  Also prevents autocompletion of fields named
 * "term" because various sites add autosuggest entries to such
 * fields.
 *
 * TODO: Be smarter about autocompletion.
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
	    || (fieldType == 'equation' && step.getMain().isCall2('='))
	    || (fieldType == 'implication' && step.getMain().isCall2('=>'))) {
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
StepEditor.prototype.tryRuleFromForm = function() {
  // TODO: Get it together on failure reporting here.
  var ruleName = this.ruleName;
  var rule = Toy.rules[ruleName];
  var minArgs = rule.info.minArgs;
  var args = this.argsFromSelection(ruleName);
  if (this.fillFromForm(ruleName, args) &&
      this.checkArgs(args, minArgs, true)) {
    this.hideForm();
    tryRuleSoon(this, rule, args);
  }
};

/**
 * Requests running the rule with the given args as soon as the UI has
 * opportunity to repaint, and indicates that the prover is working.
 */
function tryRuleSoon(stepEditor, rule, args) {
  args.forEach(function(arg) {
      if (Toy.isProved(arg) && arg.isRendered()) {
        // Really all step arguments to all steps everywhere should be
        // non-renderable in the current implementation, but this situation
        // is arguably a greater risk than others.
        console.error('Argument step ' + arg.stepNumber + ' is renderable.');
      }
    });
  stepEditor._proofEditor.containerNode.addClass('waitingForProver');
  stepEditor._proofEditor.ruleMenu.suppressing = true;
  // Try running the rule once the UI shows that the prover is working.
  Toy.afterRepaint(stepEditor._tryRule.bind(stepEditor, rule, args));
}

/**
 * Tries to run the given rule (function) with the given rule
 * arguments, adding the result to this step editor's proof.  Catches
 * and reports any errors.  Reports there was nothing to do if the
 * rule returns its input, or that the "rule failed" if it returns
 * null.  If the rule returns exactly true, this succeeds although
 * there is no step to insert.
 *
 * Use this only in tryRuleSoon.
 */
StepEditor.prototype._tryRule = function(rule, args) {
  var self = this;
  var result = null;
  var startTime = Date.now();
  var startSteps = Toy.getStepCounter();
  const editor = this._proofEditor;

  // Set to true in case of possible (deferred) autoSimplify.
  let deferCleanup = false;
  // Cleans up lockouts on interactivity.
  const cleanup = () => {
    editor.proofDisplay.setSelectLock(false);
    editor.containerNode.removeClass('waitingForProver');
    editor.ruleMenu.suppressing = false;
  }

  const caught = Toy.catchAborts(() => {
    if (Toy.profileName) {
      // Collect CPU profiling information.
      console.profile(Toy.profileName);
    }
    // Applies the rule here.
    result = rule.apply(null, args);
  });
  if (caught instanceof Error && caught.reportToUser) {
    // If a thrown error is reportable, treat it as the result,
    // reporting it to the user.
    result = caught;
  }
  // These UI actions could even be done before running the rule,
  // because the user doesn't see them until this method completes.
  // this.hideForm();

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

  // A rule may abort (throw), or certain rules may return null
  // indicating failure, such as a rule that attempts to prove a
  // statement.
  if (result === true) {
    // Do nothing.
  } else if (result instanceof Error || !(result instanceof Toy.Step)) {
    // It is possible to display more information about thrown
    // errors (aborts), but it may not be helpful to the user.
    const message = result ? result.message : 'Rule does not apply';
    this.report(message);
  } else if (result.rendering) {
      // If there is already a rendering, Expr.justify must have found
      // that the "new" step was identical to one of its dependencies,
      // so don't try to add it.  The implementation only currently
      // supports one render per step anyway.
    this.report('nothing done');
  } else {
    // Success!
    var top = $(window).scrollTop();
    // TODO: Trigger an event and let the proofDisplay show the step,
    //   removing most of this code.  It may be desirable for the
    //   proof display to trigger another event after the step is
    //   successfully rendered, triggering auto-simplification.
    const error = Toy.catchAborts(() => {
      this.proofDisplay.addStep(result);
    });
    if (error) {
      if (error instanceof Error) {
        console.error(error);
        error.message = 'Error rendering step ' + result + ': ' + error.message;
        this.report(error);
      }
      cleanup();
      return;
    }
    // Clean up after any autosimplification.
    deferCleanup = true;
    // The new step is successfully rendered.
    this.proofDisplay.deselectStep();
    // Make sure the proof errors field is hidden.
    this.clearError();
    // After the browser repaints, try simplifying the step
    // and adding the result to the proof if simplification
    // has any effect.
    Toy.afterRepaint(function() {
      cleanup();
      var trial = autoSimplify(result);
      // If autoSimplify is a no-op, do not display the result.
      var simplified = (trial.sameAs(result)
                        ? result
                        : trial);
      var steps = Toy.unrenderedDeps(simplified);
      var top2 = $(window).scrollTop();
      steps.forEach(function(step) {
        self.proofDisplay.addStep(step);
      });
      checkTop(top2);
      // Scroll the proof steps DIV all the way to the bottom
      // so the new step(s) are visible.
      editor.containerNode.find('.proofSteps').scrollTop(1e9)
    });
  }
  if (!deferCleanup) {
    cleanup();
  }
  if (typeof top == 'number') {
    checkTop(top);
  }
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
    return Toy.rules.simplifyFocalPart(step) || assert(false);
  }
}

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
 * Tries to fill in the arguments array with information from the form.
 * Returns true / false for success or failure.
 */
StepEditor.prototype.fillFromForm = function(ruleName, args) {
  var self = this;
  var rule = Toy.rules[ruleName];
  let success = true;
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
      try {
        // Try to fill in the actual argument.
        args[argNum - 1] = self.parseValue(this.value, type);
      } catch(e) {  // Not awful, only hides errors in parseValue.
        self.report(e.message);
        success = false;
        return false;
      }
    } else {
      console.error('Unrecognized input name: ' + name);
    }
  });
  return success;
};

/**
 * Parses the string value according to its type, which can
 * be any of the formTypes.  Returns an Expr for step or term
 * types.  Returns an Error if it detects the input is not valid.
 * (Does not throw.)
 *
 * TODO: Make this behave consistently, e.g. for parsing terms,
 *   and make fillFromForm behave gracefully with it.
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
    var type = expr.type;
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
    return Toy.asPath(value);
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
 * Internal-ish properties:
 * hovering: DOM node under mouse or null.
 */
function RuleMenu(proofEditor) {
  var self = this;
  self.proofEditor = proofEditor;
  self._refresher = new Toy.Refresher(self._update.bind(self));
  // Total number of menu items.
  self.length = 0;
  // A rule menu item node or null.  If the mouse is hovering over an
  // item at any given time, this will be it.
  self.hovering = null;
  // True iff we are suppressing actions from menu item events
  // (enter and click).
  self.suppressing = false;

  const $modeList = $('<div class=modeList>');
  self.$modeList = $modeList;
  $modeList.append('<div class=mode data-mode=algebra>Algebra</div>',
                   '<div class="mode selected" data-mode=general>' +
                   'General</div>',
                   '<div class=mode data-mode=other>Other</div>',
                   '<div class=mode data-mode=edit>Edit</div>',
                  );

  // Rule chooser:
  var $node = ($('<div class="ruleMenu">')
               .append($modeList)
               .append('<div class=ruleMenuTitle>Possible actions:</div>'));
  // Top node of the actual rule menu display.
  self.$node = $node;
  // Container node for menu items.
  self.$items = $('<div class=rulesItems>');

  // An intermediate DIV.  This one is set to have vertical scrolling,
  // and the rulesItems div can be inline-block to shrink-wrap itself
  // around the individual items.
  var $scrollArea = $('<div class=scrollingMenu>');
  $scrollArea.append(self.$items);
  $node.append($scrollArea);

  // Set up event handlers.

  const $ed = proofEditor.containerNode;

  $node.on('mouseenter mouseleave', function(event) {
    $ed.toggleClass('ruleMenuHovered', event.type === 'mouseenter');
  });
  
  // Entry or exit of the scrollArea clears any error display;
  // or entry into any menu item.  These are all actions that
  // might promptly lead to trying a new rule.
   $scrollArea.on('mouseenter mouseleave', function(event) {
    proofEditor.stepEditor.clearError();
  });
   $node.on('mouseenter', '.ruleItem', function(event) {
    proofEditor.stepEditor.clearError();
  });

  $modeList.on('mouseenter', '.mode', function(event) {
    if (proofEditor.stepEditor.formShowing) {
      // Do not change modes if the rule form is displayed.
      return;
    }
    const $selected = $modeList.find('[class~=selected]');
    const mode = this.dataset.mode;
    if (mode) {
      $selected.removeClass('selected');
      $(this).addClass('selected');
      if (!$selected.is(this)) {
        proofEditor.showRuleType = mode;
        proofEditor.ruleMenu.refresh();
        proofEditor.stepEditor.hideForm();
      }
    }
  });
  
  $node.on('click', '.ruleItem', function(event) {
    self.handleMouseClickItem(this, event);
  });

  // Actions for entering and leaving menu items.
  $node.on('mouseenter', '.ruleItem', function(event) {
    self.handleMouseEnterItem(this, event);
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
 * Updates the step suggestions and rule menu to offer items
 * reflecting the currently-selected step or term, if any.
 */
RuleMenu.prototype._update = function() {
  var self = this;
  const proofEditor = self.proofEditor;
  const stepEditor = proofEditor.stepEditor;
  var $items = self.$items;
  // Remove data and event handlers from suggestions.  They have
  // not been previously removed.
  $items.find('.ruleItem').each(function() {
      var suggestion = $(this).data('suggestion');
      suggestion && $(suggestion).remove();
    });
  $items.empty();
  var step = proofEditor.proofDisplay.selection;
  var term = step && step.selection;
  // Plain object describing each menu item.
  var itemInfos = [];
  self.offerableRuleNames().forEach(function(ruleName) {
      // Info is a string or array of strings.
      var info = ruleMenuInfo(ruleName, step, term, proofEditor);
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

  // TODO: Rewrite this ugly block of code.
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
            // Ignore unification failure.
            if (Toy.catchAborts(() => {
              // CAUTION: temp and temp2 are not to be added to the
              // current theory, as they are only hypothetically true
              // to test the unification.
              //
              // TODO: Consider a mechanism to check without a
              // deduction step.
              const temp = rules.assert(info.goal);
              // Unification can fail in this step.
              const temp2 = rules.instMultiVars(temp, subst);
              resultTerm = temp2.getMain().getRight();
            })) {
              // There was a failure so don't offer the fact.
              return;
            }
          }
        }
      }
      var display = ' = <span class=menuResult></span>';
      if (subst) {
        // TODO: Consider using the length of the unicode in deciding
        //   what message to generate here.
        // const unicode = statement.toUnicode();
        const html = (info.definitional
                      ? 'definition of ' + statement.getLeft().func().name
                      : 'using ' + Toy.trimParens(statement.toHtml()));
        display += (' <span class=description>' + html + '</span>');
      }
      // Rule name format of "fact <fact text>"
      // indicates that the text defines a fact to use in
      // rules.rewrite.
      var info = {ruleName: 'fact ' + text,
                  html: display,
                  result: resultTerm};
      itemInfos.push(info);
  });
  itemInfos.sort(function(a, b) {
    // We use leading spaces to influence sorting: items with
    // more leading spaces come before ones with fewer.
    return a.html.localeCompare(b.html);
  });
  var items = itemInfos.map(function(info) {
      var $item = $('<div class="ruleItem noselect">');
      $item.html(info.html);
      if (info.result) {
        $item.find('.menuResult').append(info.result.renderTerm());
      }
      $item.data('ruleName', info.ruleName);
      return $item
    });
  self.length = items.length;
  $items.append(items);
  if (term) {
    // If there is a selected term, render it and any right neighbor
    // term, and insert the renderings into all menu items that have
    // slots for them.
    var $term = $(term.renderTerm());
    $items.find('.menuSelected').append($term);
    var rightTerm = Toy.getRightNeighbor(step, term);
    var $right = '?';
    if (rightTerm) {
      var $right = $(rightTerm.renderTerm());
    }
    $items.find('.menuRightNeighbor').append($right);
  }
};

/**
 * Handler for ruleMenu selection of a rule name.  Overall purpose is
 * to run the rule from information already available, otherwise to
 * display the input form.
 */
RuleMenu.prototype.handleMouseClickItem = function(node, event) {
  if (this.suppressing) {
    return;
  }

  const ruleMenu = this;
  // Track these events in Matomo.
  _paq && _paq.push(['trackEvent', 'App', 'MainMenu']);

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
    var step = proofEditor.proofDisplay.selection;
    var term = step && step.selection;
    var formatArgs = {term: (term && term.toHtml()) || '{term}'};
    if (template) {
      // TODO: Make this block of code into a step editor method.
      // The template is not just an empty string.
      // Note that reset of the step editor will return the hidden
      // status back to normal.
      stepEditor.form.find('.customForm').html(format(template, formatArgs));
      stepEditor.showForm();
      addClassInfo(stepEditor.form);
      if (!usesSite(rule)) {
        stepEditor.addSelectionToForm(rule);
      }
      // Focus the first empty text field of the form.
      stepEditor.form.find('input[type=text],input:not([type])')
        .each(function() {
          if (!this.value) {
            this.focus();
            // Focus just the first one.
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
RuleMenu.prototype.handleMouseEnterItem = function(node, event) {
  if (this.suppressing) {
    return;
  }

  const ruleMenu = this;
  const $node = $(node);
  const proofEditor = ruleMenu.proofEditor;
  const stepEditor = proofEditor.stepEditor;
  const ruleName = $node.data('ruleName');
  // The rule may be undefined if the ruleName describes a fact.
  const rule = Toy.rules[ruleName];
  var display = proofEditor.proofDisplay;
  // Note that this item is currently hovered.
  ruleMenu.hovering = node;
  // The "suggestion" data property indicates that a suggestion has
  // been computed for this menu item.  It is a DOM node that may
  // have a proofStep in it.
  var working = display.suggestionMessage('Working . . . ');
  display.suggest(working);
  // noSuggest means "no suggestion action".  We still need a message,
  // so reuse the menu message.
  const noSuggest = rule && rule.info.noSuggest;
  if (noSuggest) {
    const suggested = display.suggestionMessage($node.clone().contents());
    $node.data('suggestion', suggested);
  }
  var suggestion = $node.data('suggestion');
  if (suggestion) {
    // A suggestion is already computed; show it.
    display.suggest(suggestion);
  } else if (!$node.data('promise')) {
    // The "promise" data property indicates that a request for a
    // step has been issued.
    var promise;
    if (ruleName.slice(0, 5) === 'fact ') {
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
    } else if (rule) {
      // It is a rule other than a rewrite with fact.
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
      // TODO: Support "real" RPCs that cross address spaces by
      //   additional encoding in the call and return.  In the call,
      //   encode step arguments to each rule as an "exact" reference
      //   to a fact, namely a string that must parse to the entirety
      //   of the fact.  In the return, encode references to these
      //   steps with an indication that the value is a reference to a
      //   step argument, and which one.  Perhaps this could be
      //   accomplished by returning the step arguments as initial
      //   steps in the proof, each using a rule such as "assert".
      //   References to these steps within the proof would decode as
      //   references to the appropriate rule argument.
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
  this._refresher.activate();
};

/**
 * Returns a list of names of rules that are "offerable" in the
 * sense of "offerable" returning true and labelApproved returning true.
 */
RuleMenu.prototype.offerableRuleNames = function() {
  var matches = [];
  for (var name in Toy.rules) {
    if (this.labelApproved(name) && this.offerableRule(name)) {
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
RuleMenu.prototype.labelApproved = function(name) {
  const editor = this.proofEditor;
  const labels = Toy.rules[name].info.labels;
  if (editor.showRules.indexOf(name) >= 0) {
    return true;
  }
  const selStep = editor.proofDisplay.selection;
  const okAlgebra = () => {
    const expr = selStep && selStep.selection;
    return (expr && !expr.isReal()
            ? false
            : labels.algebra);
  };
  const okGeneral = () =>
        labels.general || labels.basic || labels.algebra || labels.none;
  switch (editor.showRuleType) {
  case 'edit':
    return labels.edit || labels.display;
  case 'algebra':
    return okAlgebra();
  case 'general':
    // Any rule specifically labeled "general" is OK here.
    return labels.general || (okGeneral() && !okAlgebra());
  case 'other':
    return !okAlgebra() && !okGeneral() && !labels.primitive;
  default:
    throw new Error('Bad rule policy value: ' + editor.showRuleType);
  }
};

/**
 * Returns true iff the rule name can be offered by the UI, based on
 * status of step and/or term selection, declared inputs, and
 * availability of a data entry form for it.
 *
 * If there is a selection, and the rule has a precheck, and it has a
 * single "inputs" declaration that can be checked by a precheck,
 * returns false if the precheck fails.
 *  
 * Unless the precheck runs and fails, if the proof has a current
 * selection, the rule is offerable if acceptsSelection returns true
 * given the selected step and rule name, and in case the rule has a
 * toOffer property, that check also passes.  This screens rules not
 * screened by a precheck.
 *
 * Otherwise rules that take no step and no site and do have a form
 * are offerable.
 */
RuleMenu.prototype.offerableRule = function(ruleName) {
  const rule = Toy.rules[ruleName];
  const info = rule.info;
  const inputs = info.inputs;
  if (!inputs || Toy.isEmpty(inputs)) {
    return false;
  }
  const editor = this.proofEditor;
  var step = editor.proofDisplay.selection;
  if (step) {
    // Something is selected.
    var precheck = rule.precheck;
    var term = step.selection;
    // See if the rule has a precheck that can "rule it out".
    // Precheck only works on rules with a single input of a site or step type.
    if (precheck && Toy.mapSize(info.inputs) == 1 &&
        (term
         // This list needs to match siteTypes.
         ? (inputs.site || inputs.bindingSite || inputs.reducible ||
            inputs.term)
         // This list needs to match stepTypes.
         : inputs.step || inputs.equation || inputs.implication)) {
      // TODO: Consider if all of this is buggy??
      //   Will the rule really always take these arguments?
      var ok = (inputs.term
                ? precheck(term)
                : term
                // Uses prettyPathTo so behavior matches rule execution.
                ? precheck(step, step.wff.prettyPathTo(term))
                : precheck(step));
      if (!ok) {
        return false;
      }
    }
    // Check if the rule accepts the selection.
    if (acceptsSelection(step, ruleName)) {
      // If the rule has a "toOffer" property, apply it as a further
      // test of offerability.
      //
      // TODO: Consider moving this to the "policy" section
      //   (labelApproved).
      var offerTest = info.toOffer;
      if (info.toOffer) {
        return offerTest(step, step.selection);
      }
      return true;
    } else {
      return false;
    }
  } else if (!info.form) {
    // There is no form, so arguments cannot come from the form.
    return false;
  } else {
    // There is no selection, so the rule must not require a step or
    // site.
    for (const type in info.inputs) {
      // It is OK to use "in", since the type will not be the name of
      // a method on Objects.
      if (type in stepTypes || type in siteTypes) {
        return false;
      }
    }
    // All the above checks pass, so we can offer the rule.
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
  const self = this;
  const facts = [];
  const step = self.proofEditor.proofDisplay.selection;
  const expr = step && step.selection;
  if (expr) {
    const mode = self.proofEditor.showRuleType;
    // Here are the policy functions to decide what facts
    // are to be offered.

    // Truthy if OK to show in algebra mode.
    const okAlgebra = info => info.labels.algebra;

    // Truthy if OK to offer in "general" mode, ignoring
    // the exclusion of facts shown in algebra mode.
    const okGeneral = info => {
      const goal = info.goal;
      if (info.labels.general || info.labels.algebra) {
        return true;
      }
      if (info.desimplifier) {
        return false;
      }
      if (info.labels.higherOrder) {
        return true;
      }
      return false;
    };

    // Truthy if OK to show as "more" ignoring potential exclusion
    // due to being in other categories.
    const okOther = info => (!info.labels.primitive &&
                             !info.goal.matchPart().isVariable());

    Toy.eachFact(function(info) {
      const goal = info.goal;
      const matchTerm = goal.matchPart();
      if (!Toy.coreUnifTypes(expr.type, matchTerm.type)) {
        return;
      }
      const subn = expr.matchSchema(matchTerm);
      if (!subn) {
        return;
      }
      if (goal.implies()) {
        const asms = goal.getLeft();
        // TODO: Systematize handling of facts that may add
        //   assumptions.
        //
        // In general mode, if a rule adds assumptions they
        // must be of just a few sorts, currently matching
        // these schemas.  This is just a quick fix.
        if (asms.scanConj
            (x =>
             // These checks look OK.
             !x.matchSchema('R x') &&
             !x.matchSchema('not (x = y)') &&
             !x.matchSchema('x != y'))) {
          return;
        }
      }
      const ok =
            (mode === 'edit'
             ? info.labels.display || info.labels.edit
             : mode === 'algebra'
             ? okAlgebra(info)
             : mode === 'general'
             ? !okAlgebra(info) && okGeneral(info)
             : mode === 'other'
             ? !okAlgebra(info) && !okGeneral(info) && okOther(info)
             : assert(false, 'Unknown mode: {1}', mode)
            );
      if (ok) {
        facts.push(info);
      }
    });
  }
  return facts;
};

/**
 * This matches a step against the inputs descriptor of an inference
 * rule.  The step is the selected proof step, ruleName is the name of
 * the rule to match against.  Only call this if a step or part of a
 * step is selected.
 *
 * If something is selected, this accepts rules whose inputs descriptor
 * is compatible with the selection.  See the code for details.
 *
 * The rule can also require additional inputs.
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
      return !!expr.findSubst(info.using.getMain().getLeft());
    } else {
      // Otherwise OK if it takes a site, or is a proper binding site
      // or a beta-reducible expression.
      // 
      // TODO: prevent selection of bound variables as terms.
      return (argInfo.site
              || (argInfo.term &&
                  // These checks mean that the selection cannot be
                  // used as a mere term if the rule needs some kind
                  // of step as an input.  The user must select the
                  // step and then enter a term, or copy it from the
                  // clipboard.
                  //
                  // This list must match stepTypes.
                  !argInfo.step && !argInfo.equation && !argInfo.implication)
              || (argInfo.bindingSite && expr instanceof Toy.Lambda)
              || (argInfo.reducible
                  && expr instanceof Toy.Call
                  && expr.fn instanceof Toy.Lambda));
    }
  } else {
    // If the rule needs a site, do not accept just a step.
    return (!argInfo.site &&
            (argInfo.step
             || (argInfo.equation && step.getMain().isCall2('='))
             || (argInfo.implication && step.getMain().isCall2('=>'))));
  }
}

/**
 * Produces a rule menu entry from a ruleName.  Called with a
 * (rendered) step if there is a selection, the selected term if a
 * term is selected, and the menu's ProofEditor.
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
  var info = Toy.rules[ruleName].info;
  if (info.menuGen) {
    var gen = info.menuGen;
    return gen(ruleName, step, term, proofEditor);
  }
  if (Toy.isEmpty(info.inputs)) {
    // It is an axiom or theorem with no inputs.
    // TODO: Consider supporting axioms and theorems only as facts.
    //   This function only seems to be called when there is a form
    //   property anyway.
    if (info.menu) {
      return info.menu;
    }
    var thm = Toy.getTheorem(ruleName);
    var thmText = Toy.trimParens(thm.getMain().toHtml());
    if (info.axiom) {
      return 'axiom ' + thmText;
    } else {
      return 'theorem ' + thmText;
    }
  } else {
    // The rule takes inputs.
    if (info.menu) {
      // Use info.menu as the HTML, substituting suitable empty spans
      // for occurrences of {term} and {right} there.  This defers the
      // rendering and insertion of the rendering of the term and
      // right neighbor to the RuleMenu code where it is more
      // convenient and the HTML has been converted to DOM structure.
      var formatArgs = {term: '<span class=menuSelected></span>',
                        right: '<span class=menuRightNeighbor></span>'};
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
