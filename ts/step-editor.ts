// Copyright Crispin Perdue.  All rights reserved.

// Set everything up immediately on load, avoiding changes to
// the global environment except through namespace "Toy".
namespace Toy {

'use strict';

// Make application assertions available through "assert".
const assert = Toy.assertTrue;
  
const Expr = Toy.Expr;
const Step = Toy.Step;  

const abort = Toy.abort;
const format = Toy.format;
const dom = Toy.dom;
const TermSet = Toy.TermSet;
const rules = Toy.rules;
const infixCall = Toy.infixCall;

/** For execution profiling */
export var profileName;

/** 
 * If an exercise is set up, value is the exercise name, e.g. "nat",
 * otherwise null.
 */
export var exerciseLoaded = null;

/**
 * Async utility function to print and return the
 * proofState of the named exercise.  Currently unused.
 */
async function exerciseSteps(exName) {
  let result;
  await Toy.db.exercises.get(exName)
    .then(data => {
      if (data) {
        console.log(data.proofState);
        result = data.proofState;
      } else {
        console.log('not found');
      }
    });
  return result;
}

//// PROOF EDITOR

export var proofEditors = new Set();

// TODO: Use events and event handlers to make cleaner separation
//   between ProofEditor, ProofDisplay, and StepEditor.  StepEditor
//   needs some kind of access to the array of proof steps to
//   translate step numbers to steps.  Perhaps ProofDisplay can notify
//   when its list of steps changes.

// Each instance has a unique, sequential numeric ID starting at 1.
export var nextProofEditorId = 1;

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
 * Optional argument "options", plain object with named properties:
 * 
 * docName: if given, overrides the default workspace name.  This is
 *   null and ignored if this is an exercise.
 * oneDoc: if present, the editor cannot switch to work on any
 *   document other than the initial one.  Currently implemented
 *   by hiding the worksheets button.  Also hides the worksheet
 *   name display, and if no docName is given, prefixes the default
 *   name to hide it from lists.
 * exercise: name of an exercise set and part to set up, in the format
 *   exercise/part.  Suppresses automatic loading of real numbers.
 *   Also has the effect of oneDoc.  This is for tutorials and problem
 *   sets (really lists).  If given, this must be the only proof
 *   editor within this page.
 * noload: if present, do not load theories for this proof editor.
 * steps: encoding of initial steps; only applies if no document
 *   matching the computed workspace name already exists.
 *
 * Public properties:
 *
 * proofDisplay: ProofDisplay for the proof being edited.
 * steps: rendered steps from the proofDisplay.
 * $node: jQuery object for outermost DOM node for the display.
 * $proofButtons: jQuery object for the row of "proof buttons".
 * stepEditor: StepEditor for the proof being edited.
 * proofEditorId: identifies this editor for purposes of restoring its
 *   operating state from localstorage across visits / page loads.
 *   Consists of the pathname part of the browser "location", "#", and
 *   an integer sequence number of the editor within the page.  In
 *   principle an editor could also be assigned an ID explicitly during
 *   editor initialization immediately after creation.
 * exercise: the exercise property from the options.
 * fromDoc: boolean, true if the constructor gets state from an existing 
 *   document.
 * initialSteps: array of ordinary steps to display when cleared, or
 *   initially if no state is saved in the database.  From the "steps"
 *   option if given, or from an exercise problem statement; defaults
 *   to an empty array.
 * givens: read-only TermSet of boolean terms defining the problem, often
 *   equations (not steps).  Non-empty iff the first step is a "given"
 *   step; then contains the conjuncts of the main part, as determined
 *   by scanConjuncts.
 * givenVars: object/set keyed by names of variables free in the givens;
 *   read-only.
 * goalStatement: for proof exercises, a proof statement wff.
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
export class ProofEditor {
  _options;
  _givens;
  givenVars;
  solutions: any[];
  standardSolution: boolean;
  goalStatement: EType;
  showRuleType: string;
  showRules: string[];
  initialSteps: EType[];
  proofEditorId: string;
  proofDisplay: ProofDisplay;
  steps: EType[];
  $node;
  $status;
  $statusDisplay;
  $copyText;
  $proofButtons;
  _wksControls;
  stepEditor;
  ruleMenu;
  _refresher;
  _otherChanges;
  animating: boolean = false;
  fromDoc: boolean;
  exercise;
  docName;

  constructor(options_arg:Record<string, any>={}) {

  //// Initialize properties.

  const self = this;
  const options = self._options = options_arg;
  self.exercise = options.exercise;
  
  // This is set up by a later part of the constructor.
  // It stays null for exercises.
  self.docName = null;
  assert(proofEditors.size === 0 || !options.exercise,
         `Exercises permit only one ProofEditor (${options.exercise}).`);
  proofEditors.add(self);

  // If the first step of the proof is a "givens" step, this will
  // become a TermSet with all conjuncts of its main part.
  self._givens = new TermSet();
  self.givenVars = {};
  self.solutions = [];
  self.standardSolution = true;
  self.goalStatement = null;
  self.showRuleType = 'general';
  self.showRules = [];
  // Exercises often override the default empty value.
  self.initialSteps = options.steps
    // TODO: Is there a better way to express this idea?
    ? Toy.unrenderedDeps(Toy.asProof(options.steps)())
    : [];

  //// Build the DOM structures and connect the parts.

  const nid = nextProofEditorId++;
  self.proofEditorId =
    window.location.pathname + (nid === 1 ? '' : '#' + nid);
  const mainDisplay = new Toy.ProofDisplay();
  mainDisplay.proofEditor = self;
  self.proofDisplay = mainDisplay;
  self.steps = mainDisplay.steps;

  // Top-level element of the proof editor display:
  const $node = this.$node =
    $('<div class="proofEditor logicZone"></div>');

  // Maybe lock the editor to the document.
  if ('oneDoc' in options || options.exercise) {
    $node.addClass('oneDoc');
  }

  const stepEditor = new StepEditor(this);
  self.stepEditor = stepEditor;
  // This node provides a coordinate system for absolute positioning.
  const $formParent = $('<div style="position: relative">');
  $formParent.append(stepEditor.$form);

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

  let $header =
    ($('<div class=proofEditorHeader>')
     .append('&nbsp;<b class=wksTitle>Worksheet \
             "<span class=wksName></span>"</b>'));
  const $clearWork = $('<input type=button class=clearWork value="Clear work">');
  const css = {border: '1px solid red',
               color: '#d9534f',
               fontWeight: 'bold',
               backgroundColor: 'white'
  };
  $clearWork.css(css);
  // Add "Solve" button next to "Clear work", but with class "hidden".
  // Use its "solveProblem" class to find it.
  const $solve =
        $('<input type=button class="solveProblem hidden" value="Solve">')
        .css({fontWeight: 'bold'});
  const $headerRight = $('<span>').css({float: 'right'});
  $headerRight.append($solve, $clearWork);
  $header.append($headerRight);

  let $readOnly =
    $(`<p class=ifProofLoadError><i><b style="color:red">
      An error occurred executing the proof.</b><br>
      View the workspace as text to see steps not executed.<br>
      For safety this worksheet is read-only.</i></p>`);
  this.$node
    .append($header)
    .append($readOnly)
    .append(mainDisplay.node)
    .append($status)
    .append($formParent)
    .append(proofButtons.$node)
    // @ts-expect-error 2352
    .append(this._wksControls.node)
    .append(stepEditor.$proofErrors)
    .append(self.$uxDialog())
    .append(menu.$node);
  this.setEditable(true);

  // Prepare to write out proof state during refresh, so basically
  // whenever it changes.
  this._refresher = new Toy.Refresher(changes => this.refresh());
  this._otherChanges = new Toy.Refresher(changes => this.otherChanges());

  let proofData = null;
  
  // Create an editor record if none exists.
  const id = self.proofEditorId;
  Toy.db.editors.add({id: id}).catch(err => null);
  // Recover known content area height from the database
  Toy.db.editors.get(id).then(item => {
    const height = item && item.height;
    height && self.$node.find('.proofSteps').height(height);
  });
  if (!options.exercise) {
    const state = Toy.getOtherPedState(self);
    // Restore editor state (not document state).
    // This sets self.docName and potentially goalStatement.
    self.syncToDocName(options.docName ||
                       (state
                        ? state.docName
                        // The (default) document name is the proofEditorId.
                        // By default set the document name according
                        // to the URI path, and the editor number if
                        // that is greater than one.
                        : this.proofEditorId));
    // If there is a canned solution, show the "Solve" button.
    proofData = Toy.findProofData(self.docName);
    if (proofData) {
      $solve.removeClass('hidden');
    }
    // Initialize editor content.
    if (self.openDoc(self.docName)) {
      // There is an existing saved document.
      self.fromDoc = true;
    } else if (self.initialSteps) {
      self.setSteps(self.initialSteps);
    }
  }

  // Initialize the uxBox state.
  self.$node.find('.uxBox')
    .prop('checked', localStorage.getItem('Toy:uxOK') === 'true');

  // Loads a desired document.  If this is the first editor on the
  // page, load any theory documents first.
  //
  // TODO: Replace this with a mechanism that tracks theories
  //   loaded into the current "proof context".  Ideally a page
  //   could have any number of proof contexts, often associating
  //   each proof editor with a context.
  if (self.docName) {
    // TODO: this functionality is currently disabled with "if false".
    // Someday replace it with something better.
    const dependencies = () => {
      if (false && nextProofEditorId <= 2) {
        // In other words, this is the first proof editor on this
        // page.  Note: In the current implementation, any other proof
        // editors or displays on the page will have this same proof
        // context whether it is appropriate or not.
        const theories = (Toy.lsDocs()
                          .filter(nm => nm.startsWith('Theory '))
                          .sort());
        const index = theories.indexOf(self.docName);
        if (index >= 0) {
          // This removes everything starting at the index.
          theories.splice(index);
        }
        return theories;
      } else {
        return [];
      }
    };
    let names = dependencies();
    for (const nm of names) {
      self.openDoc(nm);
    }
  }
  // Updates proof editor state for the desired exercise based on
  // exercise proof state in the database, or from the relevant
  // declaration if no state has been saved.
  if (options.exercise) {
    self._initExercise(options.exercise);
  }

  //// Event handlers

  // When the user explicitly checks or unchecks the box,
  // set the localStorage item and start or stop session recording.
  self.$node.find('.uxBox').on('change', function() {
    Toy.setSessionRecording(this.checked);
    $(document).find('.proofEditor .uxBox').each((ix, elt) => {
      elt.checked = this.checked;
    });
    Toy.trackAppEvent('UXTrace', this.checked ? 'on' : 'off');
  });

  // Respond to presses on the UX dialog buttons.
  self.$node.find('.uxYes, .uxNo').on('click', function() {
    const state = $(this).is('.uxYes');
    Toy.setSessionRecording(state);
    Toy.trackAppEvent('UXTrace', state ? 'on' : 'off');
    $(document).find('.proofEditor .uxBox').each((ix, elt) => {
      // This could result in a cascade of reporting the
      // same event.
      elt.checked = state;
    });
    self.$node.removeClass('hasDialog');
    self.$node.find('.uxDialog').addClass('invisible');
  });

  self.$node.find('.clearWork').on('click', function() {
    if (window.confirm('Do you really want to clear your work?')) {
      self.clear();
      self.setEditable(true);
    }
  });

  $solve.on('click', function() {
    if (window.confirm('Replace contents with a pre-made solution?')) {
      self.setSteps(Toy.unrenderedDeps(Toy.asProof(proofData.proof)()));
    }
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
    // Also hides the error report.  When the proof editor has a dialog
    // box, most clicks within the editor do not hide the dialog.
    if (!within($target,
                '.proofEditor.hasDialog, .proofErrors, ' +
                '.stepEditor, .ruleForm')) {
      // TODO: Consider perhaps an editor reset() method.
      self.stepEditor.clearError();
    }
  });
}

/**
 * Really this responds when the proof has been updated since
 * the last time the event loop returned to idle.
 * Response to other changes is in method otherChanges.
 */
refresh() {
  const self = this;
  const mainDisplay = self.proofDisplay;
  const $status = self.$status;
  const $statusDisplay = self.$statusDisplay;
  self._updateGivens();

  // Persistently store proof state.
  // This could probably be unconditional.
  if (self.isEditable()) {
    self.saveProofState();
  }

  // Set (or clear) the possible "Proof complete"  message in the $status box.
  var steps = mainDisplay.steps;
  var len = steps.length;
  if (len > 0) {
    var step = steps[len - 1];

    // Is the goal proved?
    const stmt = self.goalStatement;
    if (stmt && !self.animating) {
      async function showProved() {
        // TODO: Use CSS transitions for the animation.  The current
        //   design probably doesn't work if auto-simplification
        //   changes a solution into a non-solution.
        self.animating = true;
        await Toy.sleep(200);
        for (const ch of '\u2713 Proof complete. '.split('')) {
          $node.append(ch);
          await Toy.sleep(20);
        }
        self.animating = false;
      }
      const solved = step.checkSubgoals(stmt) === 0;
      const $node = $('.proofEditorHeader .status');
      $node.empty();
      if (solved) {
        showProved();
      } else {
        $node.append('Proving:');
      }
    }

    var message = self.progressMessage(step.original);
    $statusDisplay.empty();
    $statusDisplay.append(message || '&nbsp;');
    $status.toggleClass('empty', !message);
  } else {
    $status.toggleClass('empty', true);
  }
}

/**
 * Updates the database for changes to state other than the proof,
 * currently the editor's display height.
 */
otherChanges() {
  const self = this;
  Toy.db.editors.update(self.proofEditorId,
                        {height: $(self.proofDisplay.stepsNode).height()}
                       );
}

/**
 * Initializes proof editor state for the given exercise item, named
 * as "exercise/item", initializing theory state by calling
 * prepExercise.  If there is an entry in the database for the
 * exercise item, sets those up, else if the proof editor has declared
 * initialSteps, sets those up.
 */
_initExercise(exName) {
  /**
   * Returns an array of ordinary proof steps that initialize an
   * exercise based on setting the given wff as a goal.
   */
  function exerciseInits(stmt) {
    const step = rules.goal(stmt);
    return [step];
  }
  const self = this;
  const db = Toy.db;
  const info = prepExercise(exName);
  const stmt = info && info.statement;
  const statement = stmt && Toy.mathParse(stmt);
  // Set initial steps if appropriate.
  if (!self._options.steps && statement) {
    self.initialSteps = exerciseInits(statement);
  }
  // Display steps saved in the database or else initial steps.
  db.exercises.get(exName)
    .then(data => {
      console.log('Exercise in db:', data);
      const decoded = data && Toy.decodeSteps(data.proofState);
      if (decoded instanceof Error) {
        self.stepEditor.report(decoded);
        self.setSteps(self.initialSteps);
      } else {
        self.setSteps(decoded || self.initialSteps);
      }
    });
  if (statement) {
    self.goalStatement = statement;
    // Display the exercise goal in the editor's header.
    const $header = self.$node.find('.proofEditorHeader');
    $header.find('.wksTitle')
      .replaceWith('<b class=status>Proving:</b> <span class=wff></span>');
    $header.find('.wff').append(statement.renderTerm());
  }
}

/**
 * Build and return a UX trace control initializing dialog
 * as a jQuery object.
 */
$uxDialog() {
  const raw = `
    <div class="dialogWrapper uxDialog invisible">
    <div class="dialog">
    <span style="flex: auto; margin: 0 1em">
    Will you kindly help advance Prooftoys usability
    by enabling detailed tracing of your usage?
    <i>You can opt out at any time.</i>
    For more information, see the
    <a href="/privacy/">privacy information</a> page.
    </span>
    <input type=button class=uxYes value=Yes>
    <input type=button class=uxNo value=No>
    </div>
    </div>`;
  const cooked = raw.replace(/^    /mg, '');
  return $(cooked);
}

/**
 * Sets the name of this editor's worksheet, (this.docName) and
 * does associated bookkeeping for the UI.  This does not load or save
 * any proof state.  (In most use cases one or the other should also
 * be done.)
 */
syncToDocName(name) {
  const self = this;
  self.docName = name;
  // Set the document name into all nodes of class wksName.
  self.$node.find('.wksName').text(name);
  // Remember the state of this editor.
  // TODO: Replace the following with some form of state observation.
  if (self.isEditable()) {
    // Only note the state within this context if editing the proof,
    // so that otherwise the document can be edited by other editors.
    // (See Toy.isDocHeldFrom.)
    Toy.noteState(self, {docName: self.docName});
    const wff = (name.startsWith('(') &&
                 Toy.catching(() => Toy.parse(name)));
    self.goalStatement = wff instanceof Expr ? wff : null;
  }
  // Visiting the same page in another tab then will cause its proof
  // editor to visit the same document as this one.
  Toy.saveState(self, {docName: self.docName});
}

/**
 * Attempts to open the named document in this proof editor, setting
 * the editor's document name and loading its proof state.  Returns
 * true iff the document is successfully loaded, false for failure,
 * and null when the current theory needs to be unloaded first.
 * Initiates unloading by reloading the page.
 *
 * If no conflicting theory is loaded, ensures that the real numbers
 * are set up except if the proof goal indicates NN but not R.  In
 * that case ensures that NN is set up.
 */
openDoc(name) {
  const goal = Toy.catching(() => Toy.parse(name));
  if (!('noload' in this._options)) {
    let needNN = false;
    if (goal instanceof Expr) {
      const names = goal.constantNames();
      needNN = names.has('NN') && !names.has('R');
      if (names.has('NN') && names.has('R')) {
        console.warn('NN and R!?');
      }
    }
    if ((needNN && Toy.realNumbersLoaded) ||
        (!needNN && Toy.exerciseLoaded)) {
      // Associate this proof editor with this document across
      // page loads.
      this.syncToDocName(name);
      // Reload and start over.
      Toy.sleep(0).then(() => location.reload());
      // Indicate an inconclusive result.
      return null;
    }
    if (needNN) {
      // This loads all natural numbers theorems.
      prepExercise('nat/');
    } else if (!Toy.realNumbersLoaded) {
      Toy.requireRealNumbers();
    }
  }
  const proofData = Toy.readDoc(name);
  // TODO: Check for possible active editing in another tab/window.
  if (proofData) {
    this.setEditable(true);
    const steps = Toy.decodeSteps(proofData.proofState);
    if (steps instanceof Error) {
      // Write the problematic proof to a new document with ".err" in
      // the name.
      const errName = Toy.genDocName(`${name}.err`);
      Toy.writeDoc(errName, {proofState: this.getStateString()});
      // Show the truncated list of steps in the proof editor.
      this.setSteps(steps.steps);  // Bug?
      this.stepEditor.report(steps);
      return false;
    } else {
      this.syncToDocName(name);
      this.setSteps(steps);
      return true;
    }
  } else {
    return false;
  }
}

/**
 * Returns the name of the editor's current document.
 */
getDocumentName() {
  return this.docName;
}

/**
 * Empties the proof and problem statement for a fresh start.
 */
clear() {
  this.showRules = [];
  this.stepEditor.hideForm();
  this.setSteps(this.initialSteps);
}

/**
 * Recompute the problem givens from the first proof step if its rule
 * name is "given".  Sets them to be all conjuncts of the RHS of the
 * main part of the first step, set up as an equivalence by
 * rules.given.
 */
_updateGivens() {
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
}

/**
 * Update the givenVars to match the (possibly changed) set of givens
 * of this problem.
 */
_updateGivenVars() {
  // An object/set with names of all variables in any of the
  // givens:
  var vars = {};
  this._givens.each(function(g) { $.extend(vars, g.freeVars()); });
  this.givenVars = vars;
}

/**
 * Add a step to the proof.
 */
addStep(step) {
  const rendered = this.proofDisplay.addStep(step);
  const stmt = this.goalStatement;
  if (stmt) {
    rendered.checkSubgoals(stmt);
  }
}

getLastStep() {
  return this.proofDisplay.getLastStep();
}

/**
 * Gets the state of the proof, in string form.
 */
getStateString() {
  return Toy.encodeSteps(this.proofDisplay.steps);
}

/**
 * Returns an array of string forms of the steps
 * of this proof editor, usable as JSON.
 */
getStepWffs() {
  return this.steps.map(s => s.wff.toString());
}

getJSONState() {
  const v = {
    proofState: this.getStateString(),
    stepWffs: this.getStepWffs(),
  };
  return v;
}

/**
 * Sets the state of the proof from a string as returned by
 * getStateString.
 */
setStateFromString(encoded) {
  // TODO: Rename to setProofFromString.
  var steps = encoded ? Toy.decodeSteps(encoded) : [];
  this.setSteps(steps);
}

/**
 * Sets the steps to the given array of non-renderable steps.
 */
setSteps(steps) {
  const setTheSteps = steps => {
    // Note that the editor does not have its own
    // removeStepAndFollowing method.
    this.proofDisplay.setSteps([]);
    for (var i = 0; i < steps.length; i++) {
      this.addStep(steps[i]);
    }
  };
  if (steps instanceof Error) {
    setTheSteps(steps.steps);
    this.setEditable(false);
    this.toggleClass('proofLoadError', true);
  } else {
    setTheSteps(steps);
    this.toggleClass('proofLoadError', false);
  }
}

/**
 * Save the proof state to the the worksheet controls text area and
 * the document's data store.  Normally use the proofChanged method
 * rather than calling this directly, to avoid redundant work.
 */
saveProofState() {
  const self = this;
  const options = self._options;
  var text = self.getStateString();
  self._wksControls.setProofText(text);
  if (self.docName) {
    Toy.writeDoc(self.docName, {proofState: text});
  } else if (options.exercise) {
    Toy.db.exercises.put({exName: options.exercise, proofState: text})
      .catch(reason => console.warn('Not put:', reason));
  } else {
    console.warn('State not saved');
  }
}

/**
 * Attempts to restore the proof state from the worksheet controls
 * text area.
 */
restoreState() {
  var string = this._wksControls.getProofText();
  this.setStateFromString(string);
}

/**
 * Returns true iff this is editable.
 */
isEditable() {
  return this.proofDisplay.isEditable();
}

/**
 * Turns editability of the proof editor on or off, currently
 * affecting only the UI.
 */
setEditable(value) {
  this.toggleClass('editable', value);
  // The following set the state of the display and hide or show the
  // step editor.
  this.proofDisplay.setEditable(value);
}

/**
 * Toggles a CSS class on the main node of this proof editor.
 */
toggleClass(className, truthy) {
  this.$node.toggleClass(className, truthy);
}
}

/**
 * Define the "givens" property as a virtual property.  Setting it has
 * the side effect of modify the "givenVars" property as well, which
 * should be treated as readonly.  If not set explicitly through the
 * setter, givens will come from uses of the "given" rule.
 */
Object.defineProperty(ProofEditor.prototype, "givens", {
    get: function() { return this._givens; },
    // TODO: Check if the setter is ever used; clean up the semantics.
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
 * Based on the given "exercise/item" exercise name, adds the fact
 * declarations to set up the theory state for that item of that
 * exercise.  (In the declarations, item names are called
 * "exertion"s.)  Applies all of the declarations for that exercise
 * preceding the desired item's record, and returns that declaration,
 * omitting its exertion property.
 *
 * If the exercise exists, but no such item, applies all declarations
 * and returns null.  An empty part name is allowed.
 */
function prepExercise(name) {
  const matches = name.match(/(.*?)\/(.*)/);
  assert(matches, `Not an exercise item name: ${name}`);
  const [_, exName, partName] = matches;
  const decls = Toy.exercises.get(exName);
  assert(decls, `No such exercise set: ${exName}`);
  let found = false;
  const keepers = [];
  for (const decl of decls) {
    const thisName = decl.exertion;
    // This line copies the own properties.
    const info = { ...decl };
    delete info.exertion;
    if (!Toy.isEmpty(info)) {
      keepers.push(info);
    }
    if (thisName === partName) {
      found = true;
      break;
    }
  }
  const result = found ? keepers.pop() : null;
  keepers.forEach(Toy.addRule);
  Toy.exerciseLoaded = exName;
  return result;
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

  // Toggling the proof state display visibility with a button.
  const $wksButton =
    $('<input type=button class=wksButton value="Worksheets... ">');

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
  // Read and write this control as ".uxBox".
  const $ux = $('<label style="color: blue">Enable usage tracing ' +
                '<input type=checkbox class=uxBox></label>');
  $ux.css({
    float: 'right'
  });
  $proofButtons.append($ux);
  // Set up a fancy tooltip.
  const tp = tippy(dom($ux), {
    allowHTML: true,
    delay: 400,
    maxWidth: '500px',
    content:
    ('<i>User experience</i> is vital to the mission of Prooftoys.</i><br><br>' +
     'Checking this box enables detailed tracing of your interactions<br>' +
     'to help make the Prooftoys user experience better.<br>' +
     'We are grateful for your participation.<br><br>' +
     'For more information see the <i>privacy information</i> page.')
  });
  $(tp.popper)
    .find('.tippy-box')
    .css({color: 'darkblue',
          backgroundColor: 'white',
          border: '2px solid black',
          borderRadius: '5px'})

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

  function makeEntryField(prefix, classes) {
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
        editor.syncToDocName(name);
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
    const name = $(this).text();
    const status = editor.openDoc(name);
    if (status === false) {
      Toy.alert('Could not open worksheet ' + name);
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
export var stepTypes = {
  step: true,
  equation: true,
  implication: true
};

// Datatypes that refer to sites within a step.  None of these are
// in formTypes.
export var siteTypes = {
  site: true,
  bindingSite: true,
  reducible: true
};


// TODO: If needed, support rules that need multiple selectable inputs
//   by using a selection and following steps as inputs.  If multiple
//   selections are needed, the step editor can use "consider" to pick
//   a term from a step, and if necessary, look back to the origin
//   site of the term to use it as a selection.  Probably only fill in
//   rule arguments from steps at the end of the current proof, and
//   remove steps added by copying or use of "consider"
//
//   Another way to collect multiple steps as inputs would be to
//   (temporarily) create a conjunction of steps and use the
//   conjunction as a single input.

/**
 * A ProofEditor has exactly one StepEditor, which can be shown or hidden.
 * It renders as a "somewhat modal" form display.
 *
 * Fields:
 * $form: jQuery DIV containing the entire input form
 * $proofErrors: jQuery DIV with the error display
 *
 * TODO: Rename this to e.g., RuleForm.
 *   Move $proofErrors into the ProofEditor.
 */
export class StepEditor {
  _proofEditor: ProofEditor;
  proofDisplay: ProofDisplay;
  clearer;
  $form;
  formShowing;
  $proofErrors;
  ruleName;
  lastRuleTime;
  lastRuleSteps;

  constructor(proofEditor) {
  // Make this available to all inner functions.
  var self = this;

  // TODO: Reconsider the distinction and the relationship between the
  // StepEditor and ProofEditor.
  self._proofEditor = proofEditor;
  self.proofDisplay = proofEditor.proofDisplay;

  // Button to clear rule input, visible when a form is active.
  self.clearer =
    $('<button class="fa fa-120 fa-times-circle sted-clear" '+
      'title="Clear the input">');
  const $form = self.$form = $('<div class="ruleForm hidden"></div>');

  $form.append(self.clearer, '<span class=customForm></span>');
  // Install event handlers.
  self.clearer.on('click', function() {
    self.hideForm();
    self._proofEditor.ruleMenu.suppressing = false;
  });

  $form.append(' <button class=go>Go</button>');
  self.$form.on('click', 'button.go', function() {
    self.tryRuleFromForm();
  });

  // Keyboard events bubble to here from the inputs in the form.
  self.$form.on('keydown', function(event) {
    if (event.keyCode == 13) {
      // <enter> key was hit
      self.tryRuleFromForm();
    }
  });

  self.$proofErrors = $('<div class="proofErrors hidden"></div>');
  // Always clear the errors when clicked.
  self.$proofErrors.on('click', '.clearer', function() {
    self.clearError();
  });
}

/**
 * Reports the HTML message as an error in the step editor.
 */
error(message) {
  this.report('<b>' + message + '</b>');
}

/**
 * Report the error through the DOM and help the user debug in case it
 * has a "step" property.  The argument should be an Error object or
 * an HTML string.
 */
report(error) {
  var $proofErrors = this.$proofErrors;
  $proofErrors.html('<button class=clearer>X</button>');
  $proofErrors.show();
  this._proofEditor.$node.addClass('hasDialog');
  if (error instanceof Error) {
    $proofErrors.append('<b>Error: ' + error.message + '</b>');
    if (error.step) {
      Toy.renderProof(error.step, $proofErrors);
    }
  } else {
    // It should be a string.
    $proofErrors.append(error);
  }
}

/**
 * Hides the error display.
 */
clearError() {
  this._proofEditor.$node.removeClass('hasDialog');
  this.$proofErrors.hide();
}

/**
 * Shows the form for entering info for the selected rule.
 */
showForm() {
  this.$form.show();
  this.formShowing = true;
  this.proofDisplay.setSelectLock(true);
  this._proofEditor.$node.addClass('ruleFormVisible');
  // Suppresses response to mouse events in the menu;
  // important especially to suppress clicks, also done
  // by tryRuleSoon, so it can safely defer running
  // its rule until after the next repaint.
  this._proofEditor.ruleMenu.suppressing = true;
}

/**
 * Hides the rule entry form.
 */
hideForm() {
  this.$form.hide();
  this.formShowing = false;
  this.proofDisplay.setSelectLock(false);
  this._proofEditor.$node.removeClass('ruleFormVisible');
}

/**
 * Check that the given args Array is filled in with values that are
 * not instances of Error, and that up to minArgs, the values are not
 * the undefined value.  If reportError is true, report the problem in
 * the StepEditor, and in any case return true iff all is OK, else
 * false.  If the values are OK and some optional args are undefined,
 * truncate the args array to omit the unneeded undefined values.
 */
checkArgs(args, minArgs, reportError) {
  // Check that the args are all filled in.
  var required = (typeof minArgs == 'number'
                  ? minArgs
                  : args.length);
  for (let i = 0; i < args.length; i++) {
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
  for (let i = required; i < args.length; i++) {
    if (args[i] === undefined) {
      args.length = i;
      break;
    }
  }
  return true;
}

/**
 * Try to fill in a field of the form with the selection.  For
 * steps this will be a reference to the step, and for terms it
 * will be a textual rendering of the selected expression.
 *
 * Only call this if the rule does not use a site (usesSite).
 */
addSelectionToForm(rule) {
  var proofDisplay = this.proofDisplay;
  var step = proofDisplay.selection;
  if (step) {
    var expr = step.selection;
    var form = this.$form;
    var n = step.stepNumber;
    // Search for the first input field that is compatible with the
    // selection and fill it in with selection information.
    // @ts-ignore 2345
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
            || (fieldType == 'equation' && step.isEquation())
            || (fieldType == 'implication' && step.implies())) {
          this.value = n;
          // Stop iteration.
          return false;
        }
      }
    });
  }
}

/**
 * Fill in arguments for the rule named by the ruleMenu from the
 * current selection and the rule's input form, and if successful set
 * up actual execution and redisplay to occur after the UI has
 * opportunity to repaint.  If reportFailure is true, shows the
 * user any error message from calling fillFromForm.  Otherwise
 * just leaves the form up for the user to complete.
 */
tryRuleFromForm() {
  // TODO: Get it together on failure reporting here.
  const ruleName = this.ruleName;
  const rule = Toy.rules[ruleName];
  const minArgs = rule.info.minArgs;
  const args = this.argsFromSelection(ruleName);
  if (this.fillFromForm(ruleName, args) &&
      this.checkArgs(args, minArgs, true)) {
    this.hideForm();
    tryRuleSoon(this, ruleName, args);
  }
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
_tryRule(ruleName, args) {
  var self = this;
  var startTime = Date.now();
  var startSteps = Toy.getStepCounter();
  const editor = this._proofEditor;
  const rule = Toy.rules[ruleName];  

  // Set to true in case of possible (deferred) autoSimplify.
  let deferCleanup = false;
  // Cleans up lockouts on interactivity.
  const cleanup = () => {
    editor.proofDisplay.setSelectLock(false);
    editor.$node.removeClass('waitingForProver');
    editor.ruleMenu.suppressing = false;
  }
  if (Toy.profileName) {
    // Collect CPU profiling information.
    console.profile(Toy.profileName);
  }

  // Rule wrappers abort in case of abort or error return
  // from the main part of the rule.  If the precheck or first
  // phase fails, they return falsy (but not undefined), or
  // an Error.
  const result = Toy.value(() => rule( ...args));
  // const thrown = Toy.thrown; // This could give the thrown value.

  if (Toy.profileName) {
    console.profileEnd();
  }
  // Update the rule stats and show them.
  this.lastRuleTime = Date.now() - startTime;
  this.lastRuleSteps = Toy.getStepCounter() - startSteps;
  // TODO: Consider providing an event with info the ProofEditor can
  //   use to display this info -- and move this code into handler.
  this._proofEditor.$node
    .find('.ruleTime').text(Math.ceil(this.lastRuleTime));
  this._proofEditor.$node
    .find('.ruleSteps').text(Math.ceil(this.lastRuleSteps));
  // Clear the initial invisible state.
  this._proofEditor.$node
    .find('.ruleStats').toggleClass('invisible', false);

  // A rule may abort (throw), or certain rules may return null
  // indicating failure, such as a rule that attempts to prove a
  // statement.
  if (result === true) {
    // Do nothing.
  } else if (!(result instanceof Toy.Step)) {
    // It is possible to display more information about thrown
    // errors (aborts), but it may not be helpful to the user.
    const message = 'Rule failed:' + ruleName;

    console.warn(`Rule ${ruleName} failed`);
    if (result instanceof Error) {
      console.warn(result.message);
    } else {
      console.warn('Result:', result);
    }

    this.report(message);
  } else if (result.rendering) {
    // If there is already a rendering, Expr.justify must have found
    // that the "new" step was identical to one of its dependencies,
    // so don't try to add it.  The implementation only currently
    // supports one render per step anyway.
    // This should have been reported to the user at suggestion time.
    // TODO: Consider not running the rule at all.
    console.log('no change');
  } else {
    // Success!
    // TODO: Trigger an event and let the proofDisplay show the step,
    //   removing most of this code.  It may be desirable for the
    //   proof display to trigger another event after the step is
    //   successfully rendered, triggering auto-simplification.
    const error = Toy.catchAborts(() => {
      self._proofEditor.addStep(result);
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
      const simplified = autoSimplify(result);
      if (!simplified.sameAs(result)) {
        self.proofDisplay.addDerivation(simplified);
      }
    });
  }
  if (!deferCleanup) {
    cleanup();
  }
};

/**
 * Create and fill in part of the args array with the step or step and
 * path of the UI's selection if there is one, using the input
 * descriptor of of the StepEditor's current rule.  Currently not
 * picky about the detailed requirements of the various kinds of site
 * and step arguments.  Relies on other components to do these checks.
 * The length of the array is the max of the "length" of the rule
 * function and any info.maxArgs.
 *
 * Also fills any "ed:" input, so perhaps this could be named
 * argsFromContext.
 */
argsFromSelection(ruleName) {
  var rule = Toy.rules[ruleName];
  var nargs = Math.max(rule.length, rule.info.maxArgs || 0);
  var args = new Array(nargs);

  // Some pseudo-rules for proof editing and such need to refer
  // to the proof editor.
  const ned = rule.info.inputs.ed;
  if (ned) {
    args[ned - 1] = this._proofEditor;
  }

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
fillFromForm(ruleName, args) {
  var self = this;
  var rule = Toy.rules[ruleName];
  let success = true;
  $(this.$form).find('input').each(function() {
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
      var which = Number(match[2]);
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
parseValue(value, type) {
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
    return this.proofDisplay.steps[index].original;
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
}

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
 * Requests running the rule with the given args as soon as the UI has
 * opportunity to repaint, and indicates that the prover is working.
 */
function tryRuleSoon(stepEditor, ruleName, args) {
  args.forEach(function(arg) {
      if (Toy.isProved(arg) && arg.isRendered()) {
        // Really all step arguments to all steps everywhere should be
        // non-renderable in the current implementation, but this situation
        // is arguably a greater risk than others.
        console.error('Argument step ' + arg.stepNumber + ' is renderable.');
      }
    });
  stepEditor._proofEditor.$node.addClass('waitingForProver');
  // Do not respond to menu mouse events until the rule has actually run.
  stepEditor._proofEditor.ruleMenu.suppressing = true;
  // Try running the rule once the UI shows that the prover is working.
  Toy.afterRepaint(stepEditor._tryRule.bind(stepEditor, ruleName, args));
}

// Computes an array of significant subgoals added to the given step
// by the given "replacer" in case it is used to replace some part of
// the step.  The goal is intended to be the proof goal, or may be
// nullish.  Any assumptions of the replacer that are not among either
// the step's assumptions or the goal's assumptions will be in the
// result array.
const addedSubgoals = (step, replacer, goal) => {
  const subgoals = [];
  const newAsms = replacer.getAsms();
  if (newAsms) {
    const goalAsms = goal ? goal.asmSet() : new TermSet();
    const currentAsms = step.asmSet();
    newAsms.scanConj(a => {
      // Ignore asms that were expected (in the goal), or
      // already in the input step.
      if (a.likeSubgoal()) {
        if (!goalAsms.has(a) && !currentAsms.has(a)) {
          subgoals.push(a);
        }
      }
    });
  }
  return subgoals;
}

/**
 * Supply this with an actual proof step.  If the rule has property
 * 'autoSimplify', this applies the value of the property to the step
 * as the auto-simplification.  If it returns a falsy value it will be
 * treated as a no-op (identity function).
 *
 * Otherwise if the step's rule has a "site" argument and it references
 * the "assumptions side" of the step, simplify that side, else the
 * "focal part".
 *
 * TODO: Consider moving smarts about a "site" argument into
 *   simplifyFocalPart.
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
  return step.simplifyUsual();
}

export interface Expr {
  simplifyUsual();
}
/**
 * Simplify this step based on its target site, if any,
 * simplify the asm side if it refers into the asms, otherwise
 * the "focal part".  Hopefully this can be considered the
 * default style of autosimplification.
 *
 * TODO: Should this be a rule?
 */
Step.prototype.simplifyUsual = function() {
  const step = this;
  const path = Toy.getStepSite(step);
  return (path && step.isAsmSide(path)
          ? Toy.rules.simplifySite(step, '/left')
          : Toy.rules.simplifyFocalPart(step) || assert(false));
};

//// RULEMENU

class RuleMenu {
  proofEditor: ProofEditor;
  _refresher;
  length: number;
  hovering;
  suppressing: boolean;
  timer: number;
  $modeList;
  $node;
  $items;
  $title;

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
constructor(proofEditor) {
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
  // Timer (from setTimeout) that will run an action unless cleared by
  // mouse movement.  Helps detect "mouse still" conditions.
  self.timer = null;

  const $modeList = $('<div class=modeList>');
  self.$modeList = $modeList;
  $modeList.append('<div class="mode selected" data-mode=general>' +
                   'Basic</div>',
                   '<div class=mode data-mode=algebra>Tactics</div>',
                   '<div class=mode data-mode=other>More</div>',
                   '<div class=mode data-mode=descriptors>Descriptions</div>',
                   '<div class=mode data-mode=edit>Edit</div>',
                  );

  // Rule chooser:
  const $node = $('<div class="ruleMenu">').append($modeList);
  // Top node of the actual rule menu display.
  self.$node = $node;
  // Container node for menu items.
  self.$items = $('<div class=rulesItems>');

  self.$title = $('<div class=ruleMenuTitle>Actions:</div>');

  // An intermediate DIV.  This one is set to have vertical scrolling,
  // and the rulesItems div can be inline-block to shrink-wrap itself
  // around the individual items.
  var $scrollArea = $('<div class=scrollingMenu>');
  $scrollArea.append(self.$items);
  $node.append(self.$title, $scrollArea);

  // Set up event handlers.

  const $ed = proofEditor.$node;

  $node.on('mouseenter mouseleave', function(event) {
    $ed.toggleClass('ruleMenuHovered', event.type === 'mouseenter');
  });
  
  // This code triggers potential change of menu mode when
  // the mouse stops within one of the .mode regions.
  // It sets up the timer on movement and also cancels any
  // timer that is currently set, so the action only occurs
  // if the mouse does not move (or leave the region) during
  // the interval.
  $modeList.on('mousemove', '.mode', function(event) {
    const target = this;
    if (proofEditor.stepEditor.formShowing) {
      // Do not change modes if the rule form is displayed.
      return;
    }
    const $selected = $modeList.find('[class~=selected]');
    const mode = this.dataset.mode;
    if (mode) {
      if (!$selected.is(this)) {
        clearTimeout(self.timer);
        self.timer = setTimeout(event => {
          // This is the action that changes the menu mode.
          $selected.removeClass('selected');
          $(target).addClass('selected');
          proofEditor.showRuleType = mode;
          proofEditor.ruleMenu.refresh();
          proofEditor.stepEditor.hideForm();
        }, 50);  // We are using a 50msec interval.
      }
    }
  });
  $modeList.on('mouseleave', '.mode', function(event) {
    clearTimeout(self.timer);
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

  // Ensure that the selected menu is initialized.
  this.refresh();
}

/**
 * Updates the step suggestions and rule menu to offer items
 * reflecting the currently-selected step or term, if any.
 */
_update() {
  var self = this;
  const proofEditor = self.proofEditor;
  const stepEditor = proofEditor.stepEditor;

  const blurbs = {
    general: 'Rewrites and other often-used actions:',
    algebra: 'Combinations, some for basic algebra:',
    descriptors: 'Unique existence and such:',
    other: 'Advanced or less common:',
  };
  const mode = proofEditor.showRuleType;
  const blurb = blurbs[mode] || 'Actions:';
  if (blurb) {
    self.$title.html(blurb);
  }

  var $items = self.$items;
  // Remove data and event handlers from suggestions.  They have
  // not been previously removed.
  $items.find('.ruleItem').each(function() {
      var suggestion = $(this).data('suggestion');
      suggestion && $(suggestion).remove();
    });
  $items.empty();
  const selStep = proofEditor.proofDisplay.selection;
  const thisStep = selStep && selStep.original;
  const selection = selStep && selStep.selection;
  const sitePath = selection && selStep.prettyPathTo(selection);

  // Array of plain objects, on per menu item.
  var itemInfos = [];

  // Find inference rules that appear relevant to the current
  // selection and proof status.
  self.offerableRuleNames().forEach(function(ruleName) {
      // Info is a string or array of strings.
      var info = ruleMenuInfo(ruleName, selStep, selection, proofEditor);
      if (typeof info === 'string') {
        itemInfos.push({ruleName: ruleName, html: info});
      } else if (Array.isArray(info)) {
        // An array occurs when a rule may be used in multiple ways.
        info.forEach(function(arg) {
          if (arg.constructor === Object) {
            itemInfos.push(arg);
          } else {
            console.error('Bad menu info:', arg);
            debugger;
          }
        });
      } else if (info) {
        console.error('Bad menu info:', info);
        debugger;
      }
  });

  if (selection) {
    // A term is selected.  Find proof steps that can serve as rewrite
    // rules with the current situation / selection.

    // Check a couple of characteristics of the schema.
    const checkSchema = schema => {
      if (!Toy.coreUnifTypes(selection.type, schema.type)) {
        return false;
      }
      if (selection.isCall2('=') && schema.isCall2('=') &&
          !Toy.coreUnifTypes(selection.getBinOp().type,
                             schema.getBinOp().type)) {
        return false;
      }
      return true;
    };
           

    //
    // Search for steps that could rewrite the selection.
    //
    proofEditor.steps.forEach((schemaStep, index) => {
      const submenu = proofEditor.showRuleType;

      // Rewriting with steps applies only to the "general" menu.
      if (submenu !== 'general') {
        return;
      }

      // This is the step number to report.
      const n = index + 1;
      // This is the part of the schema to match against the selection.
      const schema = schemaStep.matchPart();

      if (proofEditor.goalStatement) {
        const goalSchema = proofEditor.goalStatement.matchPart();
        if (schema.sameAs(goalSchema)) {
          // Don't offer to use the goal to prove itself.
          // That seems counterproductive.
          return;
        }
      }

      if (!checkSchema(schema)) {
        return;
      }

      const map = selection.matchSchema(schema);
      if (!map) {
        return;
      }

      // Try to do the substitution, which can fail.
      const eqn = Toy.catching(
        () => schemaStep.andThen('instMultiVars', map, true));
      if (eqn instanceof Error || !Toy.boundVarsOK(selStep, sitePath, eqn)) {
        return;
      }
      // Substitute into the replacement term part of the schema to
      // get the actual replacement term.
      const r1 = schemaStep.replacementTerm();
      const repl = Toy.catching(
        () => (rules.consider(r1)
               .andThen('instMultiVars', map, true).getRight()));
      if (repl instanceof Error) {
        return;
      }

      let html =
          // \u27ad is a lower-right shadowed rightwards arrow.
          ` \u27ad <b class=resultTerm></b> <input class=subgoals> \
           <span class=description>using step ${n}</span>`;
      const subgoals =
            addedSubgoals(thisStep, eqn, proofEditor.goalStatement);
      const count = subgoals.length;
      if (count === 0) {
        // If there are no significant new assumptions, give this
        // rewrite priority with an extra leading space.
        html = ' ' + html;
      }
      const $node = $('<span>').append(html);
      $node.find('.resultTerm').append(repl.renderTerm());
      if (count > 0) {
        const plural = count > 1 ? 's' : '';
        $node.find('.subgoals')
          .append(` with ~${count} new subgoal${plural}`);
      }
      itemInfos.push({ruleName: 'rewriteFrom',
                      ruleArgs: [selStep.original, sitePath,
                                 schemaStep.original],
                      html: html,
                      $node: $node
                     });
    });

    //
    // Search for registered facts that could rewrite the selection.
    //
    self.offerableFacts().forEach(function(info) {
      // TODO: Factor out all of this checking and replacement term
      //   computation, then use it here and just above.
      const fact = info.goal;

      // This is special case code for rewriting of predicates to set
      // membership.
      if (selection.isInfixCall()) {
        // Don't offer this transformation on infix calls.  It's not
        // especially helpful and looks weird.
        if (fact.alphaMatch('Y x == x in Y')) {
          return;
        }
      }

      // Facts and steps are treated similarly, but facts are
      // automatically renamed here to avoid unneeded identification
      // of variables.

      const schema = fact.matchPart();
      if (!checkSchema(schema)) {
        return;
      }
      const subst = selection.matchSchema(schema);
      if (!subst) {
        return;
      }
      // Prepare to avoid unnecessary identification of free variables
      // that could be kept distinct.  Note that if the user enters a
      // fact statement by hand, this is not done.
      const renamer = fact.distinctifier(thisStep, sitePath, subst);
      const statement = fact.rename(renamer).typedCopy();
      // CAUTION: eqn1 and eqn2 are not to be added to the
      // current theory, as they are only hypothetically true
      // to test the unification.
      //
      // This code smells an awful lot like a rewriting precheck.
      //
      // TODO: Consider a mechanism to check without a
      // deduction step, or invent a "suppose" rule that
      // proves (forall)A => A for arbitrary A, and use that.
      const eqn1 = rules.assert(statement);
      // Try to do the substitution, which can fail.
      const eqn2 = Toy.catching(
        () => eqn1.andThen('instMultiVars', subst, true));
      if (eqn2 instanceof Error || !Toy.boundVarsOK(thisStep, sitePath, eqn2)) {
        return;
      }
      const resultTerm = eqn2.replacementTerm();

      // The special character is a form of white right arrow.
      let html =
          ' \u27ad <b class=resultTerm></b><input class=subgoals>';
      const shorty = statement.shortForm();
      const mainText = Toy.trimParens(shorty.toHtml());
      const blurb = (info.definitional
                     ? 'definition of ' + statement.getLeft().func().name
                     : 'using ' + mainText)
      html += (' <span class=description>' + blurb + '</span>');
      const $node = $('<span>').append(html);
      const $resultTerm = $node.find('.resultTerm');
      $resultTerm.append(resultTerm.renderTerm());

      const subgoals =
            addedSubgoals(thisStep, eqn2, proofEditor.goalStatement);
      const count = subgoals.length;
      if (count > 0) {
        const plural = count > 1 ? 's' : '';
        $node.find('.subgoals')
          .append(` with ~${count} new subgoal${plural}`);
      }
      if (count === 0) {
        // If there are no significant new assumptions, give this
        // rewrite priority with an extra leading space.
        html = ' ' + html;
      }
      const result = {
        ruleName: 'rewrite',
        ruleArgs: [thisStep, sitePath, statement],
        html: html,
        $node: $node
      };
      itemInfos.push(result);
    });
  }

  // Ensure that each info has a priority.
  itemInfos.forEach(info => {
    if (info.priority == undefined) {
      // This sets the priority to the number of leading blanks.
      info.priority = info.html.search(/[^ ]/);
      // Remove any leading blanks.
      info.html = info.html.slice(info.priority);
    }
  });

  // Sort the itemInfos.
  itemInfos.sort(function(a, b) {
    // We use leading spaces to influence sorting: items with
    // more leading spaces come before ones with fewer.
    //
    // Higher priority comes first.
    const diff = b.priority - a.priority;
    // If same priority, compare the HTML alphabetically.
    return diff !== 0 ? diff : a.html.localeCompare(b.html);
  });

  // Generate menu items from itemInfos.
  // This can use item properties "$node" or "html",
  // "ruleName", and "ruleArgs".
  var items = itemInfos.map(function(info) {
    var $item = $('<div class="ruleItem noselect">');
    $item.append(info.$node || info.html);
    $item.data('ruleName', info.ruleName);
    $item.data('ruleArgs', info.ruleArgs);
    // For any "input" elements, append the rendering of the ruleArg
    // term or step at index "i" through the data-arg attribute with
    // value "i".
    $item.find('input').replaceWith(function() {
      const index = this.dataset.arg;
      return index ? info.ruleArgs[index].renderTerm() : [];
    });
    return $item
  });
  self.length = items.length;
  $items.append(items);
  if (selection) {
    // If there is a selected term, render it and any right neighbor
    // term, and insert the renderings into all menu items that have
    // slots for them.
    //
    // TODO: Uncomment this line to get a rendering of the selection.
    // var $term = $(selection.renderTerm());
    $items.find('.menuSelected').append('&star;');
    var rightTerm = Toy.getRightNeighbor(selStep, selection);
    var $right = rightTerm ? $(rightTerm.renderTerm()) : '?';
    $items.find('.menuRightNeighbor').append($right);
  }
}

/**
 * Handler for selection of a menu item.  Overall purpose is to run
 * the appropriate rule from information already available, otherwise
 * to display an input form.
 */
handleMouseClickItem(node, event) {
  if (this.suppressing) {
    return;
  }

  const proofEditor = this.proofEditor;
  let uxStatus = localStorage.getItem('Toy:uxOK');
  if (uxStatus == null) {
    // On first use of the menu, if uxOK is unset,
    // get the user to set it explicitly, and ignore
    // the usual menu action.
    const $pnode = proofEditor.$node;
    $pnode.find('.uxDialog').removeClass('invisible');
    $pnode.addClass('hasDialog');
    return;
  }

  // Track these events in Matomo.
  Toy.trackAppEvent('MainMenu');

  // TODO: Consider generating an event here and moving
  //   much of this code elsewhere.
  const ruleName = $(node).data('ruleName');
  const ruleArgs = $(node).data('ruleArgs');
  const stepEditor = proofEditor.stepEditor;
  // This code runs from a click, so a suggestion may well
  // be active.  Make sure it is not displayed.
  proofEditor.proofDisplay.hideSuggestion();
  proofEditor.stepEditor.ruleName = ruleName;
  var rule = Toy.rules[ruleName];
  if (rule) {
    var args = ruleArgs || stepEditor.argsFromSelection(ruleName);
    if (stepEditor.checkArgs(args, rule.info.minArgs, false)) {
      tryRuleSoon(stepEditor, ruleName, args);
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
      stepEditor.$form.find('.customForm').html(format(template, formatArgs));
      stepEditor.showForm();
      addClassInfo(stepEditor.$form);
      if (!usesSite(rule)) {
        stepEditor.addSelectionToForm(rule);
      }
      // Focus the first empty text field of the form.
      stepEditor.$form.find('input[type=text],input:not([type])')
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
    // TODO: Change over to using the usual ruleName and ruleArgs
    //   approach rather than this hack.
    // 
    // Values "fact etc" indicate use of rules.rewrite, and
    // the desired fact is indicated by the rest of the value.
    var siteStep = stepEditor.proofDisplay.selection;
    if (!siteStep || !siteStep.selection) {
      stepEditor.error('No selected site');
    }
    tryRuleSoon(stepEditor,
                 'rewrite',
                 [siteStep.original,
                  siteStep.prettyPathTo(siteStep.selection),
                  // Parsing here will cause the wff to be taken literally
                  // without potential addition of type assumptions.
                  //
                  // TODO: When applying a looked-up fact
                  // interactively, automatically rename any of its
                  // variables that do not participate in the
                  // substitution so they will stay distinct from all
                  // other free variables in the result.
                  Toy.parse(ruleName.slice(5))]);
  } else if (ruleName !== '') {
    assert(false, format('No such rule: {1}', ruleName));
  }
  // if ruleName is '' do nothing at all.  This is a ruleMenu comment.
}

/**
 * Event handler for mouseenter events on RuleMenu items.
 */
handleMouseEnterItem(node, event) {
  if (this.suppressing) {
    return;
  }

  const ruleMenu = this;
  const $node = $(node);
  const proofEditor = ruleMenu.proofEditor;
  const stepEditor = proofEditor.stepEditor;
  const ruleName = $node.data('ruleName');
  const ruleArgs = $node.data('ruleArgs');
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
    if (rule) {
      // It is a rule other than a rewrite with fact.
      var args = ruleArgs || stepEditor.argsFromSelection(ruleName);
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
          // First tidy up a little.
          $node.removeData('promise');
          // If the rule runner throws, the onerror handler will
          // return an Error as info.result, so the value will
          // be undefined, which is OK here.
          var value = info.result.value;
          // Make note of the result, remembering its node.
          if (ruleMenu.hovering === $node[0]) {
            // At this point in time after the rule has run, if this
            // item is hovered, show the result.
            var node = (value instanceof Step
                        ? display.stepSuggestion(value)
                        : display.suggestionMessage('failed'));
            $node.data('suggestion', node);
            display.suggest(node);
          }
        })
        .catch(function(info) {
            // Uncaught worker errors invoke this with result info.
            // If the "then" throws an error, the error becomes the info.
            // Note that .catch sets up a "catch" around the .then code.
            $node.removeData('promise');
            var messageNode = display.suggestionMessage('oops, not applicable');
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
refresh() {
  this._refresher.activate();
}

/**
 * Returns a list of names of rules that are "offerable" in the
 * sense of "offerable" returning true and labelApproved returning true.
 */
offerableRuleNames() {
  var matches = [];
  for (var name in Toy.rules) {
    if (this.labelApproved(name) && this.offerableRule(name)) {
      matches.push(name);
    }
  }
  matches.sort();
  return matches;
}

/**
 * Policy-based rule offering policy function based on rule labels,
 * current editor.showRuleType (current menu name), and
 * editor.showRules.  Given a rule name, returns a truthy value iff
 * current policy is to show the rule.
 */
labelApproved(name) {
  const editor = this.proofEditor;
  const labels = Toy.rules[name].info.labels;
  if (editor.showRules.indexOf(name) >= 0) {
    return true;
  }
  const selStep = editor.proofDisplay.selection;
  const okAlgebra = () =>
        labels.algebra || labels.tactic;
  const okGeneral = () =>
        labels.general || labels.basic || labels.none;
  switch (editor.showRuleType) {
  case 'edit':
    return labels.edit || labels.display;
  case 'algebra':
    // The "algebra" value is really for tactics these days.
    return okAlgebra();
  case 'general':
    return okGeneral();
  case 'other':
    return !okAlgebra() && !okGeneral() && !labels.primitive;
  default:
    return false;
  }
}

/**
 * Returns true iff the rule name can be offered by the UI, based on
 * any current selection and declared inputs.  If there are no
 * declared inputs, it does not count as a rule for this purpose.
 * This method does not screen out rules that lack a way to present a
 * menu string; use the ruleMenuInfo function for that.
 *
 * If there is a selection and the rule can get all of its arguments
 * from the selection, this screens the rule with the precheck.  If
 * the rule can use the current selection (acceptsSelection returns
 * true), and the rule has a toOffer property, this screens the rule
 * with the toOffer property, potentially in addition to the precheck.
 *
 * A rule that accepts a site or step argument is only considered
 * offerable here if there is a selection.
 * 
 * This incidentally avoids offering an otherwise offerable rule
 * if it would need a form for user input, but has none.
 *
 * TODO: Consider adding a rule attribute to suppress offering
 *   the rule in any menu.
 */
offerableRule(ruleName) {
  const rule = Toy.rules[ruleName];
  const info = rule.info;
  const editor = this.proofEditor;
  const step = editor.proofDisplay.selection;
  const inputs = info.inputs;
  if (step && info.menuGen) {
    // Apply the menuGen when there is some form of selection.
    return true;
  }
  if (Toy.isEmpty(inputs)) {
    // A rule with no stated inputs is a fact or theorem, but
    // we do not offer it as a rule.  Or perhaps check
    // rule.length.
    return false;
  }
  if (step) {
    // Something is selected.
    var precheck = rule.precheck || rule.prep;
    var term = step.selection;
    // See if the rule has a precheck that can "rule it out".
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
                // Uses prettyPathTo to provide the same path
                // provided by argsFromSelection.
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
  } else {
    // Only offer a rule that requires a step or site if there
    // is a selection.
    for (const type in info.inputs) {
      // It is OK to use "in", since the type will not be the name of
      // a method on Objects.
      if (type in stepTypes || type in siteTypes) {
        return false;
      }
    }
    if (!info.form) {
      // TODO: Preferably issue some such warning in addRule so
      //   this warning will be unnecessary.  The conditions for it
      //   are somewhat complex though.
      console.warn(Toy.format('Rule {1} lacks an input form', ruleName));
      return false;
    }
    // All the above checks pass, so we can offer the rule.
    return true;
  }
}

/**
 * Returns an array of fact info objects for facts that are offerable
 * as rewrite rules in the UI menus based on the categories of the fact
 * including at least one of the categories of the current menu.
 */
offerableFacts() {
  // TODO: filter facts based on constants they may introduce
  //   into a formula, compared with ones approved by the user
  //   and/or appearing already in the proof.
  const self = this;
  const facts = [];
  const step = self.proofEditor.proofDisplay.selection;
  const expr = step && step.selection;
  if (expr) {
    // Set of categories for the current menu
    const menuCats = catsOfMenu.get(self.proofEditor.showRuleType);

    // Consider each registered fact:
    Toy.eachFact(function(info) {
      const goal = info.goal;
      if (Toy.intersection(menuCats, info.categories).size > 0) {
        const matchTerm = goal.matchPart();
        // We never offer a fact if the goal matches _everything_ (of
        // suitable type).  This check may be unnecessary.
        if (// !matchTerm.isVariable() && XXX
            // Rewrites matching a variable should have low priority
            // in the menu display.
            // TODO: Implement priorities and sorting by priority.
            Toy.coreUnifTypes(expr.type, matchTerm.type) &&
            expr.matchSchema(matchTerm)) {
          facts.push(info);
        }
      }

    });
  }
  return facts;
}
}
// This maps from menu name to a set of fact category names to be
// presented in that mode.
const catsOfMenu =
      new Map([['none', new Set()],
               ['algebra', new Set(['algebra'])],
               ['general',
                new Set(['general', 'simplifier', 'algebra'])],
               ['descriptors', new Set(['descriptors'])],
               ['edit', new Set(['edit'])],
               ['other', new Set(['advanced', 'other',
                                  'desimplifier', 'forward'])]]);

/**
 * This matches a step against the inputs descriptor of an inference
 * rule.  The step is the selected proof step, ruleName is the name of
 * the rule to match against.  Only call this if a step or part of a
 * step is selected.
 *
 * If something is selected, this accepts rules whose inputs descriptor
 * is compatible with the selection.  See the code for details.
 *
 * The rule can also require other inputs as well as ones the
 * selection can supply
 */
function acceptsSelection(step, ruleName) {
  var info = Toy.rules[ruleName].info;
  var argInfo = info.inputs;
  // Selected expression (within a step).
  var expr = step.selection;
  if (expr) {
    // Otherwise OK if it takes a site, or is a proper binding site
    // or a beta-reducible expression.
    // 
    // TODO: prevent selection of bound variables as terms.
    const result =
          (argInfo.site
           || (argInfo.bindingSite && expr instanceof Toy.Lambda)
           || (argInfo.reducible
               && expr instanceof Toy.Call
               && expr.fn instanceof Toy.Lambda));
    return result;
  } else {
    // If the rule needs a site, do not accept just a step.
    return (!argInfo.site &&
            (argInfo.step
             || (argInfo.equation && step.isEquation())
             || (argInfo.implication && step.implies())));
  }
}

/**
 * Produces a rule menu entry from a ruleName.  Called with a
 * (rendered) step if there is a selection, the selected term if a
 * term is selected, and the menu's ProofEditor.
 *
 * This returns either a falsy value (including the empty string),
 * indicating the rule will not be offered, or a string with the menu
 * HTML, or an array, indicating multiple menu items for
 * this rule with the possibly selected step and term.
 * An array must contain strings or plain objects with properties:
 *
 * ruleName: rule name string
 * ruleArgs: array of arguments to be passed to the rule
 * html: HTML string to be displayed.
 * $node: optional jQuery object containing a DOM node to insert.
 *   If given, the "html" only affects sorting.
 * 
 * Strings in the return value should be HTML text.
 *
 * If there is a selected term, it can be formatted using {term} in
 * the rule's "menu" format string, or {right} for the term's
 * right-hand neighbor when there is one.
 */
function ruleMenuInfo(ruleName, step, term, proofEditor) {
  // Set up convenient substitutions for occurrences of {term} and
  // {right} in menu format strings via Toy.format.  These support
  // deferral of the rendering and insertion of the rendering of the
  // term and right neighbor to the RuleMenu._update code where it is
  // more convenient and the HTML has been converted to DOM structure.
  const formatArgs = {term: '<span class=menuSelected></span>',
                      right: '<span class=menuRightNeighbor></span>'};
  const info = Toy.rules[ruleName].info;
  const gen = info.menuGen;
  if (gen) {
    const items = gen(ruleName, step, term, proofEditor);
    // Check that the menu items are well-formed.
    if (Array.isArray(items)) {
      for (const item of items) {
        if (item.constructor === Object &&
            (typeof item.ruleName === 'string') &&
            (item.ruleArgs == null || Array.isArray(item.ruleArgs)) &&
            typeof item.html === 'string') {
          item.html = Toy.format(item.html, formatArgs);
        } else {
          console.error('Bad rule menu item:', item);
          debugger;
        }
      }
    } else {
      if (items && typeof items !== 'string') {
        console.error('Bad menuGen result:', items);
        debugger;
      }
    }
    return items;
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
      return Toy.format(info.menu, formatArgs);
    } else {
      const tip = info.basicTooltip;
      // TODO: Reconcile use of math markup here vs. non-use in menus.
      return tip && Toy.mathMarkup(info.basicTooltip);
    }
  }
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
        runRule: message =>
          // This rebinding is specifically for step suggestions,
          // which may fail for a wide variety of reasons.
          Toy.rebind('proceeding', true, () => {
            const value = Toy.rules[message.name].attempt( ...message.args);
            return {value};
          }),
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

// Export public names.
Toy.stepTypes = stepTypes;
Toy.siteTypes = siteTypes;

Toy.ProofEditor = ProofEditor;
Toy.StepEditor = StepEditor;

Toy.tryRuleSoon = tryRuleSoon;
//Toy.exerciseSteps = exerciseSteps;

}  // namespace;
