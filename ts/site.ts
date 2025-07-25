// Copyright Crispin Perdue.  All rights reserved.

'use strict';

/** Exported constructor */
var tippy;

// Prooftoys scripts should not depend on this file, though it may do
// some default configuration.  At present this does not appear to
// depend on any other Prooftoys script, so its functions can be used
// before the other scripts are loaded.

namespace Toy {

/**
 * Track uncaught errors with Matomo.
 */
window.onerror = function(message, source, lineno, colno, error) {
  const track = Toy.trackAppEvent;
  if (track) {
    if (error) {
      // Error and error.stack might not exist.
      track('Error', ''+(error.stack || error));
    } else {
      track('Error', message);
    }
  }
};

export var quotes = [];

 export function insertSlogans() {
  var slogan = 'Power tools for your math mind';
  var elt = document.getElementById('slogans');
  if (elt) {
    elt.innerHTML = slogan;

    // Get the collection of quotes.
    quotes = [];
    var quoteIndex = 0;
    // Splits the quote text into quotes and install them
    // into Toy.quotes in random order.
    function setupQuotes(text) {
      var list = text.split('\n\n');
      while (list.length) {
        var i = Math.floor(Math.random() * list.length);
        var quote = list[i];
        quote = quote.replace(/-- .*$/, '<span class=author>$&</span>');
        Toy.quotes.push(quote);
        list.splice(i, 1);
      }
    }
    // Rotates to the next quote.
    function nextQuote() {
      quoteIndex++;
      if (quoteIndex >= Toy.quotes.length) {
        quoteIndex = 0;
      }
      var quote = Toy.quotes[quoteIndex];
      jQuery('#slogans').html(quote);
    }
    // Set up periodic update of the quote display.
    function scanQuotes() {
      if (Toy.quotes.length) {
        setInterval(nextQuote, 30 * 1000);
      }
    }
    // Load the quotes file.
    $.get('share/quotes.txt', {dataType: 'text'})
      .done(function(data) { setupQuotes(data); scanQuotes(); });
  }
};

//
// Generating math symbols and italicizing alphabetic characters for math.
//

/**
 * Replaces ASCII math symbols in the given HTML text with HTML entities
 * for math, and with alphanumeric names in italics.  Operates on each
 * token independently, except exponentiation as a special case with
 * one-character lookahead, written as "^", and subscripting as "_".
 * 
 * TODO: Extend lookahead to a complete token using state.  Support
 *   "**" for exponentiation like "^".
 */
export function mathMarkup0(text, title) {
  // Substitutions for "forall" and "exists" consume any trailing blank,
  // helping to push them up next to following text.
  // "_" for subscript and "^" for superscript are treated specially,
  // while other operator characters can be combined.  These two
  // affect a single following character, i.e. letter or digit.
  var rex =
    /[-!<=>*/&|]+|[_^] ?.|\bforall( |\b)|\bexists1?( |\b)|[a-zA-Z0-9]+/g;
  return text.replace(rex, function(s) {
    if (s.match(/^\^[a-z]/)) {
      // "^" followed by alphabetic char (to catch variables).
      return '<sup><i>' + s[1] + '</i></sup>';
    } else if (s[0] === '^') {
      return '<sup>' + s.slice(1) + '</sup>';
    } else if (s.match(/^_[a-z]/)) {
      return '<sub><i>' + s[1] + '</i></sub>';
    } else if (s[0] === '_') {
      return '<sub>' + s.slice(1) + '</sub>';
    } else if (s.match(/^[a-z][0-9]*$/)) {
      // Variable name, not a constant, see Toy.isVariableName in expr.js.
      return '<i>' + s + '</i>';
    } else {
      // It is a constant name.
      switch(s) {
      case '=>': return title ? 'implies' : '&rArr;';
      case '==': return '&equiv;';
      case '!=': return '&ne;';
      case '<': return '&lt;';
      case '>': return '&gt;';
      case '>=': return '&ge;';
      case '<=': return '&le;';
      case '-': return '&minus;';
      case '*': return '&sdot;';
      case '/': return '&#x2215;';          // Division slash
      case 'forall': return '&forall;';
      case 'forall ': return '&forall;';
      case 'exists': return '&exist;';
      case 'exists ': return '&exist;';
      case 'exists1': return '&exist;!';
      case 'exists1 ': return '&exist;!';
      case '&*':
        // This will be useful for inserting HTML entities
        // and also plain '&'.
        return '&';             // &*amp; -> &amp;
      case '&':
        return title ? 'and' : '&and;';
      case '|':
        return title ? 'or' : '&or;';
      case 'not':
        return title ? 'not' : '&not;';
      case 'in':
        return '&in;';
      case 'notin':
        return '&notin;';
      case 'pi':
        return '&pi;';
      case 'inter':
        return '&#x2229;';
      case 'union':
        return '&#x222A;';
      case 'Inter':
        return '&#x22C2;';
      case 'Union':
        return '&#x22C3;';
      case 'subset':
        return '&subset;';
      case 'subseteq':
        return '&subseteq;';
      case 'CC':
        return '&#x2102;';
      case 'NN':
        return '&#x2115;';
      case 'QQ':
        return '&#x211A;';
      case 'RR':
        return '&#x211D;';
      case 'ZZ':
        return '&#x2124;';
      case 'epsilon':
        // "Lunate epsilon", e.g. for epsilon/delta proofs.
        return '&#x03F5;';
      case 'infinity':
        return '&infin;';
      case 'QED':
        return '<span style="color: black">&#x220E;</span>';
      default:
        return s;
      }
    }
  });
};

/**
 * Postprocess basic results of mathMarkup0 to keep operands of
 * multiplication visually near the "center dot".
 */
 export function mathMarkup(text, title=false) {
  const text0 = Toy.mathMarkup0(text, title);
  return text0.replace(/ &sdot; /g, '&sdot;');
};

/**
 * Convert the text to text using mathMarkup.  Implemented
 * by building DOM elements and getting their text, so probably
 * not the fastest thing in the world.
 */
 export function mathText(text) {
  return jQuery('<span>' + Toy.mathMarkup(text) + '</span>').text();
};

/**
 * Converts <code> element contents into math-oriented HTML if it has
 * no language given, or given as "logic" (or "fallback"), except if
 * the block has no language and its text begins with "\", this strips
 * the "\", but does not otherwise process the content.
 *
 *(Recall that Markdown converts backticks to <code> and escapes all
 * text within the Markdown code block to prevent interpretation as
 * HTML.  Hugo's Goldmark processor emits a data-lang attribute and a
 * language-xxx class if a language is given.)
 */
 export function mathifyAll() {
  jQuery('code').replaceWith(function() {
    const content = $(this).text();
    const lang = this.dataset.lang;
    const classes = this.className;
    if (!lang && content.startsWith('\\')) {
      const $element = $('<code>');
      $element.text(content.slice(1));
      return $element;
    } else if (!lang || lang === 'fallback' || lang === 'logic') {
      const markup = Toy.mathMarkup(content);
      const title = Toy.mathMarkup(content, true);
      const $element = $('<code>',
                         title === markup || title.includes('\n')
                         ? {'class': 'language-logic'}
                         : {'class': 'language-logic',
                            'data-tippy-content':  title});
      $element.html(markup);
      $element.addClass(classes);
      return $element;
    } else {
      return this;
    }
  });
};


//// Fallback visit checking

// Note a visit by the user, fetching a nonexistent page with URI path
// of current local date and time zone, but avoiding repetitious
// fetches.  Date is in local time, ISO format.
 export function checkVisit() {
  // "sv" is Swedish (not Sweden), a locale using ISO format.
  const date = new Date().toLocaleDateString("sv");
  const tz0 = Intl.DateTimeFormat().resolvedOptions().timeZone;
  const tz = tz0.replaceAll(/ |[/]/g,'-');
  const path = `${date}-${tz}`;
  const key = 'Toy.lastVisit';
  const previous = localStorage.getItem(key);
  if (path !== previous) {
    localStorage.setItem(key, path);
    jQuery.get(`/visits/${path}`);
  }
}

//// URL query parameters

// TODO: Move this code to utils.js.

// Note: This is very similar to URLSearchParams.

// This will contain a map of query string parameter names
// to their values.  Does not handle repeated parameters.
export var queryParams = {};

// The "raw" params is similar, using the same parameter splitting,
// but without decoding parameter values or replacing "+"
// with space.
export var rawQueryParams = {};

( function () {
  function decode(s) {
    return decodeURIComponent(s.replace(/\+/g, " "));
  }
  var query = window.location.search.substring(1);
  var match;
  // Must use a variable to avoid reinitializing.
  var pattern = /([^&=]+)=?([^&]*)/g;
  while (match = pattern.exec(query)) {
    Toy.queryParams[decode(match[1])] = decode(match[2]);
    Toy.rawQueryParams[decode(match[1])] = match[2];
  }
} )();


//// For mobile site "hamburgers":

// The element is a button inserted in partials/hamburger.html.
// The button is styled "display: none" in wider page widths.
const menuTrigger =
  document.querySelector('#toggle-main-menu-mobile' as "button");

if (menuTrigger) {
  menuTrigger.onclick = function() {
    const sidebar = document.querySelector('div.sidebar' as "div");
    if (sidebar) {
      sidebar.classList.toggle('displayed');
      menuTrigger.classList.toggle('is-active');
    }
  };
}

// Initializations on DOM ready.  When this file is loaded before
// util.js, the "$" here refers to jQuery.  In other files it
// will be our own "$".
$(function () {
  Promise.resolve().then(
    // Initializing after promise resolution takes this code
    // out of the jQuery "ready" handler try-catch, so errors
    // here become uncaught as we prefer them to be.
    function () {
      // Potentially fetch a nonexistent page with date and TZ.
      // The fetch writes into the server access log.
      Toy.checkVisit();

      // Create a proof editor for each div.proof-editor node,
      // initializing its steps from a data-steps attribute if the
      // constructor does not load steps from a document.  Re-visiting a
      // page results in loading from a document, so that needs to have
      // priority.
      $('div.proof-editor').each(function () {
        const options = this.dataset;
        const editor = new ProofEditor(options);
        $(this).append(editor.$node);
        window.proofEditor = editor;
      });

      // Similarly create a proof display for each div.proof-display node.
      // These are read-only.  Expects either a data-doc-name attribute,
      // which refers to proofdata.js data, or data-steps, a string of
      // steps information, i.e. "(steps ... )".  If data-step-filter is
      // truthy, displays only steps for which the string evaluates to
      // truthy given "n" as the step number.  If data-step-limit is
      // parseable as a number, steps after that one are not generated
      // at all.
      $('div.proof-display').each(function () {
        const display = new ProofDisplay();
        const data = this.dataset;
        const docName = data.docName;
        // This is always a number, NaN if not parseable.
        const stepLimit = +data.stepLimit;

        // Loads the proof data for the given document, from
        // proofData, not local storage.
        const loadDoc = () => {
          let stepsInfo;
          if (docName) {
            const proofData = findInProofData(docName);
            if (proofData) {
              stepsInfo = proofDataSteps(proofData);
            } else {
              console.error(`No steps for document ${docName}`);
            }
          } else {
            stepsInfo = data.steps;
            if (!stepsInfo) {
              console.error('No steps for proof display', this);
            }
          }
          window.proofDisplay = display;
          $(this).append(display.node);
          let stepNum = 1;
          const addStep =
            // This always adds the step if stepLimit is NaN.
            (step) => stepNum++ > stepLimit ? false : display.addStep(step);
          // Add each step immediately when computed.
          decodeSteps2(stepsInfo, addStep);
          const filterText = data.stepFilter;
          if (filterText) {
            filterStepDisplays(display, filterText);
          }
        };
        requireScript(realNumbersScript).then(loadDoc);
      });
    }
  );
});

/**
 * Filters the set of steps to be displayed in the proof display
 * based on a filterText string to be evaluated as a JS expression
 * string.  If it is truthy, each step is filtered based on its position
 * in the display, starting with 1.  If the value of the expression is
 * truthy given "n" as the step number, the step is displayed, otherwise
 * hidden with class "hidden".
 */
function filterStepDisplays(display: ProofDisplay, filterText: string) {
  const test = Function('n', 'return ' + filterText);
  const children = $(display.stepsNode).children();
  for (let i = 0; i < children.length; i++) {
    const node = children[i];
    try {
      if (!test(i + 1)) {
        $(node).addClass('hidden');
      }
    } catch(e) {
      console.error(e);
    };
  }
}

//// Managing the footer to account for (invisible) absolute DIVs

let resizer = null;

/**
 * Ensures that any div.pageFooter is positioned below all other
 * content on the page.  Prooftoys uses often-invisble absolutely
 * positioned popup elements that can extend below all other content,
 * and that can let the user scroll beyond the footer if we don't
 * do this.
 *
 * Use padding-top as needed to maintain some vertical whitespace.
 */
function footerOnResize() {
  // If another resize action is pending, clear it to reduce
  // potentially excessive repainting.
  if (resizer != null) {
    clearTimeout(resizer);
  }
  const f = $('div.pageFooter');
  f.css({visibility: 'visible'});
  // Position the footer up top, then give it a short interval
  // for the browser to recompute scrollHeight.
  f.offset({top: 0});
  resizer = setTimeout(function() {
      // The offset and scrollHeight measure what we want.
      f.offset({top: document.body.scrollHeight});
    }, 100);
}

/**
 * Makes image tooltips base
 */
function makeImageTips() {
  tippy && tippy('b[imagetip]', {
    content: (reference) => {
      const img = document.createElement('img');
      img.src = reference.getAttribute('imagetip');
      img.style.maxWidth = '80vw';
      img.style.objectFit = 'scale-down';
      return img;
    },
    placement: 'bottom',
    maxWidth: '82vw',
    delay: [500, 0],
    allowHTML: true,
    arrow: false,
    hideOnClick: false,
  });
}    

/**
 * Makes video tooltips based on info in elements -- SPAN or A or B,
 * with a videotip attribute, where the attribute value is the URL of
 * an mp4 video.  If the element tag is A or B, the element style will
 * have a border box around it.
 */
function makeVideoTips() {
  tippy && tippy('span[videotip], a[videotip], b[videotip]', {
    content: element => {
      const source = element.getAttribute('videotip');
      return `<video muted playsinline style="max-width: 80vw">
                 <source src="${source}" type="video/mp4">
               </video>`;
    },
    placement: 'bottom',
    trigger: 'click',
    maxWidth: '82vw', 
    allowHTML: true,
    interactive: true,
    arrow: false,
    appendTo: () => document.body,
    onShow(instance) {
      let video = instance.popper.getElementsByTagName('video')[0];
      video.currentTime = 0; //start from begining
      video.play();
      video.onended = event => {
        Toy.sleep(1000).then(() => instance.hide());
      }
    },
  });
}

/**
 * Initializations on DOMContentLoaded.
 */
$(function() {
  // Make image tooltips.
  makeImageTips();
  // Make video tooltips as needed.
  makeVideoTips();
  // If there is at least one footer element, this sets up
  // repositioning it any time the window resizes.
  if ($('div.pageFooter').length > 0) {
    footerOnResize();
    $(window).on('resize', footerOnResize);
  }
});

//// The following puts a property on Object.prototype!

// Make debugString accessible as ".$$" for debugger interaction.
if (!Object.prototype.$$) {
  function debstr() {
    return Toy.debugString ? Toy.debugString(this) : '' + this;
  }
  Object.defineProperty(Object.prototype, '$$', {get: debstr});
}

}  // namespace;
