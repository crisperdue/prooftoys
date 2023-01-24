// Copyright Crispin Perdue.  All rights reserved.

'use strict';

window.Toy = window.Toy || {};

// Prooftoys scripts should not depend on this file, though it may do
// some default configuration.  At present this does not appear to
// depend on any other Prooftoys script, so its functions can be used
// before the other scripts are loaded.

+function() {

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

Toy.insertSlogans = function() {
  var slogan = 'Power tools for your math mind';
  var elt = document.getElementById('slogans');
  if (elt) {
    elt.innerHTML = slogan;

    // Get the collection of quotes.
    Toy.quotes = [];
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
 * Replaces ASCII math symbols in the given HTML text with HTML
 * entities for math, and with alphanumeric names in italics.
 */
Toy.mathMarkup0 = function(text, title) {
  // Substitutions for "forall" and "exists" consume a trailing blank,
  // helping to push them up next to following text.
  var rex =
    /[-!<=>*/&|]+|[_^].|\bforall( |\b)|\bexists1?( |\b)|[a-zA-Z]+[0-9]*/g;
  return text.replace(rex, function(s) {
    if (s.match(/^\^[a-z]/)) {
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
 * Postprocess basic results of mathMarkup to keep operands of
 * multiplication visually near the "center dot".
 */
Toy.mathMarkup = function(text, title) {
  const text0 = Toy.mathMarkup0(text, title);
  return text0.replace(/ &sdot; /g, '&sdot;');
};

/**
 * Convert the text to text using mathMarkup.  Implemented
 * by building DOM elements and getting their text, so probably
 * not the fastest thing in the world.
 */
Toy.mathText = function(text) {
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
Toy.mathifyAll = function() {
  jQuery('code').replaceWith(function() {
    const content = $(this).text();
    const lang = this.dataset.lang;
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
Toy.checkVisit = function() {
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
Toy.queryParams = {};

// The "raw" params is similar, using the same parameter splitting,
// but without decoding parameter values or replacing "+"
// with space.
Toy.rawQueryParams = {};

(function () {
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
})();


//// For mobile site "hamburgers":

// The element is a button inserted in partials/hamburger.html.
// The button is styled "display: none" in wider page widths.
const menuTrigger = document.querySelector('#toggle-main-menu-mobile');

if (menuTrigger) {
  menuTrigger.onclick = function() {
    const sidebar = document.querySelector('div.sidebar');
    if (sidebar) {
      sidebar.classList.toggle('displayed');
      menuTrigger.classList.toggle('is-active');
    }
  };
}

// Initializations on DOM ready.  When this file is loaded before
// util.js, the "$" here refers to jQuery.  In other files it
// will be our own "$".
$(function() {
  Promise.resolve().then
  // Initializing after promise resolution takes this code
  // out of the jQuery "ready" handler try-catch, so errors
  // here become uncaught as we prefer them to be.
  (function() {
    // Potentially fetch a nonexistent page with date and TZ.
    // The fetch writes into the server access log.
    Toy.checkVisit();

    // Create a proof editor for each div.proof-editor node,
    // initializing its steps from a data-steps attribute if the
    // constructor does not load steps from a document.  Re-visiting a
    // page results in loading from a document, so that needs to have
    // priority.
    $('div.proof-editor').each(function() {
      const options = this.dataset;
      const editor = new Toy.ProofEditor(options);
      $(this).append(editor.$node);
      window.proofEditor = editor;
    });
    // Similarly create a proof display for each div.proof-display node.
    // These are read-only.
    $('div.proof-display').each(function() {
        const data = this.dataset;
        const stepsInfo = data.steps;
        if (!stepsInfo) {
          console.error('No steps for proof display', this);
        }
        const display = new Toy.ProofDisplay();
        window.proofDisplay = display;
        const decoded = Toy.decodeSteps(stepsInfo);
        if (decoded instanceof Error) {
          // TODO: Give the ordinary user at least a hint that
          //   something went wrong.
          console.error('Failed to decode steps:');
          console.error(decoded);
          display.setSteps([]);
        } else {
          display.setSteps(decoded);
          $(this).append(display.node);
        }
    });
  })
});

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
 * Initializations on DOMContentLoaded.
 */
$(function() {
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

}();
