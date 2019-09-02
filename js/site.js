// Copyright 2011-2019 Crispin Perdue.
// All rights reserved.

var Toy = {};

+function() {

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
Toy.mathMarkup0 = function(text) {
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
      case '=>': return '&rArr;';
      case '==': return '&equiv;';
      case '!=': return '&ne;';
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
      case '&':
      case 'and':
        return '&and;';
      case '|':
      case 'or':
        return '&or;';
      case 'not':
        return '&not;';
      case 'in':
        return '&in;';
      case 'inter':
        return '&#x2229;';
      case 'union':
        return '&#x222A;';
      case 'Inter':
        return '&#x22C2;';
      case 'Union':
        return '&#x22C3;';
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
Toy.mathMarkup = function(text) {
  const text0 = Toy.mathMarkup0(text);
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
 * Converts all <s> and <code> element contents into math-oriented
 * HTML.  Ignores all HTML markup within each element, though HTML
 * entities are OK.
 *
 * Also converts <del> within .preBlock because the Hugo
 * markdown engine ("Black Friday") over-protects <code>
 * within HTML tags.
 */
Toy.mathifyAll = function() {
  jQuery('s, code, .preBlock del').replaceWith(function() {
      return '<code>' + Toy.mathMarkup($(this).text()) + '</code>';
    });
};

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

var _HTML_MAP = {
        '&': '&amp;',
        '<': '&lt;',
        '>': '&gt;',
        '"': '&quot;',
        "'": '&#x27;',
        '/': '&#x2F;',
        '`': '&#x60;'
};

/**
 * Escapes text to guarantee it is not interpreted as containing
 * HTML markup.
 *
 * TODO: Move to utils.js.
 */
Toy.escapeHtml = function(str) {
  return str.replace(/[&<>"'\/`]/g,  // help the emacs parser: "]
                     function(match) { return _HTML_MAP[match]; });
};

//// For mobile site "hamburgers":

const menuTrigger = document.querySelector('#toggle-main-menu-mobile');

menuTrigger && (menuTrigger.onclick = function() {
  // This code will err out if the elements do not exist.
  const sidebar = document.querySelector('div.sidebar');
  sidebar.classList.toggle('displayed');
  menuTrigger.classList.toggle('is-active');
  // const body = document.querySelector('body')
  // body.classList.toggle('lock-scroll');
  });

// Initializations on DOM ready.
$(function() {
    // Create a proof editor for each div.proof-editor node,
    // initializing its steps from a data-steps attribute if the
    // constructor does not load steps from a document.  Re-visiting a
    // page results in loading from a document, so that needs to have
    // priority.
    $('div.proof-editor').each(function() {
        const data = this.dataset;
        const stepsInfo = data.steps;
        const editor = new Toy.ProofEditor();
        editor.initialSteps = stepsInfo;
        window.proofEditor = editor;
        if (!editor.fromDoc) {
          // Editor not loaded from a document, so load it
          // from any data-steps property.
          editor.setRulesMode(data.rulesMode || 'general');
          if (stepsInfo) {
            editor.setSteps(Toy.decodeSteps(stepsInfo));
          }
        }
        $(this).append(editor.containerNode);
      });
  });

}();


//// The following are GLOBAL!

// Global "str" function is useful for converting arbitrary objects
// to strings.
function str(x) {
  if (x.toString == Object.prototype.toString &&
      Toy.debugString) {
    return Toy.debugString(x);
  } else if (Toy.Expr && x instanceof Toy.Expr) {
    var prefix = (x.hasHyps ? '|' : '') + (x.wff ? '|-' : '');
    return (prefix ? prefix + ' ' + x.toString() : x.toString());
  } else {
    return x.toString();
  }
}
// Make str function accessible as ".$$" for debugger interaction.
if (!Object.prototype.$$) {
  Object.defineProperty(Object.prototype,
                        '$$',
                        {get: function() { return str(this); }});
}

