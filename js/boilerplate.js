// Copyright 2011-2018 Crispin Perdue.
// All rights reserved.

// TODO: Deploy the app in a single file under flag control.
// Normally initialize the flag from the page URL, so references
// to localhost use separate sources for easy debugging.
// Load all scripts from js/ subdirectory and preprocess scripts
// into there.


(function() {
  // Try the HTML5 way, otherwise look for a script
  // named boilerplate.js.
  var element = document.currentScript
    || document.querySelector('script[src$="boilerplate.js"]');
  var src = element.getAttribute('src');
  // URL of this script, up to the actual name:
  var prefix = src.replace(/boilerplate.js$/, '');

  function write(html) {
    document.write(html);
  }

  // Fortunately browsers seem to cancel out the prefix and initial
  // ".." in names.
  function getScript(name) {
    document.write('<script src="' + prefix + name + '"></script>\n');
  }

  // Include jQuery in all cases.
  getScript('../lib/jquery-3.1.1.js');

  write('<link rel=stylesheet href=' +
        '"https://fonts.googleapis.com/css?family=Roboto' +
        ':400,400i,700,700i">');

  // Include Font Awesome.
  write('<link rel="stylesheet" href=' +
        '"https://maxcdn.bootstrapcdn.com/font-awesome/4.7.0/css/font-awesome.css">');

  // Include the application's styles.
  write('<link rel="stylesheet" href="../css/logic.css">');

  // Behavior can be customized by this global variable.
  if (!window.noTooltipster) {
    // These load Tooltipster and the light theme from current locations
    // in the source tree.
    write('<link rel="stylesheet" href="' + prefix +
          '../lib/tooltipster-master/dist/css/tooltipster.bundle.css">');
    write('<link rel="stylesheet" href="' + prefix +
          '../lib/tooltipster-master/dist/css/plugins/tooltipster/sideTip' +
          '/themes/tooltipster-sideTip-light.min.css">');
    getScript('../lib/tooltipster-master/dist/js/tooltipster.bundle.js');
  }

  // Loading of scripts can be customized by this global variable.
  if (!window.noProofScripts) {
    getScript('util.js');
    getScript('prelim.js');
    getScript('expr.js');
    getScript('xutil.js');
    getScript('step-editor.js');
    getScript('../jsc/rendering.js');
    getScript('solution-status.js');
    getScript('engine.js');
    getScript('logic.js');
    getScript('numbers.js');
    // Support Google Plus stuff in particular.
    document.write('<script src="https://apis.google.com/js/platform.js">\n' +
                   '{parsetags: "explicit"}\n' +
                   '</script>\n');
  }
})();

var Toy = Toy || {};

// Boilerplate text for the left navigation area.
Toy.navText = [
  '<a class=nav href="index.html">',
  'Home page</a>',
  '<a class=nav href="introduction.html">',
  'Introduction to proofs</a>',
  '<a class=nav href="booleans.html">',
  'Basic logic through pictures</a>',
  '<a class=nav href="real-numbers.html">',
  'Working with real numbers</a>',
  '<a class=nav href="proofbuilder.html">',
  'Interactive proof builder</a>',
  '<a class=nav target=_blank',
  '   href="http://github.com/crisperdue/prooftoys">',
  ' GitHub project site</a>',
  '<a class=nav target=_blank',
  '   href="https://groups.google.com/d/forum/prooftoys">',
  ' Discussion forum</a>',
  '<a class=nav target=_blank',
  '   href="https://github.com/crisperdue/mathtoys/issues">',
  ' Feedback</a>',
  '<br>',
  '<a href="http://mathtoys.org/">Mathtoys website<br>(algebra problems)</a>',
  '</ul>'
].join('\n');

// Also inserts Google Plus content if any.
Toy.insertNav = function() {
  var nav = document.getElementById('leftNav');
  if (nav) {
    nav.innerHTML = Toy.navText;
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

// Google analytics support.
if (!location.pathname.match(/\/tests.html$/)) {
  var id = (location.hostname == 'prooftoys.org'
            ? 'UA-28801147-2' : 'UA-28801147-3');
  (function(i,s,o,g,r,a,m){i['GoogleAnalyticsObject']=r;i[r]=i[r]||function(){
  (i[r].q=i[r].q||[]).push(arguments)},i[r].l=1*new Date();a=s.createElement(o),
  m=s.getElementsByTagName(o)[0];a.async=1;a.src=g;m.parentNode.insertBefore(a,m)
  })(window,document,'script','https://www.google-analytics.com/analytics.js','ga');

  ga('create', id, 'auto');
  ga('send', 'pageview');
}

//
// Generating math symbols and italicizing alphabetic characters for math.
//

/**
 * Replaces ASCII math symbols in the given HTML text with HTML
 * entities for math, and with alphanumeric names in italics.
 */
Toy.mathMarkup = function(text) {
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
 * Convert the text to text using mathMarkup.  Implemented
 * by building DOM elements and getting their text, so probably
 * not the fastest thing in the world.
 */
Toy.mathText = function(text) {
  return jQuery('<span>' + Toy.mathMarkup(text) + '</span>').text();
};

/**
 * Converts all <S> element contents into math-oriented HTML.
 * Ignores all HTML markup within each element, though HTML
 * entities are OK.
 */
Toy.mathifyAll = function() {
  jQuery('s').replaceWith(function() {
    return '<span class="mathColor">' +
      Toy.mathMarkup($(this).text()) +
      '</span>';
  });
};

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
 */
Toy.escapeHtml = function(str) {
  return str.replace(/[&<>"'\/`]/g,  // help the emacs parser: "]
                     function(match) { return _HTML_MAP[match]; });
};

// Global "str" function is useful for converting arbitrary objects
// to strings.
function str(x) {
  if (x.toString == Object.prototype.toString) {
    return Toy.debugString(x);
  } else if (x instanceof Toy.Expr) {
    var prefix = (x.hasHyps ? '|' : '') + (x.wff ? '|-' : '');
    return (prefix ? prefix + ' ' + x.toString() : x.toString());
  } else {
    return x.toString();
  }
}
// Make str function accessible as ".$$" for debugger interaction.
Object.defineProperty(Object.prototype,
                      '$$',
                      {get: function() { return str(this); }});
