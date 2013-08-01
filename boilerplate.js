// Copyright 2011, 2012 Crispin Perdue.  All rights reserved.

// TODO: Deploy the app in a single file under flag control.
// Normally initialize the flag from the page URL, so references
// to localhost use separate sources for easy debugging.
// Load all scripts from js/ subdirectory and preprocess scripts
// into there.

// Include jQuery in all cases.
document.write('<script src="lib/jquery-1.9.1.js"></script>\n');

if (!window.noProofScripts) {
  document.write('<script src="expr.js"></script>\n');
  document.write('<script src="step-editor.js"></script>\n');
  document.write('<script src="jsc/proof.js"></script>\n');
  document.write('<script src="theorems.js"></script>\n');
}

var Toy = Toy || {};

// Boilerplate text for the left navigation area.
Toy.navText = [
  '<a class=nav href="index.html">',
  'Home page</a>',
  '<a class=nav href="introduction.html">',
  'Introduction</a>',
  '<a class=nav href="booleans.html">',
  'Basic logic through pictures</a>',
  '<a class=nav href="real-numbers.html">',
  'Working with real numbers',
  '<a class=nav href="proofbuilder.html">',
  'Interactive proof builder</a>',
  '<a class=nav href="http://code.google.com/p/prooftoys/wiki/">',
  'Additional documentation</a>',
  '<a class=nav href="http://code.google.com/p/prooftoys">',
  'Project site</a>',
  '<a class=nav href="https://groups.google.com/d/forum/prooftoys">',
  'Discussion forum</a>',
  '<a class=nav href="http://code.google.com/p/prooftoys/source/checkout">',
  'Source code</a>',
  '<a class=nav',
  'href="http://code.google.com/p/prooftoys/issues/entry?template=Comment/suggestion">',
  'Feedback</a>',
].join('\n');

Toy.insertNav = function() {
  var nav = document.getElementById('leftNav');
  if (nav) {
    nav.innerHTML = Toy.navText;
  }
};

Toy.insertSlogans = function() {
  var slogans = ['"mathematical thinking for simple minds"'].join('\n');
  var elt = document.getElementById('slogans');
  if (elt) {
    elt.innerHTML = slogans;
  }
};


// Google analytics; the account is specific to Prooftoys.org.
// TODO: Consider running this code only when the site is prooftoys.org.

if (!location.pathname.match(/\/tests.html$/)) {
  var _gaq = _gaq || [];
  var pluginUrl = '//www.google-analytics.com/plugins/ga/inpage_linkid.js';
  _gaq.push(['_require', 'inpage_linkid', pluginUrl]);
  _gaq.push(['_setAccount', 'UA-28801147-2']);
  _gaq.push(['_trackPageview']);

  (function() {
    var ga = document.createElement('script'); ga.type = 'text/javascript';
    ga.async = true;
    ga.src = ('https:' == document.location.protocol
              ? 'https://ssl'
              : 'http://www') + '.google-analytics.com/ga.js';
    var s = document.getElementsByTagName('script')[0];
    s.parentNode.insertBefore(ga, s);
  })();
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
    /[-!<=>*/&|]+|[_^].|\bforall( |\b)|\bexists( |\b)|[a-zA-Z]+[0-9]*/g;
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
      // Variable name, not a constant, see Toy.isVariable in expr.js.
      return '<i>' + s + '</i>';
    } else {
      // It is a constant name.
      switch(s) {
      case '==>': return '&rArr;';
      case '==': return '&#x21d4;';	// Bidirectional implication
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
      case '&&':
      case 'and':
        return '&and;';
      case '||':
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
}

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

/**
 * The arguments are a child class constructor and parent class
 * constructor; both should be functions.  Makes the child a
 * subclass of the parent, making the parent's prototype be
 * the prototype for the child's prototype and instances of the
 * child be instances of the parent class.
 */
Toy.extends = function(child, parent) {
  if (typeof child === 'function' && typeof parent === 'function') {
    child.prototype = Object.create(parent.prototype);
  } else {
    throw new Error('Toy.extends requires functions as arguments.');
  }
};

// Make ".toString()" accessible as ".str" for debugger interaction.
Object.defineProperty(Object.prototype,
                      'str',
                      {get: function() { return this.toString(); }});
