// Copyright 2011, 2012, 2013, 2014, 2015 Crispin Perdue.
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
  var prefix = src.replace(/boilerplate.js$/, '');

  function write(html) {
    document.write(html);
  }

  function getScript(name) {
    document.write('<script src="' + prefix + name + '"></script>\n');
  }

  // Include jQuery in all cases.
  getScript('../lib/jquery-1.10.2.js');

  // getScript('../lib/jquery.tooltipster.js');

  // qTip2 tooltips
  var qtip = 'http://cdn.jsdelivr.net/qtip2/2.2.1/';
  write('<link rel="stylesheet" href="' + qtip + 'jquery.qtip.css">')
  write('<script src="' + qtip + 'jquery.qtip.js"></script>');

  write('<link rel="stylesheet" href="../css/logic.css">');
  
  // write('<link rel="stylesheet" href="../css/tooltipster-light.css">');
  // write('<link rel="stylesheet" href="../css/tooltipster.css">');
  write('<link rel="stylesheet" href="https://maxcdn.bootstrapcdn.com/font-awesome/4.4.0/css/font-awesome.min.css">');
  if (!window.noProofScripts) {
    getScript('util.js');
    getScript('prelim.js');
    getScript('expr.js');
    getScript('xutil.js');
    getScript('step-editor.js');
    getScript('../jsc/rendering.js');
    getScript('theorems.js');
    // Support Google Plus stuff in particular.
    document.write('<script src="https://apis.google.com/js/platform.js">\n' +
                   '{parsetags: "explicit"}\n' +
                   '</script>\n');
  }
})();

// Create the tooltips only when document ready ... and settled (?)
window.setTimeout(function () {
    // Uncomment this line for a simple test.
    // $('b').attr('title', 'Bold asdf asdf asdf asdf asdf asdf ads ff');
    var options = {
      position: {my: 'top left', at: 'bottom center'},
      // This could be attractive, but does not work in combo with others.
      // position: {target: 'mouse'},
      overwrite: false, // Don't overwrite tooltips already bound
      show: {
        delay: 1000,
        event: 'mouseenter',  // Or perhaps mouseover in some cases.
        ready: true // Show immediately - important!
      }
    };
    // On need convert any nonempty title to a qTips.  This enables
    // qTip for existing elements and also ones dynamically created.
    $('body').on('mouseenter', '[title!=""]', function (event) {
        $(this).qtip(options);
      });
    console.log('Tooltips established');
  }, 1000);

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
  'Working with real numbers',
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
  var slogans = ['"Power tools for your math mind"'].join('\n');
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
      // Variable name, not a constant, see Toy.isVariableName in expr.js.
      return '<i>' + s + '</i>';
    } else {
      // It is a constant name.
      switch(s) {
      case '=>': return '&rArr;';
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
 * constructor (or null); both should be functions.  If the parent is
 * given, makes the child a subclass of the parent, making the
 * parent's prototype be the prototype for the child's prototype and
 * instances of the child be instances of the parent class.
 *
 * This adds to the child constructor a property "methods", so that
 * MyConstructor.addMethods(properties) adds the properties to its
 * prototype.
 *
 * It adds a setter property "$" that does the same thing as
 * "methods".  This is semantically strange, but works well with the
 * Emacs indenter for Java mode, unlike the alternatives, and makes
 * calls on the methods look nice in Chrome debugger stack traces.
 */
Toy.extends = function(constructor, parent) {
  if (typeof constructor === 'function' && typeof parent === 'function') {
    constructor.prototype = Object.create(parent.prototype);
  } else if (typeof constructor === 'function' && parent == null) {
    // Do nothing.
  } else {
    throw new Error('Toy.extends requires functions as arguments.');
  }
  constructor.addMethods = function(properties) {
    $.extend(constructor.prototype, properties);
  };
  
};

// Global "str" function is useful for converting arbitrary objects
// to strings.
function str(x) {
  if (x.toString == Object.prototype.toString) {
    return Toy.debugString(x);
  } else {
    return x.toString();
  }
}
// Make str function accessible as ".str" for debugger interaction.
Object.defineProperty(Object.prototype,
                      'str',
                      {get: function() { return str(this); }});
