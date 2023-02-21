// Copyright Crispin Perdue.  All rights reserved.

'use strict';

////
//// GENERAL UTILITIES -- self-contained
////
//// All of these utilities are generic, not specific to Prooftoys or
//// theorem-proving.
////

// We avoid changes to the global environment except through namespace
// "Toy".
window.Toy = window.Toy || {};

// Alternative to jQuery $(fn).  Used by our own "$" function above.
Toy.onReady = function(fn) {
  if (document.readyState === 'loading') {  // Loading hasn't finished yet
    document.addEventListener('DOMContentLoaded', fn);
  } else {  // DOMContentLoaded has already fired
    fn();
  }
};

/**
 * Version of the jQuery $ function that type checks its input.
 * Overrides the definition from jQuery.
 */
window.$ = function(x) {
  // Assign to window.$ to ensure Toy.onReady is ready first. (!)
  // I think it is a scoping issue.
  if (arguments.length > 1) {
    return jQuery.apply(null, arguments);
  } else if (typeof x === 'function') {
    return Toy.onReady(x);
  } else if (typeof x === 'string' ||
                          x.nodeType ||
             x === window ||
             x instanceof jQuery) {
    return jQuery(x);
  } else {
    throw new Error('Not a DOM node: ' + x);
  }
}
jQuery.extend($, jQuery);


(function() {

// This ensures that all of our scripts can refer to _paq even in
// strict mode, and even if Matomo support is not loaded.  If Matomo
// loads later, it will set up _paq when it loads because it checks
// whether (typeof _paq != 'object').
if (!window._paq) {
  window._paq = undefined;
}

// TODO: Consider removing dependencies here on jQuery.
// They look questionable anyway.

//// General use

// TODO: Someday in the distant future, capture and analyze
// exception reports from user's browsers, and use that as
// a realistic basis for warning the user.  

// These browsers are known to be incompatible with Prooftoys.
Toy.incompatible = !!navigator.userAgent.match(/ MSIE /);

// These browsers, if recent enough, should be compatiable
// with Prooftoys.
Toy.compatible = !!navigator.userAgent.match(/(Chrome|Firefox|Safari)[/]/);

/**
 * Track an event with Matomo.  Truthy return value iff _paq is
 * initialized.  Needs an action possibly followed by a string
 * and possibly a number.
 */
Toy.trackAppEvent = function(action, ...more) {
  _paq && _paq.push(['trackEvent', 'App', action, ...more]);
  console.log('App event:', action, ...more);
  return !!_paq;
};

/**
 * Enable/disable Matomo Heatmap sesssion recording.
 * also stores the target state in Toy:uxOK.
 */
Toy.setSessionRecording = function(on) {
  localStorage.setItem('Toy:uxOK', on ? 'true' : 'false');
  _paq && _paq.push(['HeatmapSessionRecording::' +
                     (on ? 'enable' : 'disable')]);
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
 *
 * Obsolete.
 */
Toy.extends = function(constructor, parent) {
  if (typeof constructor === 'function' && typeof parent === 'function') {
    // Set up the prototype for the child class.
    // Instances will see this as their constructor.
    constructor.prototype = Object.create(parent.prototype, {
        constructor: {value: constructor}
      });
  } else if (typeof constructor === 'function' && parent == null) {
    // Do nothing.
  } else {
    abort('Toy.extends requires functions as arguments.');
  }
  constructor.addMethods = function(properties) {
    jQuery.extend(constructor.prototype, properties);
  };
};

/**
 * Adds some methods / properties to a class given the constructor.
 */
function addMethods(constructor, properties) {
  Object.assign(constructor.prototype, properties);
}

/**
 * Converts a singleton jQuery object to its DOM node,
 * checking carefully that it is a jQuery singleton.
 */
function dom($node) {
  if ($node instanceof jQuery) {
    if ($node.length === 0) {
      abort('No element');
    } else if ($node.length === 1) {
      return $node[0];
    } else {
      abort('Multiple elements: ' + $node);
    }
  } else {
    abort('Not a jQuery object: ' + $node);
  }
}

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


//// Property access

var ownProperty = Object.prototype.hasOwnProperty;

/**
 * Version of hasOwnProperty that is not accessed through the
 * prototype chain, so it works even if the object has a
 * "hasOwnProperty" property.
 * 
 */
function hasOwn(thing, name) {
  return ownProperty.call(thing, name);
};

/**
 * Gets the named property if it is an own property, otherwise
 * returns "undefined".
 */
function getOwn(thing, name) {
  return (hasOwn(thing, name) ? thing[name] : undefined);
};

/**
 * Returns an object with no prototype, having the own properties
 * of the input object as its properties.
 */
function ownProperties(object) {
  // If it has no prototype just return it.
  if (Object.getPrototypeOf(object) === null) {
    return object;
  }
  var result = Object.create(null);
  Object.getOwnPropertyNames(object).forEach(function(name) {
      result[name] = object[name];
    });
  return result;
}

/**
 * Converts an object/map into a Map from own property names to their
 * values.
 */
function asMap(object) {
  const result = new Map();
  Object.getOwnPropertyNames(object).forEach(function(name) {
      result.set(name, object[name]);
  });
  return result;
}

/**
 * Builds and returns an object with no prototype and properties taken
 * from the arguments, an alternating sequence of string keys and
 * values.  The argument list length must be even.
 */
function object0(_args) {
  var result = Object.create(null);
  var nargs = arguments.length;
  if (nargs % 2) {
    abort('object0 bad arguments list');
  }
  for (var i = 0; i < nargs; i += 2) {
    result[arguments[i]] = arguments[i + 1];
  }
  return result;
}

/**
 * Removes from the first map (plain object) all entries having keys
 * enumerable in the second map
 */
function removeAll(map1, map2) {
  for (var k in map2) {
    delete map1[k];
  }
}

/**
 * Removes from the first map (plain object) all entries that are not
 * "own" properties of the second map, keeping only entries for keys
 * that appear in both.
 */
function removeExcept(map1, map2) {
  for (var k in map1) {
    if (!hasOwn(map2, k)) {
      delete map1[k];
    }
  }
}

function isIterable (value) {
  // Note that Object is the identity function if value is an Object.
  return Symbol.iterator in Object(value);
}

//// JavaScript Sets

/**
 * Coerces the given plain object to a Set, or if it is a Set, just
 * returns it.  Accepts any Iterable as input, or a plain object,
 * converted to the set of its keys with Object.keys, or a Set.
 */
function asSet(object) {
  return (object instanceof Set
          ? object
          : object.constructor === Object
          ? new Set(Object.keys(object))
          : isIterable(object)
          ? new Set(object)
          : abort('Not coercible to a Set: {1}', object));
}

/**
 * Returns a new Set containing all the elements of each of its zero
 * or more arguments, coerced to Sets with asSet.
 */
function union(...args) {
  const result = new Set();
  args.forEach(setLike => asSet(setLike).forEach(x => result.add(x)));
  return result;
}

/**
 * Returns a new Set containing all values that are elements of each
 * of its arguments, each coerced to a Set with asSet.
 */
function intersection(arg1, ...rest) {
  const result = union(arg1);
  const sets = rest.map(asSet);
  result.forEach(x => {
    for (const set of sets) {
      if (!set.has(x)) {
        result.delete(x);
        return;
      }
    }
  });
  return result;
}

/**
 * Returns the items in the first argument that are not also
 * in the second argument, taking each as a set.
 */
function setDiff(big_arg, small_arg) {
  const result = union(big_arg);
  const small = asSet(small_arg);
  result.forEach(x => { if (small.has(x)) { result.delete(x); }});
  return result;
}

/**
 * Returns true iff the second argument contains every element of the
 * first argument, otherwise false, taking each as a Set.
 */
function isSubset(arg1, arg2) {
  const small = asSet(arg1);
  const big = asSet(arg2);
  if (small.size > big.size) {
    return false;
  }
  for (const v of small) {
    if (!big.has(v)) {
      return false;
    }
  }
  return true;
}

/**
 * True if both arguments are sets and each "has"
 * the same elements.
 */
function equalSets(arg1, arg2) {
  assert(arg1 instanceof Set, 'Not a Set: {1}', arg1);
  assert(arg2 instanceof Set, 'Not a Set: {1}', arg2);
  if (arg1.size !== arg2.size) {
    return false;
  }
  for (const v of arg1) {
    if (!arg2.has(v)) {
      return false;
    }
  }
  return true
}


//// Stricter property access

/**
 * Creates a proxy for the given object that allows no access to
 * properties; no getting, setting, deleting, or defining properties,
 * and no method calls.  Only <proxy>.$locked$ is available, which
 * retrieves the locked object.
 *
 * The result of (obj instanceof Error) is true for these objects.
 * 
 * Useful for constructing "error objects" that can be returned in
 * error situations, that resist most uses as a normally returned
 * object.
 */
function locked(obj) {
  const toss = () => { abort('Locked'); };
  const handler = {
    get: function(target, key, receiver) {
      if (key === '$locked$') {
        return obj;
      } else if (key === 'toString') {
        return target.toString.bind(target);
      } else if (key === Symbol.toPrimitive) {
        return function(hint) { return target.toString(); }.bind(target);
      } else {
        toss();
      }
    },
    set: toss,
    defineProperty: toss,
    deleteProperty: toss
  };
  return new Proxy(obj, handler);
}

/**
 * Returns the locked object, or if not locked, the object
 * you passed in, which cannot be null or undefined.
 */
function unlock(obj) {
  return obj.$locked$ || obj;
}

/*
 * Constructs and returns a proxy that aborts with a TypeError in case
 * of access to a nonexistent object property; or if the object given
 * is an Error, aborts with that Error.
 *
 * Provides a "self" property that returns the wrapped object.
 * So you can use the idiom x.self || x to unwrap the thing
 * if it is wrapped.
 *
 * TODO: Probably doesn't support calling methods in Safari, where
 *   method calls need additional support, returning a function with
 *   obj "baked in".  The magic for that is fairly black in Chrome.
 *   Fortunately we use this for Error objects and it's fine for that.
 *   See "locked" above for code that should work in Safari.
 */ 
function strict(obj) {
  let handler = {
    get: function(obj, prop) {
      if (prop == 'self') {
        return obj;
      } else if (prop in obj || typeof prop === 'symbol') {
        return obj[prop];
      } else {
        Toy.abort(obj instanceof Error
                  ? obj
                  : new TypeError('No property ' + prop));
      }
    }
  };
  return new Proxy(obj, handler);
}

/**
 * Returns a truthy value if any of the arguments is a LogicError.
 */
function errant(...values) {
  return values.some(x => x instanceof Error);
}

////
//// Math calculation

// JavaScript is defined to use IEEE 64-bit floating point in "round
// to nearest" mode.  2**53 is confusable with 2**53 + 1, so this is
// the greatest integer value we "allow".
var MAX_INT = Math.pow(2, 53) - 1;

/**
 * Polyfill for the new standard Math.sign.
 */
Math.sign = Math.sign || function(x) {
  x = +x; // convert to a number
  if (x === 0 || isNaN(x)) {
    return x;
  }
  return x > 0 ? 1 : -1;
}

/**
 * Polyfill for the new standard Math.trunc.
 */
Math.trunc = Math.trunc || function(x) {
  return x < 0 ? Math.ceil(x) : Math.floor(x);
}

/**
 * Knuth-style div defined by the floor of the quotient.
 * Always yields an integer.
 */
function div(n, divisor) {
  return Math.floor(n / divisor);
}

/**
 * Knuth-style modulus, where a nonzero result always has
 * the sign of the divisor.  Obeys the rule that
 * b * div(a, b) + mod(a, b) = a.
 */
function mod(n, divisor) {
  return n - divisor * div(n, divisor);
}

/**
 * Returns the GCD of two positive integers using Euclid's algorithm;
 * actually the truncation of the absolute values of any two numbers,
 * except if either number's absolute value is less than 1, returns 0.
 * For correct results supply inputs <= MAX_INT.
 */
function gcd(x, y) {
  var x1 = Math.trunc(Math.abs(x));
  var y1 = Math.trunc(Math.abs(y));
  var a = Math.max(x1, y1);
  var b = Math.min(x1, y1);
  if (b < 1) {
    return 0;
  }
  while (true) {
    var r = a % b;
    if (r === 0) {
      return b;
    }
    a = b;
    b = r;
  }
}

/**
 * Returns the LCM of two integers.  This always returns a positive
 * value regardless of their signs.
 */
function lcm(x, y) {
  return Math.abs(x * y) / gcd(x, y);
}

/**
 * Returns the "next prime divisor" of x and y, being the smallest
 * prime number among the result of getPrimes that is greater than n
 * and exactly divides both x and y.  Returns null if none is found.
 * This provides a naive means for finding successive common divisors
 * and eventually finding a GCD and/or reducing a fraction to lowest
 * terms.
 */
function npd(x, y, n) {
  var xFactor = nextPrimeFactor(x, n);
  var yFactor = nextPrimeFactor(y, n);
  // This is the largest number that need by considered as a factor
  // of both x and y.
  var max = Math.min(Math.abs(x), Math.abs(y));
  while (xFactor && yFactor &&
         xFactor <= max && yFactor <= max) {
    if (xFactor === yFactor) {
      return xFactor;
    }
    // At this point xFactor !== yFactor.
    if (xFactor < yFactor) {
      xFactor = nextPrimeFactor(x, xFactor);
    } else {
      yFactor = nextPrimeFactor(y, yFactor);
    }
  }
  return null;
}

// Array of prime numbers up to 32000.
var primes = [];

/**
 * Returns an array of all prime numbers up to 32000.  This is enough
 * to support factoring of any number less than 10**9.
 */
function getPrimes() {
  "use strict";
  if (primes.length === 0) {
    primes.push(2);
    // Limit of 32000 guarantees ability to factor any natural number
    // less than 1e9 (a billion).
    for (var x = 3; x < 32000; x += 2) {
      var isPrime = true;
      var max = Math.sqrt(x);
      for (var i = 0; ; i++) {
        var y = primes[i];
        if (y > max) {
          break;
        }
        if (x % y === 0) {
          isPrime = false;
          break;
        }
      }
      if (isPrime) {
        primes.push(x);
      }
    }
  }
  return primes;
}

/**
 * Returns the least prime number among the result of getPrimes that
 * is greater than "last" and a factor of x, possibly x itself.
 * Returns null if there is none.
 */
function nextPrimeFactor(x, last) {
  var abs = Math.abs(x);
  var primes = getPrimes();
  for (var i = 0; i < primes.length; i++) {
    var p = primes[i];
    if (p > last && abs >= p && x % p === 0) {
      return p;
    }
  }
  return null;
}

/**
 * Returns an array with the prime factors of the given number.
 * Result is an empty array if the input is not a positive integer, or
 * does not have prime factors (e.g. -1, 0), or the function finds no
 * prime factor within its search range (up to approximately the
 * square root of a billion).
 */
function primeFactors(n) {
  const result = [];
  if (Number.isInteger(n) && n > 0) {
    var p = 0;
    while (p = nextPrimeFactor(n, p)) {
      while (n % p == 0) {
        result.push(p);
        n = n / p;
      }
    }
  }
  return result;
}

//// Assertions, error reporting and debugging

/**
 * Calls the debugger, and when continued, returns the value passed to
 * it.  Useful for debugging values of expressions in arbitrary
 * contexts including expressions in return statements.
 */
function debug(value) {
  console.log('Value:', value);
  if (value) {
    console.log(' =', value.toString());
  }
  debugger;
  return value;
}

/**
 * Checks for Error values.  Calls the function with the error
 * if it is an Error, otherwise just returns the value.
 */
function check(v, f = Toy.abort) {
  return v instanceof Error ? f(v) : v;
}

/**
 * For debugging: Logs all facts containing the given pattern of
 * operator characters in the given order.  Operates by "squishing"
 * the keys of _factsByKey into just the occurrences of the characters
 * +, -, *, /, =, >, <, !, and checking for occurrences of the given
 * pattern string among these squished representations of the facts.
 */
function factSquish(pattern) {
  return (Array.from(Toy._factsByKey.keys())
          .map(k => [k, k.replace(/[^-+*/=!<>]/g, '')])
          .filter(pair => pair[1].includes(pattern))
          .forEach(pair => console.log(pair[0])));
}

/**
 * Asserts that the condition is true, throwing an exception if it is
 * not.  The message may be either a string or a function of no
 * arguments that returns something that can be logged.  If the
 * optional step is supplied it should be the most recent available
 * completed proof step.
 *
 * If the (optional) message is a string, it may be a format string,
 * and all arguments following it are accessible as {1}, {2}, and so
 * on.
 */
function assertTrue(condition, message, ...args) {
  if (!condition) {
    var step;
    if (typeof message === 'function') {
      abort( ...message(args));
    } else {
      message = message || 'Assertion failure';
      abort({isAssert: true}, message, ...args);
    }
  }
}

// Use the application's assertTrue function for assertions.
var assert = assertTrue;

/**
 * Returns a string showing the top-level properties
 * of an object, and their values.  If "specials" is
 * given, it should be a map from key name to a function
 * for presenting the value of any key with that name.
 */
function debugString(o, specials) {
  if (o === null) {
    return 'null';
  }
  if (o === undefined) {
    return 'undefined';
  }
  if (Array.isArray(o)) {
    var result = [];
    for (var i = 0; i < o.length; i++) {
      result.push(debugString(o[i]));
    }
    return '[' + result.join(', ') + ']';
  }
  if ([Map, Set].some(typ => o instanceof typ)) {
    try {
      const aa = Array.from(o);
      return '(' + o.constructor.name + ')' + debugString(aa);
    } catch(e) {}
  }
  if (o.constructor !== Object &&
      o.toString && typeof o.toString === "function") {
    if (o instanceof Toy.Expr && o.isProved()) {
      return '|- ' + o.toString();
    } else {
      return o.toString();
    }
  }
  if (typeof o == 'object') {
    var result = '{';
    var keys = Object.getOwnPropertyNames(o);
    keys.sort();
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i];
      if (result.length > 1) {
        result += ', ';
      }
      result += key + ': ';
      var value = o[key];
      // Now add display of the value for the key:
      var f = specials && specials[key];
      if (f) {
        result += f(value);
      } else if (typeof value == 'string') {
        result += '"' + o[key] + '"';
      } else if (Array.isArray(value)) {
        // Array-like value.
        vString = o[key].toString();
        if (vString.length > 40) {
          result += '[\n';
          for (var i = 0; i < value.length; i++) {
            result += value[i] + '\n';
          }
          result += ']\n';
        } else {
          result += '[' + o[key] + ']';
        }
      } else {
        result += '' + o[key];
      }
    }
    return result + '}';
  } else {
    return '' + o;
  }
}

Toy.alert = function(message) {
  if (Toy.testing) {
    console.error('Alert: ' + message);
  } else {
    window.alert(message);
  }
}

//// Data structure operations

/**
 * Is the given object empty, i.e. has it any enumerable properties?
 */
function isEmpty(o) {
  for (var key in o) {
    return false;
  }
  return true;
}

/**
 * Returns the number of enumerable properties possessed by the object.
 */
function mapSize(o) {
  var n = 0;
  for (var key in o) {
    n++;
  }
  return n;
}

/**
 * Configure the given object with the given property descriptors.
 * This is like Object.defineProperties, except key values that are
 * not specifically of type Object are treated as plain values and
 * not made writable, enumerable, or configurable.
 */
function configure(object, properties) {
  var define = Object.defineProperty;
  for (var key in properties) {
    var value = properties[key];
    if (typeof value === 'object' && value.constructor === Object) {
      define(object, key, value);
    } else {
      define(object, key, {value: value});
    }
  }
  return object;
}

/**
 * True iff the arrays are the same length and elements are ==
 * at each index.
 */
Array.equals = function(a1, a2) {
  // Optimize identity check.
  if (a1 === a2) {
    return true;
  }
  if (a1.length != a2.length) {
    return false;
  }
  for (var i = 0; i < a1.length; i++) {
    if (a1[i] != a2[i]) {
      return false;
    }
  }
  return true;
};

/**
 * Calls the given function on each element of the array, passing it
 * the element, the index, and the array.  If on any iteration the
 * function returns any value other than undefined, immediately
 * returns that value, otherwise the value is undefined.  Remembers
 * the array length at the start and uses that value throughout.
 */
function each(array, fn) {
  var len = array.length;
  assert(typeof len === 'number', 
         'Not an array: {1}', array);
  for (var i = 0; i < len; i++) {
    var result = fn(array[i], i, array);
    if (result !== undefined) {
      return result;
    }
  }
}

/**
 * Returns a function that access the value resulting from a call to
 * fn.  On its first call the returned "memo function" calls fn and
 * remembers the value.  Subsequent calls return the remembered value.
 *
 * The result has a property "done" that has the value true iff
 * it has been called at least once.
 */
function memo(fn) {
  var value;
  var memoFn = function() {
    if (memoFn.done) {
      return value;
    } else {
      value = fn();
      // If fn aborts, consider it not done.
      memoFn.done = true;
      return value;
    }
  };
  memoFn.done = false;
  return memoFn;
}

/**
 * Returns a string derived from the format string and the object by
 * replacing occurrences of {<identifier>} in the format string by the
 * value of that property of the object.
 *
 * Alternatively, supply extra non-Object arguments and access them
 * as {1}, {2}, etc..  This presumably is more efficient.
 */
function format(fmt, map_arg) {
  var map = (map_arg && map_arg.constructor === Object)
    ? map_arg
    : arguments;
  return fmt.replace(/\{[$_a-zA-Z0-9]*?\}/g, function(matched) {
      return map[matched.slice(1, -1)];
    });
}

/**
 * Returns a string based on the given format string, with
 * sequences of the form {{<text>}} replaced by the result
 * of "eval"ing 'Toy.' + <text> (at top level).
 */
function interpolate(fmt) {
  "use strict";
  return fmt.replace(/\{\{.*?\}\}/g, function(matched) {
      return eval('Toy.' + matched.slice(2, -2));
    });
}

/**
 * If text begins and ends with left and right parens, trims them off.
 */
function trimParens(text) {
  return text.replace(/^\((.*)\)$/, '$1');
}

/**
 * Sort a map (object), returning a list of objects with key and value
 * properties.  The comparator should accept two plain objects with
 * key and value properties, returning numbers as appropriate to their
 * desired ordering.
 */
function sortMap(object, comparator) {
  var list = [];
  for (var key in object) {
    list.push({key: key, value: object[key]});
  }
  return list.sort(comparator);
}

//// Control flow

/**
 * Unconditionally throws an Error (used by assert).  Convenient, and
 * works properly with catchAborts.  If the first argument is an Error,
 * aborts (throws) with that Error object.  If a string, treats the
 * string as a "format" template and passes it with any addditional
 * arguments to Toy.format.
 *
 * If the first argument is not an Error or string, it is treated as a
 * plain object with properties controlling details of the abort:
 *
 *   with: value is a map of properties to attach to the Error object.
 *
 * In this case the remaining arguments then are as for a call without
 * options.
 */
function abort(msg, ...args) {
  // TODO: Interpret options??
  function _abort(options, msg, ...args) {
    const e = new Error(Toy.format(msg, ...args));
    let step;
    // Find a step argument if there is one.
    for (var i = 0; i < args.length; i++) {
      var arg = args[i];
      if (Toy.isProved(arg)) {
        // TODO: Handle multiple "step" arguments.
        step = arg;
        break;
      }
    }
    e.step = step;
    Toy.thrown = e;
    throw e;
  }
  if (msg instanceof Error) {
    const error = msg;
    Toy.thrown = error;
    throw error;
  } else if (typeof msg === 'string') {
    _abort({}, msg, ...args);
  } else {
    _abort(...arguments);
  }
}

// In case of uncaught exceptions, reset state to indicate that no
// abort is in progress.  This listener is pretty innocuous, so we
// install it early.
window.addEventListener('error', event => {
  Toy.exitTarget = Toy.exitValue = Toy.thrown = undefined;
});

/**
 * Create and return an error using a template message and
 * arguments.  If a plain object is passed instead of a template
 * string, treat that as options preceding the other arguments.
 * Also accepts an initial "options" argument, a plain object.
 */
function error(options, msg, ...args) {
  if (typeof options === 'string') {
    return error({}, options, msg, ...args);
  } else {
    const e = new Error(Toy.format(msg, ...args));
    const props = 'with' in options ? options.with : {};
    Object.assign(e, props);
    // I think this is intended to support error chaining.
    if ('from' in options) {
      e.from = options.from;
    }
    return e;
  }
}

/**
 * Returns a string indicating the invocation point of
 * the function calling this.
 */
function invoker(n = 0) {
  const stack = new Error().stack.split('\n');
  let place = stack[n + 2];
  if (place.match(/andThen/)) {
    place = stack[n + 3];
  }
  return place;
}

/**
 * Create and return a "strict" error using a template message and
 * arguments.  If a plain object is passed instead of a template
 * string, treat that as options preceding the other arguments.
 *
 * TODO: Rename as "strictError".
 */
function newError(...args) {
  return strict(error(...args));
}

/**
 * Designed to be called with an arrow function as its argument, one
 * with one or more default parameters, as in:
 *
 * bind((y=complexComputation()) => { console.log(y); return y; }).
 * This way it serves much like a "let expression" in languages such
 * as Lisp or ML.
 *
 * This calls its function argument, passing it no arguments, and
 * returns the function's value.
 */
const bind = f => f();

// Calls the function with no arguments in a context where the given
// property of Toy has the given value and returns its value if it
// returns at all.  Guarantees restoration of the old value on exit
// from the function.  If the property was not previously present,
// adds it, restoring it afterward to undefined.
function rebind(name, value, fn) {
  assert(typeof name === 'string',
         'Property name must be a string: {1}', name);
  try {
    var oldValue = Toy[name];
    Toy[name] = value;
    return fn();
  } finally {
    Toy[name] = oldValue;
  }
}

//// Exit target information.

// A stack of "exit target" objects currently available for use.
// Entry to withExit pushes one onto the stack, and exit from it
// pops it off.
let activeTargets = [];

// Exit object (function) identifying the stack level we want to
// unwind to.
let exitTarget = null;

// Value to return from the exit.
let exitValue = undefined;

// A counter for debugging, helps the developer distinguish different
// targets.
let targetID = 1;

// Unwind the stack (for exits). This is not an error situation, so
// you may want to tell the debugger to "Never Pause" here:
function unwind() {
  throw undefined;
}

/**
 * Starts a computation that can be aborted by a call to an exit
 * function.  Calls the given function, passing it an exit function.
 * During the computation, if the exit function is called, withExit
 * returns the value passed to the exit function.  If the exit
 * function is called after completion of the call to "fn", the result
 * is an assertion failure.  This is a limited form of
 * call-with-current-continuation.
 */
function withExit(fn) {
  const id = targetID++;
  const exitFn = value => {
    // If the exit will fail, notice it before unwinding the stack.
    assert(activeTargets.includes(exitFn),
           '{1} is not active', exitFn);
    // Store this function to identify where to stop unwinding.
    exitTarget = exitFn;
    // Store the value in a global and start unwinding the stack.
    exitValue = value;
    unwind();
  };
  // For debugging.
  exitFn.toString = () => 'Exit function ' + id;

  // There is an entry in activeTargets for each invocation of
  // withExit currently in progress.
  activeTargets.push(exitFn);
  try {
    return fn(exitFn);
  } finally {
    activeTargets.pop();
    if (exitTarget === exitFn) {
      // The exit created here is the "target", so return the
      // requested value and stop unwinding the stack.
      const v = exitValue;
      exitTarget = exitValue = undefined;
      return v;
    }
  }
}

/**
 * Stops stack unwinding from any abort during the execution of the
 * given fn.  This calls fn, passing no arguments, and returning the
 * thrown value iff the function throws, except if the thrown value is
 * falsy, e.g. undefined, returns true.  This catches aborts, but not
 * exits.  If the function returns normally this returns false.
 *
 * This design has an advantage over passing a "catcher" function in
 * that the actions here can do local flow of control actions such as
 * "return" or "break" right in the block.  For example this can be
 * used in a form such as if (catchAborts(...)) { <actions> }, where
 * the actions execute in case of an abort.
 */
function catchAborts(fn) {
  let success = false;
  // For good measure:
  Toy.thrown = null;
  try {
    fn();
    success = true;
  } finally {
    if (success) {
      return false;
    } else if (exitTarget) {
      // An exit is in progress, not an abort, so continue unwinding
      // the stack.
      unwind();
    } else {
      return Toy.thrown || true;
    }
  }
}

/**
 * Truthy iff x is nullish or an Error object.  Use this to
 * test the results of inference steps.
 */
function isError(x) {
  return x == null || x instanceof Error;
}

/**
 * Call the given function with the given arguments, returning the
 * undefined value if the function aborts, else the value returned
 * from the function call.  Does not interfere with exitFrom
 * and withExit.
 *
 * Intended for enforcing planned control flow even when unknown
 * problems may occur.  For recovery from specific problems consider
 * using dynamically bound recovery functions.
 */
function normalReturn(fn, ...args) {
  let normalValue;
  if (catchAborts(() => normalValue = fn.apply(undefined, args))) {
    return undefined;
  } else {
    return normalValue;
  }
}

/**
 * Returns the value of calling the given function with the given
 * arguments, unless a throw occurs during its execution.  In that
 * case returns the error.  This does not interfere with exits, i.e.
 * continues the unwinding process.
 *
 * By using "catch" internally, this suppresses debugging when the
 * developer tools are open, so this is intended for catching errors
 * that are expected as part of normal operation.
 */
function catching(fn, ...args) {
  try {
    return fn.apply(undefined, args);
  } catch(e) {
    if (exitTarget) {
      unwind();
    } else {
      return e;
    }
  }
}


//// NestedTimer -- timer that excludes time in other timers

// Stack of active NestedTimers.
const _timers = [];

function NestedTimer(name) {
  this.name = name;
  this.elsewhere = 0;
}

NestedTimer.prototype = {

  start: function() {
    _timers.push(this);
    this.elsewhere = Date.now();
  },

  /*
   * Ends the timer and returns its time in milliseconds.
   */
  end: function() {
    var now = Date.now();
    assertTrue(this == _timers[_timers.length - 1], 'Timer not nested');
    _timers.pop();
    var elapsed = now - this.elsewhere;
    if (_timers.length) {
      var prev = _timers[_timers.length - 1];
      prev.elsewhere += elapsed;
    }
    return elapsed;
  }
};


//// JSON

/**
 * JSON parse function that returns the undefined value
 * in case of an error during parsing.  Legal JSON includes
 * null, but not undefined.
 */
function jsonParse(string) {
  try {
    return JSON.parse(string);
  } catch(e) {  // OK here, only catches error from JSON.parse.
    return undefined;
  }
}

/**
 * Convert the given value to a JSON string, with an optional replacer
 * as in JSON.stringify.  Uses a "space" value of 1 for human
 * readability.
 */
function stringify(object, replacer) {
  return JSON.stringify(object, replacer, 1);
}


//// LOCAL STORAGE

// The pid distinguishes this JavaScript environment from others
// that might edit documents in local storage.
//
// This approach could result in environments with the same pid, but
// that is highly unlikely.  We could used IndexedDB generated keys to
// guarantee uniqueness.  Alternatively, Maekawa's algorithm together
// with a registry of all pid values in localStorage might be able to
// reliably generate unique pid values if desired.
//
// Currently the decimal representation of a non-negative integer less
// than 1e15.
// 
let pid = '' + Math.floor(Math.random() * 1e15);

// This facility uses localStorage as follows:
//
// All key names begin with "Toy:", to distinguish them from any keys
// potentially used by other packages loaded into the page.
//
// Within the "Toy" namespace, we have a "doc" space, a "pid" space,
// and a "ped" space, each used as a table of records.
//
// The "doc" (document) table models a trivial file system with named
// documents that can be read and written.  A valid document name is
// currently a sequence of one or more alphanumeric, space, hyphen,
// "/", ".", and/or underscore characters.
//
// A document contains an arbitrary JSON-encoded object.  The read and
// write operations work on the entire document as a single atomic
// operation.
//
// The "pid" table stores information for each pid.  For each pair of
// pid and ID of editable proof editor in that context it has the
// associated document name.  All "pid" information is removed when
// the pid's context is unloaded.
//
// The "ped" table stores persistent state per proof editor ID,
// independent of pid.  This is currently an associated document name,
// which determines the document to load when (re)visiting a page.
//
// Operations that take a document name argument (except checkDocName)
// return undefined in case the name is invalid, and some other value
// otherwise.  All such operations do nothing if the name is not
// valid.
//
// A document is held by zero or more "using" proof editors and pids.
// The document is held iff its name is the document name of an editor
// in some page whose pid other than the current one.
//

// TODO: Consider supporting event listeners for changes to documents
//   and held status of documents.


//// Documents (by name)

/**
 * Returns true or false depending on whether the given string is a
 * valid document name.  Currently one or more of alphanumeric or
 * "-./_ #".
 */
function checkDocName(name) {
  const result = name.match(/^([a-zA-Z0-9_ /.#-]+)$/);
  if (!result) {
    console.warn('Bad document name:', name);
  }
  return !!result;
}

/**
 * Returns the contents of the named document as a string of JSON
 * data, or undefined if there is no such document or the value
 * is not valid JSON.
 */
function readDoc(name) {
  if (checkDocName(name)) {
    return jsonParse(localStorage.getItem('Toy:doc:' + name));
  }
}

/**
 * Atomically replaces the content of the named document with a JSON
 * encoding of the given value, returning true.
 */
function writeDoc(name, content) {
  if (checkDocName(name)) {
    localStorage.setItem('Toy:doc:' + name, stringify(content));
    return true;
  }
}

/**
 * Removes the document with the given name, returning true unless the
 * name is invalid.
 */
function rmDoc(name) {
  if (checkDocName(name)) {
    localStorage.removeItem('Toy:doc:' + name);
    return true;
  }
}

/**
 * Returns an array of the names of all stored documents.
 */
function lsDocs() {
  const prefix = 'Toy:doc:';
  const len = prefix.length;
  const names = [];
  for (let i = 0; i < localStorage.length; i++) {
    const key = localStorage.key(i);
    if (key.startsWith(prefix)) {
      names.push(key.slice(len));
    }
  }
  return names;
}

/**
 * Developer tool that searches through all Mathtoys docs in localStorage,
 * searching for the given regex pattern in the document proof state.
 * Returns an array of names of docs containing the pattern.
 */
function grepDocs(pattern) {
  return lsDocs().filter(function(name) {
      const str = readDoc(name).proofState;
      return str.match(pattern);
    });
}

//// Proof editor state, by proofEditorId

// This is persistent state, document name per editor ID.
// Each proof editor object has a numeric ID that is unique within its
// window, based on order of creation within the window, starting
// with number 1.

// Internal function that returns a localstorage key for information
// associated with a specific proof editor at a specific URL.  Here
// "ped" is short for proof editor.
function pedKey(ed) {
  return Toy.format('Toy:ped:{1}', ed.proofEditorId);
}

/**
 * Returns stored state of the given proof editor as JSON-encoded
 * data, or undefined if there is no such proof editor or the value is
 * not valid JSON.
 */
function getSavedState(ed) {
  return jsonParse(localStorage.getItem(pedKey(ed)));
}

/**
 * Replaces the stored information about the given proof editor with a
 * JSON encoding of the given value, returning true.
 */
function saveState(ed, content) {
  localStorage.setItem(pedKey(ed), stringify(content));
}


//// PID state

// For each pair of pid and editor ID in editable state, records
// the associated document name.

// This is ephemeral state, destroyed when the relevant JS context
// is unloaded.

// TODO: Rename to noteStatus, also saveStatus, etc..
function noteState(ed, content) {
  const key = Toy.format('Toy:pid:{1}:{2}', pid, ed.proofEditorId);
  localStorage.setItem(key, stringify(content));
}

/**
 * Returns true if the named document has at least one recorded user
 * in some other pid or proof editor, otherwise false.
 */
function isDocHeldFrom(name, ped) {
  const pidPattern = /^Toy:pid:(.*?):(.*)/;
  const id = ped.proofEditorId;
  let found = false;
  let matches = 0;
  for (let i = 0; i < localStorage.length; i++) {
    const key = localStorage.key(i);
    const match = key.match(pidPattern);
    match && matches++;
    // The value can be undefined if the value is not JSON.
    const value = jsonParse(localStorage.getItem(key));
    const docName = value && value.docName;
    if (match && name === docName &&
        (pid !== match[1] || id !== match[2])) {
      found = true;
    }
  }
  console.log('Found', matches, 'pid entries');
  return found;
}

/**
 * Calls its functional arg with each key and value of the
 * localStorage object.
 */
function eachStore(fn) {
  const store = localStorage;
  for (let i = 0; i < store.length; i++) {
    const key = store.key(i);
    fn(key, store.getItem(key));
  }
}

/**
 * Removes all information about proof editors in the current context.
 */
function releaseThisPid() {
  const keys = [];
  const prefix = 'Toy:pid:' + pid + ':';
  for (let i = 0; i < localStorage.length; i++) {
    const key = localStorage.key(i);
    if (key.startsWith(prefix)) {
      keys.push(key);
    }
  }
  keys.forEach(function(k) { localStorage.removeItem(k); });
  localStorage.removeItem('Toy:beat:' + pid);
}

$(window).on('unload', releaseThisPid);


//// Benchmarking

/**
 * Call the function with no arguments "count" times, defaulting to
 * 1000.  Report the time and number of calls through the console log.
 * Use Function.bind to presupply arguments to the function.
 */
function benchmark(fn, count) {
  count = count || 1000;
  var start = Date.now();
  for (var i = 0; i < count; i++) {
    fn();
  }
  var elapsed = Date.now() - start;
  console.log(format('{1} calls in {2}ms', count, elapsed));
}


//// Custom events

// Plain object where we can hang events for completion of module
// loading.  Indicate module loaded using Toy.loaded.trigger('xutil'),
// and notice loading with e.g. Toy.loaded.on('xutil', ... ).
Toy.loaded = jQuery({});


//// ToySet

function ToySet(stringifier) {
  this.map = {};
  this.stringifier = stringifier || String;
}

var emptySet = Object.freeze(new ToySet());

/**
 * Add an element, returning this.
 */
ToySet.prototype.add = function(value) {
  this.map[this.stringifier(value)] = value;
  return this;
};

/**
 * Add all the values in the given array or ToySet to this ToySet.
 * Return this.
 */
ToySet.prototype.addAll = function(more) {
  var self = this;
  function add(value) { self.add(value); }
  if (more instanceof ToySet) {
    more.each(add);
  } else {
    more.forEach(add);
  }
  return self;
};

/**
 * Does the set contain the element (one with the same key)?
 */
ToySet.prototype.has = function(value) {
  return hasOwn(this.map, this.stringifier(value));
};

ToySet.prototype.size = function() {
  var result = 0;
  this.each(function(x) { result++; });
  return result;
};

/**
 * Applies to another collection that has an "each" method that
 * iterates over its elements, exiting in case of a defined value.
 * Returns a boolean value indicating whether this contains all the
 * elements of the other collection.
 */
ToySet.prototype.superset = function(other) {
  var self = this;
  var result = true;
  other.each(function(o) {
      if (!self.has(o)) {
        result = false;
        return false;
      }
    });
  return result;
};

/**
 * Returns true iff this and the argument set each contain all the
 * elements of the other one.
 *
 * TODO: Consider making more efficient.
 */
ToySet.prototype.equals = function(other) {
  return this.size() === other.size() && this.superset(other);
};

/**
 * Remove the element.
 */
ToySet.prototype.remove = function(value) {
  delete this.map[this.stringifier(value)];
};

/**
 * Call the given function for each element of the set, passing the
 * set element as its argument.  Use the optional thisObj as "this"
 * for the calls, or "undefined" if it is not given.  If the function
 * returns any value other than "undefined" that value becomes the
 * return value of this method, and iteration ends.
 */
ToySet.prototype.each = function(fn, thisObj) {
  var map = this.map
  for (var key in map) {
    var result = fn.call(thisObj, map[key], key);
    if (result !== undefined) {
      return result;
    }
  }
};

/**
 * Count of distinct elements.
 */
ToySet.prototype.size = function() {
  var counter = 0;
  this.each(function () { counter++; });
  return counter;
};

/**
 * Is the set empty?
 */
ToySet.prototype.isEmpty = function() {
  for (var key in this.map) {
    return false;
  }
  return true;
};

/**
 * Remove all members of this ToySet.
 */
ToySet.prototype.clear = function() {
  var map = this.map;
  for (var key in map) {
    delete map[key];
  }
};

/**
 * Returns an element of the set or undefined if the set is empty.
 */
ToySet.prototype.choose = function() {
  for (var key in this.map) {
    return this.map[key];
  }
};

/**
 * Returns an iterable (actually an array) of the values in the ToySet.
 */
ToySet.prototype.values = function() {
  var result = [];
  this.each(x => void result.push(x));
  return result;
};

ToySet.prototype.toString = function() {
  var values = this.values().map(function (x) { return x.toString(); });
  return format('{1}({2})', this.constructor.name || '', values);
};


//// ToyMap

/**
 * Arguments are a function to convert a key object to an identifying
 * string, and a default value when getting a key that is not in the
 * map.  The default default is the undefined value.
 */
function ToyMap(stringifier, dfault) {
  this.map = {};
  this.stringifier = stringifier || String;
  this.dfault = dfault;
}

/**
 * Set the value of a map element.
 */
ToyMap.prototype.set = function(key, value) {
  this.map[this.stringifier(key)] = value;
};

/**
 * Does it have an element with matching key?
 */
ToyMap.prototype.has = function(key) {
  return hasOwn(this.map, this.stringifier(key));
};

/**
 * Gets the value at a key or undefined if no such element.
 */
ToyMap.prototype.get = function(key) {
  var map = this.map;
  var k = this.stringifier(key);
  return hasOwn(map, k) ? map[k] : this.dfault;
};

/**
 * Remove any element with matching key.
 */
ToyMap.prototype.remove = function(key) {
  delete this.map[this.stringifier(key)];
};

/**
 * Iterate over the map, allowing early return.  The fn receives a
 * value and (string) key.  In any iteration where the value of the
 * function is not the undefined value, immediately returns that
 * value.
 */
ToyMap.prototype.each = function(fn, thisObj) {
  var map = this.map
  for (var key in map) {
    var result = fn.call(thisObj, map[key], key);
    if (result !== undefined) {
      return result;
    }
  }
};

/**
 * Number of distinct keys in the map.
 */
ToyMap.prototype.size = function() {
  var counter = 0;
  this.each(function () { counter++; });
  return counter;
};

/**
 * Is it empty?
 */
ToyMap.prototype.isEmpty = function() {
  for (var key in this.map) {
    return false;
  }
  return true;
};

//// Array snapshots

/**
 * Create a new "array snapshot" with a degree of protection against
 * accidental programmer modification of the array.  The values in the
 * array are intended to be accessed only through an iterator.
 */
function ArraySnap(a) {
  var self = this;
  self._arraySnap = a.concat();
  self[Symbol.iterator] = function() {
    return self._arraySnap[Symbol.iterator]();
  }
}

/**
 * Returns a new Array with all the elements of this ArraySnap.
 */
ArraySnap.prototype.copy = function() {
  return this._arraySnap.concat();
}


//// Counting and timing calls on functions.

// Map from function name to data (calls and times)
var trackingData = {};

/**
 * Return a function that calls the given one, timing and counting
 * calls on it.  Uses the name argument if given, or the function's name
 * for reporting purposes, otherwise throws an Error.
 */
function tracked(fn, opt_name) {
  var name = opt_name || fn.name;
  if (typeof fn !== 'function' || !name) {
    abort('Not a named function');
  }
  var data = trackingData[name];
  if (!data) {
    data = trackingData[name] = {calls: 0, times: 0};
  }
  return function() {
    var start = Date.now();
    try {
      return fn.apply(this, arguments);
    } finally {
      data.calls++;
      data.times += Date.now() - start;
    }
  };
}

/**
 * Replace the given property of the given object with a tracked
 * version, reporting using the property name or opt_name if
 * present.
 */
function track(object, property, opt_name) {
  var old = object[property];
  object[property] = tracked(object[property], opt_name || property);
}

// Finding and reporting different stack contexts where code runs:

Toy.callStacks = new Map();

function noticeStack(msg) {
  var stack = new Error(msg).stack;
  Toy.callStacks.set(stack, (Toy.callStacks.get(stack) || 0) + 1);
}

function showStacks() {
  const stacks = Toy.callStacks;
  for (const s of stacks.keys()) {
    const n = stacks.get(s);
    console.log('' + n + ' of ' + s);
  }
};


//// Refresher class and deferred actions

/**
 * Creates an object that will run the given function, if activated,
 * the next time the event system becomes idle.  When the function
 * runs, the Refresher becomes ready for another activation.
 */
function Refresher(fn) {
  this.fn = fn;
  this._timer = null;
  this.active = false;
}

/**
 * Activates this Refresher to run the next time the event system
 * becomes idle.
 *
 * Commonly called when an object has changed or needs to change.
 */
Refresher.prototype.activate = function() {
  var self = this;
  var fn = this.fn;
  function action() {
    self._timer = null;
    self.active = false;
    fn();
  }
  if (this._timer === null) {
    this.active = true;
    this._timer = soonDo(action);
  }
};

/**
 * Do the action as soon as the event handling system becomes idle.
 * It will run after the current initialization or event handler
 * completes.
 */
function soonDo(action) {
  return window.setTimeout(action, 0);
}

/**
 * Returns a promise that resolves to null after the given number of
 * milliseconds.
 */
function wait(millis) {
  return new Promise(function (resolve, reject) {
      setTimeout(resolve, millis);
  });
}

/**
 * Do the action as soon as possible after giving the page a chance to
 * repaint.  Sometimes Webkit needs a small delay to trigger a
 * repaint, regardless of some of the claims made on
 * stackoverflow.com.
 */
function afterRepaint(action) {
  return window.setTimeout(action, 10);
}

/**
 * Returns a promise that resolves after allowing enough time
 * for a repaint to trigger.
 */
function allowRepaint() {
  return wait(10);
}

//// Change handlers

// The functions "changed" and "onChange" support a model in which
// there are various functions that update state, whose results depend on 
// the state of objects and/or the values of specific properties of objects.
// In this model, when an object or property of an object has changed, it
// is recorded as being changed, and that status continues until the
// functions dependent on it have run.
//
// When an object or one of its properties is flagged as changed by a
// call to "changed", "onChange" marks all dependent functions as
// needing to run, and makes sure they run as soon as the system event
// loop returns to idle.  At that point, each dependent function is run
// just once, within a try-catch block.

/** Map from object to a set of event handler functions.  The handlers
 * respond to reported changes to the object by deciding whether to
 * add an action to run when the system event loop returns to idle.
 * Private.
 */
const changeHandlers = new Map();

/**
 * Reports a change to the given object, or given property of the
 * given object.  This has the effect of enqueuing all relevant
 * registered actions to run when the system event loop returns to
 * idle.  See onChange for more information.
 */
function changed(object, opt_partName) {
  const handlers = changeHandlers.get(object);
  handlers && handlers.forEach(function(handler) {
      handler(object, opt_partName);
    });
}

/**
 * Registers an action to run when a relevant change is made to a
 * given object, as reported using the "changed" function.  This takes
 * a single plain object as its argument, with properties:
 *
 * action: Arbitrary function to run in response to a change in the
 *   "source" object.
 * source: If this object is changed, the action may run in response.
 * part: A string.  If given, the action is to run in response to
 *   a change to the source object reported by the "changed" function,
 *   specifying the same property name.  If not given, the action runs
 *   in response to a change to the source object reported without
 *   specifying any property name.
 *
 * Calls to "changed" cause relevant registered actions to be enqueued
 * to run when the event loop returns to idle.  A given action
 * function only runs at most once per cycle regardless of the number
 * of relevant calls to "changed".  Each enqueued action runs within a
 * catchAborts block to ensure that all have the opportunity to run.
 */
function onChange(properties) {
  const source = properties.to;
  const part = properties.part;
  const action = properties.do;
  const existing = changeHandlers.get(source);
  const handlers = existing || new Set();
  existing || changeHandlers.set(source, handlers);
  // It does not matter that changeHandlers is a Set (rather than an
  // array), because each handler function is a distinct object.
  handlers.add(function(event, propertyName) {
      if (propertyName === part) {
        addPendingAction(action);
      }
    });
};

/**
 * A set of actions registered to run when the system event loop next
 * returns to idle.  Private.
 */
let pendingActions = new Set();

/**
 * Private.  Adds an action to pendingActions, and makes sure the
 * actions will run when the event loop returns to idle.
 */
function addPendingAction(fn) {
  if (pendingActions.size === 0) {
    soonDo(runPendingActions);
  }
  pendingActions.add(fn);
}

/**
 * Private.  Runs each pending action within a try-catch block,
 * ensuring that all have opportunity to run.
 */
function runPendingActions() {
  const actions = pendingActions;
  pendingActions = new Set();
  actions.forEach(function(fn) {
    if (Toy.catchAborts(fn)) {
      console.error('Error occurred in change handler:', e);
    }
  });
}


//// Graphics

/**
 * Create and return a DIV that renders as a right triangle pointing
 * in the given direction (left, right, up, or down), of the given
 * height and color, specified in any form acceptable to CSS.  A
 * numeric height is taken as pixels.  Do not put anything in the DIV,
 * or the effect will be ruined.
 *
 * Sets the CSS pointer-events property to 'none', but you can
 * override this if you prefer.
 */
function makeTriangle(where, height, color) {
  color = color || 'black';
  height = height || '10px';
  var topBottomProps = {
    height: 0,
    width: 0,
    borderLeftWidth: height,
    borderLeftStyle: 'solid',
    borderLeftColor: 'transparent',
    borderRightWidth: height,
    borderRightStyle: 'solid',
    borderRightColor: 'transparent',
    borderTopWidth: height,
    borderTopStyle: 'solid',
    borderTopColor: color,
    borderBottomWidth: height,
    borderBottomStyle: 'solid',
    borderBottomColor: color,
    pointerEvents: 'none'
  };
  var leftRightProps = {
    height: 0,
    width: 0,
    borderTopWidth: height,
    borderTopStyle: 'solid',
    borderTopColor: 'transparent',
    borderBottomWidth: height,
    borderBottomStyle: 'solid',
    borderBottomColor: 'transparent',
    borderLeftWidth: height,
    borderLeftStyle: 'solid',
    borderLeftColor: color,
    borderRightWidth: height,
    borderRightStyle: 'solid',
    borderRightColor: color,
    pointerEvents: 'none'
  };
  var mapping = {
    'up': topBottomProps,
    'down': topBottomProps,
    'left': leftRightProps,
    'right': leftRightProps
  };
  var properties = mapping[where];
  if (!properties) {
    abort('Triangle direction must be up, down, right, or left');
  }
  var zeroProp = {
    'up': 'borderTopWidth',
    'down': 'borderBottomWidth',
    'left': 'borderLeftWidth',
    'right': 'borderRightWidth'
  };
  properties[zeroProp[where]] = 0;
  var div = $('<div>');
  div.css(properties);
  return div[0];
}

/**
 * Supports testing of makeTriangle.
 */
function _testTriangle(where, height, color) {
  var tt = makeTriangle(where, height, color);
  $('body').prepend(tt);
};

//// Same origin policy

/**
 * Set document.domain to its parent (if possible).  This is useful
 * for enabling actions such as XHR across sudomains of the same
 * domain.  The assignment fails if the browser deems the current
 * domain "top level" such as co.uk or herokuapp.com.  Returns true
 * iff it shortens the domain, else false.
 */
function useParentOrigin() {
  const domain = document.domain;
  const a = domain.split('.');
  try {
    document.domain = a.slice(1).join('.');
  } catch(err) {  // OK here, only catches from 1 line of code.
    // Ensure it is set, even if to the same value.
    document.domain = document.domain;
    return false;
  }
  return true;
}


//// RPC with message queuing

// This section uses ES6 / ES2015 language features

/**
 * Message queue constructor for RPC communication, as with Web Worker
 * threads.  If a numeric argument and URI string are supplied, will
 * immediately create and add that many Worker threads.
 */
function MessageQueue(n, uri) {
  // Queue of messages to be sent.  Each item is a data structure with
  // properties "promise", "resolve", "reject", and "wrapper", where
  // the wrapper has a "channelType", an "id", and "data", which is
  // the message itself as enqueued.
  //
  // Of these, only the wrapper and its properties are passed to
  // worker code and only these should be referenced in client code.
  this.queue = [];
  // Map from rpc ID to message, containing messages that have been sent
  // but not yet responded to.  The items have the same structure as
  // queue elements.
  this.inProgress = new Map();
  // Set of Web Workers handling messages from this queue.
  this.workers = new ToySet();
  // Workers not currently handling a request.
  this.idleWorkers = [];

  if (arguments.length == 2) {
    for (var i = 0; i < n; i++) {
      this.addWorker(new Worker(uri));
    }
  }
}

// Will be set to the time of the first call to rpcLog.
var rpcLogStart;

/**
 * Log messages, the RPC ID, and the number of milliseconds since
 * rpcLogStart if RPC logging is turned on by setting Toy.logRpc to
 * true.
 */
function rpcLog(_args) {
  if (!Toy.logRpc) {
    return;
  }
  if (!rpcLogStart) {
    rpcLogStart = Date.now();
  }
  var a = jQuery.makeArray(arguments);
  a.push('at');
  a.push(Date.now() - rpcLogStart);
  console.log.apply(console, a);
}

MessageQueue.id = 1;

var msgMethods = {

  /**
   * Adds a worker to the pool of workers available to handle RPCs.
   */
  addWorker: function(w) {
    w.onmessage = this._handleReply.bind(this);
    this.workers.add(w);
    this.idleWorkers.unshift(w);
    this._dispatch();
  },

  /**
   * Sends a request via the queue.  Returns a specialized Promise to
   * be resolved with the result of the call.  Worker code will
   * receive this wrapped in a plain object with properties
   * "channelType" having the value "RPC", "id" a unique message ID,
   * and "data" containing the message argument.
   *
   * Standard RPC worker error responses are a plain object with
   * properties:
   *
   * type: name of Error object constructor,
   * message: error.message,
   * stack: error.stack.
   */
  enqueue: function(message) {
    var id = MessageQueue.id++;
    var wrapper = {channelType: 'RPC', id: id, data: message};
    var resolve, reject;
    var promise = makeRpcPromise(function(res, rej) {
        resolve = res;
        reject = rej;
      });
    promise.mq = this;
    promise.id = id;
    var info = {promise: promise,
                resolve: resolve,
                reject: reject,
                wrapper: wrapper};
    this.queue.push(info);
    rpcLog('Queueing RPC', id);
    this._dispatch();
    return promise;
  },

  /**
   * Internal method invoked as the onmessage handler for replies from
   * the worker.
   */
  _handleReply: function(event) {
    var wrapper = event.data;
    if (wrapper.channelType === 'RPC') {
      var message = wrapper.result;
      var id = wrapper.id;
      var info = this.inProgress.get(id);
      if (info) {
        this.inProgress.delete(id);
        this.idleWorkers.push(event.target);
        if (!info.promise.canceled) {
          if (wrapper.isError) {
            info.reject(wrapper);
          } else {
            info.resolve(wrapper);
          }
        } else {
          rpcLog('Ignoring reply to canceled RPC', id);
        }
      } else {
        console.error('RPC reply unknown ID', event);
        debugger;
      }
      this._dispatch();
    } else {
      this.handleOther(event);
    }
  },

  /**
   * Called when the MessageQueue receives a message from
   * a worker and it does not have a channelType property
   * with value "RPC".
   */
  handleOther: function(event) {
    console.warn('Unknown MessageQueue response', event);
  },

  /**
   * Called at the very start of each dispatch.  This may be
   * overridden to rearrange the lists of waiting requests and idle
   * workers if desired to change the effect of the dispatch.
   */
  schedule: function() {},

  /**
   * Private method called internally at points where it might be
   * appropriate to post another RPC call message.  If there is an
   * idle worker and a request in the queue, posts the first request
   * to the first idle worker.
   */
  _dispatch: function() {
    this.schedule();
    if (this.workers.size() === 0) {
      console.warn('No RPC workers');
    }
    if (this.idleWorkers.length && this.queue.length) {
      var worker = this.idleWorkers.shift();
      var info = this.queue.shift();
      worker.postMessage(info.wrapper);
      rpcLog('Launched RPC', info.wrapper.id);
      this.inProgress.set(info.wrapper.id, info);
    }
  }
};

Object.assign(MessageQueue.prototype, msgMethods);


/**
 * Factory function that makes a Promise specialized for use with
 * MessageQueue RPCs.
 *
 * This is not a class because subclassing of built-in objects such as
 * Promise is tricky without ES2015 subclassing.  So it just extends
 * each object individually.
 *
 * Has slots "mq" for the RPC message queue of its message, and
 * "id" for the ID of the RPC call it waits for.
 */
function makeRpcPromise(initFn) {
  var p = new Promise(initFn);
  p.mq = null;
  p.id = -1;
  p.canceled = false;
  Object.assign(p, rpcPromiseMethods);
  return p;
}

const rpcPromiseMethods = {

  /**
   * Convenience method that pushes this Promise onto the given array,
   * returning the Promise.
   */
  addTo: function(array) {
    array.push(this);
    return this;
  },

  /**
   * After the cancel method is called, this Promise will never
   * resolve or reject.  If its RPC is in a waiting queue, this
   * removes it, and if it is in progress, the response handling code
   * will ignore it.  Sets the "canceled" property to true.
   */
  cancel: function() {
    this.canceled = true;
    this.dequeue();
  },

  /**
   * Attempts to dequeue this Promise, succeeding when it is still
   * in its message queue.  In case of success the Promise will
   * never resolve or reject.  Returns boolean value, truthy for
   * success.
   */
  dequeue: function() {
    var a = this.mq.queue;
    var id = this.id;
    rpcLog('RPC dequeue request', id);
    rpcLog('Queue length =', a.length);
    for (var i = 0; i < a.length; i++) {
      rpcLog('  RPC', a[i].wrapper.id);
    }
    for (var i = 0; i < a.length; i++) {
      if (a[i].wrapper.id === id) {
        a.splice(i, 1);
        rpcLog('Dequeued RPC', id)
        return true;
      }
    }
    return false;
  }

};


/* Test code for RPC

var q = new Toy.MessageQueue(1, 'pt/js/worker.js');
var p = q.enqueue({action: 'ping'})
         .then(x => (console.log('ping', x), x))
         .catch(x => console.log('Failed', x));
var p = q.enqueue({action: 'fail'})
         .then(x => (console.log('fail?', x), x))
         .catch(x => console.log('Failed', x));
var p = q.enqueue({action: 'plus1', input: 4})
         .then(x => (console.log('Plus1', x), x))
         .catch(x => console.log('Failed', x));
*/


//// Simulated Web Worker objects

/**
 * Creates a fake Worker usable from the MessageQueue API.  Messages
 * passed to the message queue will be passed to RPC handler methods
 * as-is, without copying or encoding of any kind.
 *
 * Assign a function to the "onmessage" property to receive RPC
 * results.
 */
function FakeRpcWorker(receiver) {
  this.receiver = receiver;
  this.onmessage = null;
}

/**
 * Posts a message to this FakeRpcWorker.  This results in calling the
 * internal handler from a timer, and later a call to the FakeWorker's
 * onmessage property, passing it a faked-up event, an object that has
 * a "target" property and a "data" property with the worker's reply
 * data, but currently no other information.  The internal handler
 * function takes the place of a real Worker's onmessage handler in
 * its internal global scope.
 *
 * The internal handler function builds reply data that is a plain
 * object with properties: "channelType" with value "RPC"; "id" with
 * the same RPC call ID passed in, "result" with the
 * application-specific result value, and boolean "isError" true
 * if the result is to be considered a failure.
 *
 * Starts the worker with a short delay to promote prompt repainting.
 * The worker's reply notification is also asynchronous, but has no
 * delay on the theory that the worker will not modify the DOM.
 */
FakeRpcWorker.prototype.postMessage = function(wrapper) {
  // TODO: Give each worker a fake global scope object property,
  //   e.g. named "scope".  Separate out the handler and replier here,
  //   attaching them as the global scope onmessage event handler and
  //   postMessage function.
  var self = this;
  var receiver = self.receiver;
  // This is the fake reply event to be passed to the reply handler.
  var reply = {target: self};
  // This function does the work of a "real" onmessage handler
  // function in worker.js for messages to a worker, except this
  // receives the RPC wrapper object directly, not wrapped in an
  // event, and replies by calling the fake worker object's onmessage
  // property asynchronously.
  function workerMessageHandler() {
    if (wrapper.channelType === 'RPC') {
      // Handle (thrown) errors without catching them, so the debugger
      // can take control at the point of the error.
      function handleError(msg, url, line, col, error) {
        // Restore the old error handler here ASAP.
        window.onerror = oldHandler;
        var e = (receiver.encodeError
                 ? receiver.encodeError(error)
                 : error instanceof Error
                 ? {type: error.constructor.name,
                    message: error.message,
                    stack: error.stack}
                 : '?');
        reply.data = {channelType: 'RPC', id: id, result: e, isError: true};
        // Emulate the usual protocol for replies.
        rpcLog('Posting error reply for RPC', reply.data.id);
        window.setTimeout(replier, 0);
      }
      var oldHandler = window.onerror;
      window.onerror = handleError;
      var id = wrapper.id;
      var message = wrapper.data;
      var action = message.action;
      var actions = receiver.actions;
      if (!actions.hasOwnProperty(action)) {
        abort('Unknown RPC action', action);
      }
      var fn = actions[action].bind(receiver);
      var result = fn(message, wrapper);
      reply.data = {channelType: 'RPC', id: id, result: result,
                    isError: false};
      function replier() {
        var responder = self.onmessage;
        rpcLog('Handling RPC reply', reply.data.id);
        responder(reply);
        rpcLog('Handled RPC reply', reply.data.id);
      }
      rpcLog('Posting reply for RPC', reply.data.id);
      // The worker code should not access the DOM, so there should
      // not be reason to wait for a repaint before handling the
      // worker's reply.
      window.setTimeout(replier, 0);
      // When successful, restore the old handler immediately.
      window.onerror = oldHandler;
    } else if (receiver.handleOther) {
      receiver.handleOther(event);
    } else {
      console.warn('Unhandled message', event);
    }
  }
  // Call the handler from a timer.
  // Follow the example of Toy.afterRepaint in allowing time for
  // repaints and other more urgent activities to take priority.
  window.setTimeout(workerMessageHandler, 10);
}


/**
 * Copies a string to the clipboard. Must be called from within an 
 * event handler such as click. May return false if it failed, but
 * this is not always possible. Browser support for Chrome 43+, 
 * Firefox 42+, Safari 10+, Edge and IE 10+.
 * IE: The clipboard feature may be disabled by an administrator. By
 * default a prompt is shown the first time the clipboard is 
 * used (per session).
 *
 * From: https://stackoverflow.com/questions/400212/
 *   how-do-i-copy-to-the-clipboard-in-javascript
 */
function copyToClipboard(text) {
  if (window.clipboardData && window.clipboardData.setData) {
    // IE specific code path to prevent textarea being shown while
    // dialog is visible.
    return clipboardData.setData("Text", text); 
  } else if (document.queryCommandSupported &&
             document.queryCommandSupported("copy")) {
    var textarea = document.createElement("textarea");
    textarea.textContent = text;
    // Prevent scrolling to bottom of page in MS Edge.
    textarea.style.position = "fixed";
    document.body.appendChild(textarea);
    textarea.select();
    try {
      // Security exception may be thrown by some browsers.
      return document.execCommand("copy");
    } catch (ex) {  // OK, only catches from 1 line of code.
      console.warn("Copy to clipboard failed.", ex);
      return false;
    } finally {
      document.body.removeChild(textarea);
    }
  }
}

/**
 * Works with CSS in proofs.scss to run a node's oninsert
 * property when the node is inserted into the DOM (except
 * as display:none (?)).
 */
{
  let handler = function(event) {
    if (event.animationName == 'nodeInserted'
        && typeof event.target.oninsert == 'function') {
      event.target.oninsert();
    }
  }
  document.addEventListener('animationstart', handler, false);
}


//// PID heartbeat

/**
 * Cleans up all localStorage data associated with any pids that
 * have not issued a heartbeat by updating Toy:pid:<pid> within the
 * last 30 seconds.
 *
 * In theory the unload handler does this, but sometimes that is
 * insufficient, perhaps when using the debugger.
 */
function removeOldPidData() {
  const store = localStorage;
  const now = Date.now();
  // Both of the following map from pid to full key.
  // The pid values are all strings.
  const beatKeys = new Map();
  const statusKeys = new Map();
  // Set of string pid values with recent heartbeats.
  const currentPids = new Set();
  // Iterate over all data, recording everything pid-related
  // and particularly noting pids that have "recent" heartbeats.
  for (let i = 0; i < store.length; i++) {
    const key = store.key(i);
    const matches = key.match(/^Toy:beat:(.*)/);
    if (matches) {
      // This is a heartbeat item.  Add it to beatKeys and potentially
      // currentPids.
      const pid = matches[1];
      beatKeys.set(pid, key);
      const time = Number(store.getItem(key));
      // The number here is empirical based on Chrome / MacOS behavior
      // when tab is not visible.  Recent releases of Chrome stretch
      // the 10 second heartbeat out to ~60 seconds in non-visible
      // tabs / windows.
      if (now < time + 150_000) {
        currentPids.add(pid);
      }
    } else {
      const matches = key.match(/^Toy:pid:(.*?):/);
      if (matches) {
        // This is a pid data item; add it to statusKeys.
        const pid = matches[1];
        statusKeys.set(pid, key);
      }
    }
  }
  // Given a full key and pid that came from it, removes it
  // unless the pid is current.
  function removeIfOutdated(fullKey, pid) {
    if (!currentPids.has(pid)) {
      const value = store.getItem(fullKey);
      store.removeItem(fullKey);
      console.log('Removing info for old pid:', fullKey, '=', value)
      if (fullKey.startsWith('Toy:beat:')) {
        console.log('Last heartbeat at', new Date(Number(value)));
      }
    }
  }
  // Now we do all modifications in a batch after iterating.
  statusKeys.forEach(removeIfOutdated);
  beatKeys.forEach(removeIfOutdated);
}

/**
 * Records that this pid is active.
 */
function heartbeat() {
  localStorage.setItem('Toy:beat:' + pid, '' + Date.now());
}

// Immediately issue a heartbeat and clean up old stuff.
heartbeat();
removeOldPidData();

// Then repeat the routine every ten seconds.
window.setInterval(function() { heartbeat(); removeOldPidData(); }, 10000);

//// ELEMENT RESIZE HANDLERS

/**
 * This observer creation code is from an example in the
 * csswg draft.
 */
Toy.sizeObserver = new ResizeObserver(entries => {
  for (const entry of entries) {
    let cs = window.getComputedStyle(entry.target);
    /*
    console.log('watching element:', entry.target);
    console.log(entry.contentRect.top, ' is ', cs.paddingTop);
    console.log(entry.contentRect.left, ' is ', cs.paddingLeft);
    console.log(entry.borderBoxSize[0].inlineSize, ' is ', cs.width);
    console.log(entry.borderBoxSize[0].blockSize, ' is ', cs.height);
    */
    if (entry.target.handleResize)
        entry.target.handleResize(entry);
  }
});

/**
 * Simplistic access to the resize observer.
 * Call this at most once per element to be observed.
 * The handler will be called with an entry where
 * the element is the target.
 * 
 */
function onResize(element, handler) {
  element.handleResize = handler;
  Toy.sizeObserver.observe(element);
};

//// Export public names.

Toy.onResize = onResize;

Toy.dom = dom;

// This is a circled latin small letter i.
// An "info" character without circle is available at &#x2139;
// A "circled information source character" exists at &#x1f6c8;
// but it is not supported in Chrome fonts.
// In font-awesome 4.7.0 "fa fa-info-circle".  See also the "warning
// sign", &#x26a0, and font-awesome 4.7.0 "fa fa-question-circle".
Toy.infoChar = '<span style="color:blue">&#x24d8;</span>';

Toy.hasOwn = hasOwn;
Toy.getOwn = getOwn;
Toy.addMethods = addMethods;
// Done at point of definition because "extends" is a reserved word.
// Toy.extends = extends;

Toy.MAX_INT = MAX_INT;
Toy.div = div;
Toy.mod = mod;
Toy.gcd = gcd;
Toy.lcm = lcm;
Toy.npd = npd;
Toy.getPrimes = getPrimes;
Toy.nextPrimeFactor = nextPrimeFactor;
Toy.primeFactors = primeFactors;

Toy.debug = debug;
Toy.check = check;
Toy.factSquish = factSquish;
Toy.assertTrue = assertTrue;
Toy.debugAssertions = true;
Toy.assert = assert;
Toy.debugString = debugString;
Toy.locked = locked;
Toy.unlock = unlock;
Toy.strict = strict;
Toy.errant = errant;

Toy.isEmpty = isEmpty;
Toy.mapSize = mapSize;
Toy.configure = configure;
Toy.asMap = asMap;
Toy.ownProperties = ownProperties;
Toy.object0 = object0;
Toy.removeAll = removeAll;
Toy.removeExcept = removeExcept;
Toy.isIterable = isIterable;
Toy.asSet = asSet;
Toy.union = union;
Toy.intersection = intersection;
Toy.setDiff = setDiff;
Toy.isSubset = isSubset;
Toy.equalSets = equalSets;
Toy.each = each;
Toy.memo = memo;
Toy.format = format;
Toy.interpolate = interpolate;
Toy.trimParens = trimParens;
Toy.sortMap = sortMap;

Toy.rebind = rebind;
Toy.abort = abort;
Toy.bind = bind;
Toy.invoker = invoker;
Toy.error = error;
Toy.newError = newError;
Toy.isError = isError;
Toy.normalReturn = normalReturn;
Toy.catching = catching;
Toy.withExit = withExit;
Toy.catchAborts = catchAborts;
Toy.thrown = null;

Toy.NestedTimer = NestedTimer;

Toy.jsonParse = jsonParse;
Toy.stringify = stringify;

Toy.pid = pid;  // Note: this property does not control the internal variable.
Toy.checkDocName = checkDocName;
Toy.readDoc = readDoc;
Toy.writeDoc = writeDoc;
Toy.rmDoc = rmDoc;
Toy.lsDocs = lsDocs;
Toy.grepDocs = grepDocs;

Toy.getSavedState = getSavedState;
Toy.saveState = saveState;
Toy.noteState = noteState;
Toy.isDocHeldFrom = isDocHeldFrom;
// For testing:
Toy._releaseThisPid = releaseThisPid;

Toy.eachStore = eachStore;

Toy.benchmark = benchmark;
Toy.ToySet = ToySet;
Toy.emptySet = emptySet;
Toy.ToyMap = ToyMap;
Toy.ArraySnap = ArraySnap;

Toy.track = track;
Toy.tracked = tracked;
Toy.trackingData = trackingData;
Toy.noticeStack = noticeStack;
Toy.showStacks = showStacks;

Toy.Refresher = Refresher;
Toy.soonDo = soonDo;
Toy.wait = wait;
Toy.afterRepaint = afterRepaint;
Toy.allowRepaint = allowRepaint;

Toy.changed = changed;
Toy.onChange = onChange;

Toy.makeTriangle = makeTriangle;

Toy.useParentOrigin = useParentOrigin;

Toy.rpcLog = rpcLog;
Toy.logRpc = false;
Toy.MessageQueue = MessageQueue;
Toy.FakeRpcWorker = FakeRpcWorker;
Toy.makeRpcPromise = makeRpcPromise;

Toy.copyToClipboard = copyToClipboard;

// for interactive testing
Toy._testTriangle = _testTriangle;

})();
