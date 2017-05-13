// Copyright 2011 - 2017 Crispin Perdue.
// All rights reserved.

////
//// GENERAL UTILITIES -- self-contained
////
//// All of these utilities are generic, not specific to Prooftoys or
//// theorem-proving.
////


// Set everything up immediately on load, avoiding changes to the
// global environment except through namespace "Toy".
(function() {

/**
 * Toy.incompatible - true iff browser is an old MSIE not compatible
 * with Prooftoys + jQuery 2 and similar JavaScript.
 */
// See http://www.useragentstring.com/.
// TODO: Support only "modern" browsers based on caniuse.com and
//   similar.  In particular MSIE 11+, but other requirements TBD,
//   perhaps all browsers shown in default views in caniuse.com.
Toy.incompatible = !!navigator.userAgent.match(/ MSIE [1-8][.]/);

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
    // Set up the prototype for the child class.
    // Instances will see this as their constructor.
    constructor.prototype = Object.create(parent.prototype, {
        constructor: {value: constructor}
      });
  } else if (typeof constructor === 'function' && parent == null) {
    // Do nothing.
  } else {
    throw new Error('Toy.extends requires functions as arguments.');
  }
  constructor.addMethods = function(properties) {
    $.extend(constructor.prototype, properties);
  };
};

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
  result = [];
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

////
//// Assertions, error reporting and debugging
////

// In Prooftoys, some "errors" are nonlocal flow of control, and
// intended to be caught, as in catch/throwResult.  Most errors are
// program bugs, and should enter the debugger immediately if the
// debugger is available, with reporting to the developer and/or end
// user as appropriate.  With reporting to the end user is appropriate
// recovery of application state.  In some situations the calling code
// may intentionally create situations leading to errors, noticing and
// responding to those errors, bypassing the usual reporting.

/**
 * Builds and throws a new Error object with the given info.  If the
 * info is a string, it becomes the message; if it is a function, its
 * value becomes the message, otherwise treats the info
 * as property names and values to assign to the error.
 *
 * The optional type if given is the error constructor, defaulting to
 * Error.
 */
function err(info, type) {
  var error = new (type || Error)();
  if (typeof info === 'string') {
    error.message = info;
  } else if (typeof info === 'function') {
    error.message = info();
  } else {
    jQuery.extend(error, info);
  }
  throw error;
}

/**
 * If the condition is not truthy, throws using the function "err"
 * with the given info and optional type.  See also "assertTrue",
 * which logs the stack and enters a debugger if available.
 */
function check(condition, info, type) {
  if (!condition) {
    err(info, type);
  }
}

/**
 * Logs an error; the message property if that is truthy, otherwise
 * the argument itself.
 */
function logError(err) {
  if (window.console) {
    window.console.error(err.stack);
  }
}

/**
 * Call the given function passing no arguments.  Report any errors to
 * the user and to the console, then rethrow.
 */
function withErrorReporting(fn) {
  try {
    return fn();
  } catch(err) {
    logError(err);
    window.alert(err.message);
    throw err;
  }
}

// Accumulation of assertion failures and potentially information
// about other errors that have occurred.
var errors = [];

/**
 * Asserts that the condition is true, throwing an exception if it is
 * not.  The message may be either a string or a function of no
 * arguments that returns something that can be logged.  If the
 * optional step is supplied it should be the most recent available
 * completed proof step.
 *
 * If the message is a string, it may be a format string, and all
 * arguments following it are accessible as {1}, {2}, and so on.
 *
 * Logs the message and step into the errors list by appending an
 * object with properties 'message' and 'step'.
 */
function assertTrue(condition, message_arg) {
  if (!condition) {
    var step;
    var message;
    if (typeof message_arg == 'function') {
      message = message_arg();
    } else {
      var args = arguments;
      message = message_arg.replace(/\{.*?\}/g, function(matched) {
          return args[matched.slice(1, -1) - -1];
        });
      var isProved = Toy.isProved;
      // Find a step argument if there is one.
      for (var i = 0; i < args.length; i++) {
        var arg = args[i];
        if (isProved(arg)) {
          // TODO: Handle multiple "step" arguments.
          step = arg;
          break;
        }
      }
    }
    errors.push({message: message, step: step});
    var e = new Error(message);
    e.step = step;
    e.isAssert = true;
    if (Toy.debugAssertions) {
      console.log(e.stack);
      debugger;
    }
    throw e;
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
  if (typeof o == 'object') {
    var result = '{';
    var keys = [];
    for (var key in o) { keys.push(key); }
    keys.sort();
    for (var i = 0; i < keys.length; i++) {
      var key = keys[i];
      if (hasOwn(o, key)) {
        if (result.length > 1) {
          result += ', ';
        }
        result += key + ': ';
        var value = o[key];
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
    }
    return result + '}';
  } else {
    return o.toString();
  }
}


//
// Data manipulation utilities
//

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
 * Configure the given object with the given property descriptors.
 * This is like Object.defineProperties, except key values that are
 * not specifically of type Object are treated as plain values and
 * not made writable, enumerable, or configurable.
 */
function configure(object, properties) {
  var define = Object.defineProperty;
  for (key in properties) {
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
 * Synonym for ownProperties.
 */
function asMap(object) {
  return ownProperties(object);
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
    throw new Error('object0 bad arguments list');
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
 * "own" properties of the second map.
 */
function removeExcept(map1, map2) {
  for (var k in map1) {
    if (!hasOwn(map2, k)) {
      delete map1[k];
    }
  }
}

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
  var map = (map_arg.constructor === Object)
    ? map_arg
    : arguments;
  return fmt.replace(/\{[$_a-zA-Z0-9]*?\}/g, function(matched) {
      return map[matched.slice(1, -1)];
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

//// Result -- returning values using catch/throw.

/**
 * Throw one of these to return an arbitrary value
 * from a recursive function.
 */
function Result(value) {
  this.value = value;
}

/**
 * Throws a Result object with the given value as its value.
 */
function throwResult(value) {
  throw new Result(value);
}

/**
 * Call the given function with the given arguments, returning the
 * undefined value if the function throws, else the value returned
 * from the function call.
 */
function normalReturn(fn, _args) {
  var result;
  var args = jQuery.makeArray(arguments);
  args.shift();
  try {
    return fn.apply(undefined, args);
  } catch(e) {
    return;
  }
}

/**
 * Call the given function, passing it any additional arguments given.
 * If it throws a Result object, return its "value".  Rethrow any
 * other thrown value, and return the function value if it does not
 * throw.
 */
function catchResult(fn, _args) {
  var args = jQuery.makeArray(arguments);
  args.shift();
  try {
    return fn.apply(undefined, args);
  } catch(e) {
    if (e instanceof Result) {
      return e.value;
    } else {
      throw e;
    }
  }
}


//// NestedTimer -- timer that excludes time in other timers

// Stack of active NestedTimers.
_timers = [];

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


//// benchmark -- times repeated calls to a function

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


//// SET

function Set(stringifier) {
  this.map = {};
  this.stringifier = stringifier || String;
}

var emptySet = Object.freeze(new Set());

/**
 * Add an element, returning this.
 */
Set.prototype.add = function(value) {
  this.map[this.stringifier(value)] = value;
  return this;
};

/**
 * Add all the values in the given array or Set to this Set.
 * Return this.
 */
Set.prototype.addAll = function(more) {
  var self = this;
  function add(value) { self.add(value); }
  if (more instanceof Set) {
    more.each(add);
  } else {
    more.forEach(add);
  }
  return self;
};

/**
 * Does the set contain the element (one with the same key)?
 */
Set.prototype.has = function(value) {
  return hasOwn(this.map, this.stringifier(value));
};

/**
 * Applies to another collection that has an "each" method that
 * iterates over its elements, exiting in case of a defined value.
 * Returns a boolean value indicating whether this contains all the
 * elements of the other collection.
 */
Set.prototype.superset = function(other) {
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
Set.prototype.equals = function(other) {
  return this.superset(other) && other.superset(this);
};

/**
 * Remove the element.
 */
Set.prototype.remove = function(value) {
  delete this.map[this.stringifier(value)];
};

/**
 * Call the given function for each element of the set, passing the
 * set element as its argument.  Use the optional thisObj as "this"
 * for the calls, or "undefined" if it is not given.  If the function
 * returns any value other than "undefined" that value becomes the
 * return value of this method, and iteration ends.
 */
Set.prototype.each = function(fn, thisObj) {
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
Set.prototype.size = function() {
  var counter = 0;
  this.each(function () { counter++; });
  return counter;
};

/**
 * Is the set empty?
 */
Set.prototype.isEmpty = function() {
  for (var key in this.map) {
    return false;
  }
  return true;
};

/**
 * Remove all members of this Set.
 */
Set.prototype.clear = function() {
  var map = this.map;
  for (var key in map) {
    delete map[key];
  }
};

/**
 * Returns an element of the set or undefined if the set is empty.
 */
Set.prototype.choose = function() {
  for (var key in this.map) {
    return this.map[key];
  }
};

/**
 * Returns an iterable (actually an array) of the values in the Set.
 */
Set.prototype.values = function() {
  var result = [];
  this.each(x => void result.push(x));
  return result;
};

Set.prototype.toString = function() {
  var values = this.values().map(function (x) { return x.toString(); });
  return format('{1}({2})', this.constructor.name || '', values);
};


//// MAP

/**
 * Arguments are a function to convert a key object to an identifying
 * string, and a default value when getting a key that is not in the
 * map.  The default default is the undefined value.
 */
function Map(stringifier, dfault) {
  this.map = {};
  this.stringifier = stringifier || String;
  this.dfault = dfault;
}

/**
 * Set the value of a map element.
 */
Map.prototype.set = function(key, value) {
  this.map[this.stringifier(key)] = value;
};

/**
 * Does it have an element with matching key?
 */
Map.prototype.has = function(key) {
  return hasOwn(this.map, this.stringifier(key));
};

/**
 * Gets the value at a key or undefined if no such element.
 */
Map.prototype.get = function(key) {
  var map = this.map;
  var k = this.stringifier(key);
  return hasOwn(map, k) ? map[k] : this.dfault;
};

/**
 * Remove any element with matching key.
 */
Map.prototype.remove = function(key) {
  delete this.map[this.stringifier(key)];
};

/**
 * Iterate over the map, allowing early return.  The fn receives a
 * value and (string) key.  In any iteration where the value of the
 * function is not the undefined value, immediately returns that
 * value.
 */
Map.prototype.each = function(fn, thisObj) {
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
Map.prototype.size = function() {
  var counter = 0;
  this.each(function () { counter++; });
  return counter;
};

/**
 * Is it empty?
 */
Map.prototype.isEmpty = function() {
  for (var key in this.map) {
    return false;
  }
  return true;
};


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
    throw new Error('Not a named function');
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
 * Returns a promise that resolves after the given number
 * of microseconds.
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
    throw new Error('Triangle direction must be up, down, right, or left');
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


//// RPC with message queuing
//
// This section uses ES6 / ES2015 language features

/**
 * Message queue constructor for RPC communication, as with Web Worker
 * threads.  If a numeric argument and URI string are supplied, will
 * immediately create and add that many Worker threads.
 */
function MessageQueue(n, uri) {
  var Map = window.Map;
  // Queue of messages to be sent.  Each item is a data structure with
  // properties "resolve", "reject", and "wrapper", where the wrapper
  // has a channelType, an "id", and "data", which is the message
  // itself.
  this.queue = [];
  // Map from rpc ID to message, containing messages that have been sent
  // but not yet responded to.  The items have the same structure as
  // queue elements.
  this.inProgress = new Map();
  // Set of Web Workers handling messages from this queue.
  this.workers = new Set();
  // Workers not currently handling a request.
  this.idleWorkers = [];

  if (arguments.length == 2) {
    for (var i = 0; i < n; i++) {
      this.addWorker(new Worker(uri));
    }
  }
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
   * Sends a request via the queue.  Returns a Promise to be resolved
   * with the result of the call.  Standard RPC worker error responses
   * are a plain object with properties:  type: name of Error object
   * constructor, message: error.message, stack: error.stack.
   */
  send: function(message) {
    var wrapper = {channelType: 'RPC', id: MessageQueue.id++, data: message};
    var info;
    var promise = new Promise(function(resolve, reject) {
        info = {resolve: resolve, reject: reject, wrapper: wrapper};
      });
    this.queue.push(info);
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
        if (wrapper.hasOwnProperty('error')) {
          info.reject(wrapper.error);
        } else {
          info.resolve(wrapper.result);
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
    console.log('Unknown MessageQueue response', event);
  },

  /**
   * Called at the very start of each dispatch.  This may be
   * overridden to rearrange the lists of waiting requests and idle
   * workers if desired to change the effect of the dispatch.
   */
  schedule: function() {},

  /**
   * Private method called internally at points where it might be
   * appropriate to send another RPC request.  If there is an
   * idle worker and a request in the queue, sends the first
   * request to the first idle worker.
   */
  _dispatch: function() {
    this.schedule();
    if (this.workers.size() === 0) {
      console.log('No RPC workers');
    }
    if (this.idleWorkers.length && this.queue.length) {
      var worker = this.idleWorkers.shift();
      var info = this.queue.shift();
      worker.postMessage(info.wrapper);
      this.inProgress.set(info.wrapper.id, info);
    }
  }
};

Object.assign(MessageQueue.prototype, msgMethods);

/* Test code

var q = new Toy.MessageQueue(1, 'pt/js/worker.js');
var p = q.send({action: 'ping'})
         .then(x => (console.log('ping', x), x))
         .catch(x => console.log('Failed', x));
var p = q.send({action: 'fail'})
         .then(x => (console.log('fail?', x), x))
         .catch(x => console.log('Failed', x));
var p = q.send({action: 'plus1', input: 4})
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
 * internal handler from a timer, and later call to the FakeWorker's
 * onmessage property passing a faked-up event, an object that has a
 * "target" property and a "data" property, but currently no other
 * information.
 *
 * Starts the worker with a short delay to promote prompt repainting.
 * The worker's reply notification has no delay on the theory that
 * the worker will not modify the DOM.
 */
FakeRpcWorker.prototype.postMessage = function(wrapper) {
  var self = this;
  var receiver = self.receiver;
  var reply = {target: self};
  // This function is the same as the "real" onmessage handler
  // function in worker.js for messages to a worker, except this
  // receives the RPC wrapper object directly, not wrapped in an
  // event, and replies by calling the fake worker's onmessage
  // property from a timer.
  function handler() {
    if (wrapper.channelType === 'RPC') {
      try {
        var id = wrapper.id;
        var message = wrapper.data;
        var action = message.action;
        var actions = receiver.actions;
        if (!actions.hasOwnProperty(action)) {
          throw new Error('Unknown RPC action', action);
        }
        var fn = actions[action].bind(receiver);
        var result = fn(message, wrapper);
        reply.data = {channelType: 'RPC', id: id, result: result};
      } catch(error) {
        var e = (receiver.encodeError
                 ? receiver.encodeError(error)
                 : error instanceof Error
                 ? {type: error.constructor.name,
                    message: error.message,
                    stack: error.stack}
                 : '?');
        reply.data = {channelType: 'RPC', id: id, error: e};
      }
      function replier() {
        var responder = self.onmessage;
        responder(reply);
      }
      // The worker code should not access the DOM, so there should
      // not be reason to wait for a repaint before handling the
      // worker's reply.
      window.setTimeout(replier, 0);
    } else if (receiver.handleOther) {
      receiver.handleOther(event);
    } else {
      console.log('Unhandled message', event);
    }
  }
  // Call the handler from a timer.
  // Follow the example of Toy.afterRepaint in allowing time for
  // repaints and other more urgent activities to take priority.
  window.setTimeout(handler, 10);
}


//// Export public names.

Toy.hasOwn = hasOwn;
Toy.getOwn = getOwn;
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

Toy.err = err;
Toy.check = check;
Toy.logError = logError;
Toy.withErrorReporting = withErrorReporting;
Toy.assertTrue = assertTrue;
Toy.debugAssertions = true;
Toy.assert = assert;
Toy.debugString = debugString;

Toy.isEmpty = isEmpty;
Toy.configure = configure;
Toy.asMap = asMap;
Toy.ownProperties = ownProperties;
Toy.object0 = object0;
Toy.removeAll = removeAll;
Toy.removeExcept = removeExcept;
Toy.each = each;
Toy.memo = memo;
Toy.format = format;
Toy.trimParens = trimParens;
Toy.sortMap = sortMap;

Toy.Result = Result;
Toy.throwResult = throwResult;
Toy.catchResult = catchResult;
Toy.normalReturn = normalReturn;

Toy.NestedTimer = NestedTimer;
Toy.benchmark = benchmark;
Toy.Set = Set;
Toy.emptySet = emptySet;
Toy.Map = Map;

Toy.track = track;
Toy.tracked = tracked;
Toy.trackingData = trackingData;

Toy.Refresher = Refresher;
Toy.soonDo = soonDo;
Toy.wait = wait;
Toy.afterRepaint = afterRepaint;
Toy.allowRepaint = allowRepaint;
Toy.makeTriangle = makeTriangle;

Toy.MessageQueue = MessageQueue;
Toy.FakeRpcWorker = FakeRpcWorker;

// for interactive testing
Toy._testTriangle = _testTriangle;

})();
