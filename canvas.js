// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Utilities for working with Canvases.

// Number of degrees per radian.
var degree = Math.PI / 180;

// Context lineWidth to indicate rendering should not stroke.
var noStroke = 1e-9;

// Merge this style to prevent filling of regions.
var noFillStyle = {noFill: true};

/**
 * Call the function with each of the elements of the array-like
 * argument in turn.
 */
function forEach(arrayLike, fn) {
  Array.prototype.forEach.call(arrayLike, fn);
}

/**
 * Renders the given rendering info in the given graphics context,
 * clipped by zero or more shapes (clipping regions).  The "shape"
 * argument is optional, and multiple shape arguments may be given,
 * and is passed to the function "render" along with the graphics
 * context.
 *
 * The rendering info is an object with shape information and normally
 * some combination of fill information, stroke information, and label
 * information.
 *
 * This function restores the original graphics context in all cases
 * before exiting.  Arguments are a graphics context, a rendering
 * information object, and zero or more shapes, whose intersection
 * will be used to clip the rendering.  The shapes are given as
 * functions, each computing a path.
 */
function withClipping(cxt, info, clipPaths_) {
  cxt.save();
  try {
    for (var i = 2; i < arguments.length; i++) {
      var style = arguments[i];
      cxt.beginPath();
      style.shape(cxt, style);
      cxt.clip();
    }
    render(cxt, info);
  } finally {
    cxt.restore();
  }
}

/**
 * Calls the function passing it the context cxt in an environment
 * with the circle centered at point cx, cy and radius "r" as the
 * clipping region.
 *
 * After all of this restores the original rendering context and draws
 * the perimeter of the clipping region.
 */
function withinCircle (cxt, fn) {
  cxt.save();
  cxt.beginPath();
  makeCircle(cxt, cx, cy, r);
  cxt.clip();
  cxt.beginPath();

  fn(cxt);
  cxt.restore();
  cxt.save();

  // Make the bounding circle.
  cxt.beginPath();
  cxt.lineWidth = 2;
  cxt.strokeStyle = 'black';
  makeCircle(cxt, cx, cy, r, true);
  cxt.stroke();

  cxt.restore();
  cxt.beginPath();
}

/**
 * Adds a circle path (or the outside of one) from style info.
 */
function circle(cxt, info) {
  if (info.outside) {
    outside(cxt);
  }
  makeCircle(cxt, info.x, info.y, info.radius, info.counter);
}

/**
 * Adds a circle to the current path, centered at x, y, with the given
 * radius, and counterclockwise iff the "counter" argument is true;
 * then closes the path.  Does not render anything.
 */
function makeCircle(cxt, x, y, radius, counter) {
  // The "arc" method behaves as if it starts with a lineTo, so start
  // by moving to the start point of the arc.
  cxt.moveTo(x + radius, y);
  cxt.arc(x, y, radius, 0, 2 * Math.PI, counter);
  cxt.closePath();
}

/**
 * If using the default transform this makes a path enclosing the
 * entire canvas, clockwise.
 */
function canvas(cxt, info) {
  var canvas = cxt.canvas;
  var w = canvas.width;
  var h = canvas.height;
  cxt.moveTo(0, 0);
  cxt.lineTo(0, w);
  cxt.lineTo(h, w);
  cxt.lineTo(h, 0);
  cxt.closePath();
}

/**
 * Traverses the boundaries of the canvas counterclockwise.
 * Assumes the coordinate system has not been transformed.
 * Use this to fill outside a shape.
 */
function outside(cxt) {
  var canvas = cxt.canvas;
  var w = canvas.width;
  var h = canvas.height;
  cxt.moveTo(0, 0);
  cxt.lineTo(0, h);
  cxt.lineTo(h, w);
  cxt.lineTo(w, 0);
  cxt.closePath();
}

/**
 * Builds a path for the graphics object described by "info", and
 * renders it if it has a "render" property.
 *
 * Supported values for the "render" property are "fill", "stroke",
 * and "fillStroke".  If the value is "fillStroke" this fills and then
 * strokes according to the styles specified by the info.
 *
 * This always starts a fresh path, and if it renders it starts a new
 * path after rendering.
 *
 * Filling and stroking are currently only done in the drawing phase.
 *
 * TODO: Be more flexible about strategies for stroking, and support
 * filling just the outside of the given shape.
 */
function render(cxt, info) {
  var fn = info.shape;
  if (typeof fn !== 'function') {
    throw new Error('Not a valid shape: ' + fn);
  }
  cxt.beginPath();
  fn(cxt, info);
  var fill = !info.noFill;
  var stroke = cxt.lineWidth > noStroke;  
  if (fill || stroke) {
    // Render.
    cxt.save();
    try {
      // Merge styles into the graphics context.
      mergeStyle(cxt, info);
      if (fill) {
        cxt.fill();
      }
      if (stroke) {
        cxt.stroke();
      }
    } finally {
      cxt.restore();
      cxt.beginPath();
    }
  }
  // TODO: Make each shape do its own labeling.
  if (fn === circle) {
    labelCircle(cxt, info);
  }
}

/**
 * Renders label information for the circle described by "info", using
 * the given graphics context.  Saves and restores the context around
 * the rendering.  Currently strokes the circle's border and writes
 * the text of info.label in black at X coordinate info.labelX if
 * given, otherwise info.x; and Y coordinate info.y.
 */
function labelCircle(cxt, info) {
  if (info.label) {
    var labelX = 'labelX' in info ? info.labelX : info.x;
    cxt.save();
    cxt.textAlign = 'center';
    cxt.textBaseline = 'middle';
    cxt.fillStyle = 'black';
    cxt.fillText(info.label, labelX, info.y);

    cxt.beginPath();
    makeCircle(cxt, info.x, info.y, info.radius);
    cxt.strokeStyle = 'gray';
    cxt.lineWidth = 1;
    cxt.stroke();
    cxt.beginPath();

    cxt.restore();
  }
}

/**
 * Merges the properties of any number of objects, with later argument
 * properties overriding earlier ones, returning a new object with the
 * merged properties.
 */
function merge() {
  var result = {};
  for (var i = 0; i < arguments.length; i++) {
    var arg = arguments[i];
    for (var key in arg) { result[key] = arg[key]; }
  }
  return result;
}

/**
 * The style argument must be a style descriptor.  If it has a
 * fillStyle, set that as the context fillStyle.  If it is a string,
 * set the context's fillStyle directly.  Otherwise, if the fillStyle
 * has an "image" property it describes a pattern.  The image property
 * can be either an element or an element ID, and sets the context's
 * fillStyle to a pattern with repetition style given as the
 * fillStyle's "repeat" property, which defaults to "repeat".
 *
 * Style properties:
 *
 * translate: pair of numbers indicating X, Y the origin will be
 * translated to.
 *
 * scale: number or pair of numbers to scale X and Y independently,
 * applies after translation.
 *
 * rotate: angle to rotate by, in radians.
 */
function mergeStyle(cxt, style) {
  // Pick up various properties from the style.
  for (var key in cxt) {
    var exclude = ['fillStyle', 'strokeStyle', 'canvas'];
    if (exclude.indexOf(key) < 0) {
      var value = cxt[key];
      if (typeof value !== 'function' && key in style) {
        cxt[key] = style[key];
      }
    }
  }

  // Canvas width and height.  Note that setting these resets all
  // other context properties to their defaults.
  if ('width' in style) {
    cxt.canvas.width = style.width;
  }
  if ('height' in style) {
    cxt.canvas.height = style.height;
  }

  // Fill style
  var fill = style.fillStyle;
  if (fill != null) {
    if (typeof fill === 'string') {
      cxt.fillStyle = fill;
    } else {
      var image = fill.image;
      if (image) {
        if (typeof image === 'string') {
          image = document.getElementById(image);
        }
        var pattern = cxt.createPattern(image, fill.repeat || 'repeat');
        cxt.fillStyle = pattern;
      }
    }
  }

  // Stroke style
  var stroke = style.strokeStyle;
  if (stroke != null) {
    if (typeof stroke === 'string') {
      cxt.strokeStyle = stroke;
    } else {
      var image = stroke.image;
      if (image) {
        if (typeof image === 'string') {
          image = document.getElementById(image);
        }
        var pattern = cxt.createPattern(image, stroke.repeat || 'repeat');
        cxt.strokeStyle = pattern;
      }
    }
  }

  // Translation
  var translate = style.translate;
  if (translate) {
    translateX = translate[0];
    translateY = translate[1];
    cxt.translate(translateX, translateY);
  }
  
  // Scaling
  var scale = style.scale;
  var scaleX = scale;
  var scaleY = scale;
  if (scale && scale.length == 2) {
    scaleX = scale[0];
    scaleY = scale[1];
  }
  cxt.scale(scaleX, scaleY);
  
  // Rotation
  cxt.rotate(style.rotate);
}

/**
 * Draw a right arrow of unit length and width specified by
 * info.width, which defaults to .1, along the X axis from the origin.
 *
 * TODO: Parameterize at least by length, so the arrowhead does not
 * get stretched by scaling.
 */
function arrow(c, info) {
  c.save();
  mergeStyle(c, info);
  try {
    var width = info.width || .1;
    var width2 = width / 2;
    c.moveTo(0, -width2);
    c.lineTo(.9, -width2);
    c.lineTo(.9, -width);
    c.lineTo(1, 0);
    c.lineTo(.9, width);
    c.lineTo(.9, width2);
    c.lineTo(0, width2);
    c.closePath();
    // Reset the transform to the default before filling
    // and stroking so the widths and patterns are in the
    // usual coordinate system.
    c.setTransform(1, 0, 0, 1, 0, 0);
    c.fill();
    c.stroke();
  } finally {
    c.restore();
    c.beginPath();
  }
}

/**
 * Returns the untransformed canvas coordinates of the given event.
 * Value is an Object with properties "x" and "y".
 * 
 * Technique from "JavaScript: The Definitive Guide", 6th edition.
 */
function eventPoint(canvas, event) {
  var rect = canvas.getBoundingClientRect();
  var x = (event.clientX - rect.left) * (canvas.width / rect.width);
  var y = (event.clientY - rect.top) * (canvas.height / rect.height);
  return {x: x, y: y};
}
