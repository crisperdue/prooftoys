// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Utilities for working with Canvases.

/**
 * Calls the function passing it the context cxt in an environment
 * with the circle centered at point cx, cy and radius "r" as the
 * clipping region, then performs the actions specified by the labels
 * array, passing each of its elements the context as an argument and
 * clearing the array.
 *
 * After all of this restores the original rendering context and draws
 * the perimeter of the clipping region.
 */
function withinCircle (cxt, fn) {
  cxt.save();
  cxt.beginPath();
  circle(cxt, cx, cy, r);
  cxt.clip();
  cxt.beginPath();

  fn(cxt);
  // Apply all of the labels.
  labels.forEach(function(fn) { fn(cxt); });
  labels = [];

  cxt.restore();
  cxt.save();

  // Make the bounding circle.
  cxt.beginPath();
  cxt.lineWidth = 2;
  cxt.strokeStyle = 'black';
  circle(cxt, cx, cy, r, true);
  cxt.stroke();

  cxt.restore();
  cxt.beginPath();
}

/**
 * Renders a circle using the x, y, and radius properties of the given
 * "info" object and the given rendering context.  Iff info.outside is
 * truthy renders the outside of the circle rather than the inside.
 *
 * Restores the graphics context to its state before the call, and
 * adds a request to run "labelCircle" to the global labels list.
 */
function drawCircle(cxt, info) {
  cxt.save();
  if (info.outside) {
    outside(cxt);
  }
  mergeFillStyle(cxt, info);
  fillCircle(cxt, info.x, info.y, info.radius);
  cxt.restore();
  labels.push(function() { labelCircle(cxt, info); });
}

/**
 * Fills a circle using the given rendering context.
 */
function fillCircle(cxt, x, y, radius) {
  circle(cxt, x, y, radius);
  cxt.fill();
  cxt.beginPath();
}

/**
 * Adds a circle to the current path, centered at x, y, with the given
 * radius, and counterclockwise iff the "counter" argument is true;
 * then closes the path.  Does not render anything.
 */
function circle(cxt, x, y, radius, counter) {
  cxt.arc(x, y, radius, 0, 2 * Math.PI, counter);
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
 * Renders label information for the circle described by "info", using
 * the given graphics context.  Saves and restores the context around
 * the rendering.  Currently strokes the circle's border and writes
 * the text of info.label in black at X coordinate info.labelX and Y
 * coordinate info.y.
 */
function labelCircle(cxt, info) {
  if (info.labelX != null) {
    cxt.save();
    cxt.fillStyle = 'black';
    cxt.fillText(info.label, info.labelX, info.y);

    cxt.beginPath();
    circle(cxt, info.x, info.y, info.radius);
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
 */
function mergeFillStyle(cxt, style) {
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
        cxt.fillStyle  = pattern;
      }
    }
  }
}
