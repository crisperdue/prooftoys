// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Utilities for working with Canvases.

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

function circle(cxt, x, y, radius, counter) {
  cxt.arc(x, y, radius, 0, 2 * Math.PI, counter);
  cxt.closePath();
}

function fillCircle(cxt, x, y, radius) {
  circle(cxt, x, y, radius);
  cxt.fill();
  cxt.beginPath();
}

/**
 * Traverse the boundaries of the canvas counterclockwise.
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


function drawCircle(cxt, info) {
  cxt.save();
  if (info.outside) {
    outside(cxt);
  }
  mergeFillStyle(cxt, info);
  // cxt.fillStyle = info.fillStyle || cxt.fillStyle;
  fillCircle(cxt, info.x, info.y, info.radius);
  cxt.restore();
  labels.push(function() { labelCircle(cxt, info); });
}

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
