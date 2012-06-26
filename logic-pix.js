// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Building blocks for logic pictures.

var cx = 105, cy = 105;
var r = 100;
var aRadius = 30;
var bRadius = 150;


var shadeSilver = function() {
  var canvas = document.createElement('canvas');
  canvas.width = 10;
  canvas.height = 10;
  var cxt = canvas.getContext('2d');
  cxt.strokeStyle = 'silver';
  cxt.lineWidth = 1.4;
  cxt.lineCap = 'square';
  cxt.moveTo(0, 5);
  cxt.lineTo(5, 0);
  cxt.stroke();
  cxt.moveTo(5, 10);
  cxt.lineTo(10, 5);
  cxt.stroke();
  return canvas;
}();

var shadeBlue = function() {
  var canvas = document.createElement('canvas');
  canvas.width = 10;
  canvas.height = 10;
  var cxt = canvas.getContext('2d');
  cxt.strokeStyle = 'rgb(200, 200, 255)';
  cxt.lineWidth = 1.4;
  cxt.lineCap = 'square';
  cxt.moveTo(0, 5);
  cxt.lineTo(10, 5);
  cxt.stroke();
  return canvas;
}();

var shadeYellow = function() {
  var canvas = document.createElement('canvas');
  canvas.width = 10;
  canvas.height = 10;
  var cxt = canvas.getContext('2d');
  // Fill with a light gray.
  // cxt.fillStyle = '#ccc';
  // cxt.fillRect(0, 0, 10, 10);
  // Then stroke with yellow hatching.
  cxt.strokeStyle = 'yellow';
  cxt.lineWidth = 1.4;
  cxt.lineCap = 'square';
  cxt.moveTo(0, 5);
  cxt.lineTo(5, 10);
  cxt.stroke();
  cxt.moveTo(5, 0);
  cxt.lineTo(10, 5);
  cxt.stroke();
  return canvas;
}();

function initCxt(canvas) {
  if (typeof canvas == 'string') {
    canvas = document.getElementById(canvas);
  }
  if (!canvas) {
    var error = 'initCxt: No canvas';
    console.log(error);
    throw new Error(error);
  }
  var cxt = canvas.getContext('2d');
  // Light blue:
  cxt.fillStyle = 'rgb(210, 210, 255)';
  cxt.textAlign = 'center';
  cxt.textBaseline = 'middle';
  cxt.lineWidth = 1;
  cxt.lineJoin = 'round';
  cxt.font = 'bold 12pt sans-serif';
  return cxt;
}

/**
 * Draws the intersection of circle1 and circle2 using the fill style
 * of circle1.
 */
function drawAnd(cxt, circle1, circle2) {
  withinCircle(cxt, function() {
      var noFill = {noFill: true};
      render(cxt, merge(circle1, noFill));
      render(cxt, merge(circle2, noFill));
      withClipping(cxt, circle1, circle2);
    });
}

var blueShading = {fillStyle: {image: shadeBlue}};

var silverShading = {fillStyle: {image: shadeSilver}};

var yellowShading = {fillStyle: {image: shadeYellow}};


// Circle geometry:

// Small and centered.
var circleCenter = {shape: circle, x: 105, y: 105, radius: 30};

// Large and on the left.
var circleLeft = {shape: circle, x: 5, y: 105, radius: 150};

// Large and on the right.
var circleRight = {shape: circle, x: 205, y: 105, radius: 150};

// Smallish, overlaps circleRightish.
var circleLeftish = {shape: circle, x: 80, y: 105, radius: 38};

// Smallish, overlaps circleLeftish.
var circleRightish = {shape: circle, x: 130, y: 105, radius: 38};
