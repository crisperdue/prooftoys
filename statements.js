// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for statements.html

var cx = 105, cy = 105;
var r = 100;
var aRadius = 30;
var bRadius = 150;
var blue25 = 'hsla(240, 100%, 50%, 1)';
var green25 = 'hsla(120, 100%, 30%, 1)';
var red25 = 'hsla(10, 100%, 50%, 1)';


var shadeSilver = function() {
  var canvas = document.createElement('canvas');
  canvas.width = 10;
  canvas.height = 10;
  var cxt = initCxt(canvas);
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
  var cxt = initCxt(canvas);
  cxt.strokeStyle = 'rgb(180, 180, 255)';
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
  var cxt = initCxt(canvas);
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

var circleA = {
  x: 105, y: 105, radius: 30, fillStyle: {image: shadeYellow},
  label: 'A', labelX: 105
};

var circleB = {
  x: 225, y: 105, radius: 160, fillStyle: {image: shadeBlue},
  label: 'B', labelX: 175
};

var circleC = {
  x: -15, y: 105, radius: 160, fillStyle: {image: shadeSilver},
  label: 'C', labelX: 35
};

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

function twoArrowsAndNumberLine() {
  // Picture with two arrows and a number line:
  var c = initCxt('canvasArrow');
  var originX = 150;
  var originY = 60;
  var style1 = {
    fillStyle: {image: shadeYellow},
    translate: [originX + 10, originY - 30], scale: [120, 100],
    lineWidth: 1,
    strokeStyle: 'silver'
  };
  arrow(c, style1);
  var style2 = {
    fillStyle: {image: shadeSilver},
    translate: [originX + 100, originY - 27], scale: [-200, 100],
    lineWidth: 1,
    strokeStyle: 'silver'
  };
  arrow(c, style2);
  c.moveTo(originX - 100, originY);
  c.lineTo(originX + 100, originY);
  c.moveTo(originX - 100, originY);
  c.lineTo(originX - 100, originY - 10);
  c.moveTo(originX + 100, originY);
  c.lineTo(originX + 100, originY - 10);
  c.moveTo(originX, originY);
  c.lineTo(originX, originY - 10);
  c.lineWidth = 1;
  c.lineStyle = 'black';
  c.stroke();

  c.textAlign = 'center';
  c.textBaseline = 'top';
  c.fillStyle = 'black';
  c.fillText('-100', originX - 100, originY + 5);
  c.fillText('0', originX, originY + 5);
  c.fillText('100', originX + 100, originY + 5);
}

function draw() {
  // First picture: x > 10 or x < 100.
  var c = initCxt('canvasOrAll');
  withinCircle(c, function() {
      drawCircle(c, merge(circleB, {
	  label: 'x > 10', labelX: 155, fillStyle: {image: shadeYellow}}));
      drawCircle(c, merge(circleC, {label: 'x < 100', labelX: 55}));
    });

  // Second picture.
  twoArrowsAndNumberLine();

  // Venn diagram of an implication.
  c = initCxt('canvasImplies');
  withinCircle(c, function() {
      var styleA = {label: 'men', fillStyle: '#fff'};
      drawCircle(c, merge(circleA, styleA));
      var styleC = {label: 'mortals', labelX: 170, fillStyle: '#fff'};
      drawCircle(c, merge(circleB, styleC));
    });
}

window.onload = draw;
