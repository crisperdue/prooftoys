// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for statements.html

var cx = 105, cy = 105;
var r = 100;
var aRadius = 30;
var bRadius = 150;


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
  shape: circle,
  x: 105, y: 105, radius: 30, fillStyle: {image: shadeYellow},
  label: 'A'
};

var circleB = {
  shape: circle,
  x: 225, y: 105, radius: 160, fillStyle: {image: shadeBlue},
  label: 'B', labelX: 175
};

var circleC = {
  shape: circle,
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
      drawCircle(c, merge(circleC, {label: 'x < 100', labelX: 55}));
      drawCircle(c, merge(circleB, {
	  label: 'x > 10', labelX: 155, fillStyle: {image: shadeYellow}}));
    });

  // Arrows.
  twoArrowsAndNumberLine();

  c = initCxt('canvasAnd');
  withinCircle(c, function() {
      var style1 = {x: cx, y: cy, radius: r, fillStyle: {image: shadeSilver}};
      drawCircle(c, style1);
      var overrides = {fillStyle: {image: shadeYellow}, label: 'A and B'};
      var style2 = merge(style1, overrides);
      drawCircle(c, style2);
    });

  // Venn diagram of an implication.
  c = initCxt('canvasImplies');
  withinCircle(c, function() {
      var styleA = {label: 'birds', fillStyle: '#fff'};
      drawCircle(c, merge(circleA, styleA));
      var styleC = {label: 'wings', labelX: 170, fillStyle: '#fff'};
      drawCircle(c, merge(circleB, styleC));
    });

  // Venn diagram of a false implication, coloring in just the
  // area where the implication is false.
  c = initCxt('canvasNotImplies');
  withinCircle(c, function() {
      var styleA =
        merge(circleA, {x: 85, label: 'birds', fillStyle: '#fff'});
      drawCircle(c, styleA);
      var styleC =
        merge(circleB,
              {shape: outCircle, label: 'wings', labelX: 160, fillStyle: '#fff'});
      drawCircle(c, styleC);
      withClipping(c, {shape: canvas, fillStyle: 'red', render: 'fill'},
        styleC, styleA);
    });

  // Picture where bird --> wings, with normal shading.
  c = initCxt('birdWingsTrue');
  c.canvas.scrollIntoView();
  withinCircle(c, function() {
      var styleA =
        {outside: true, label: 'birds', fillStyle: {image: shadeYellow}};
      drawCircle(c, merge(circleA, styleA));
      var styleC =
        merge(circleB,
              {label: 'wings', labelX: 170,
               fillStyle: {image: shadeSilver}});
      drawCircle(c, styleC);
    });

  // Picture where bird --> wings is not true everywhere, with normal shading.
  c = initCxt('birdWingsFalse');
  c.canvas.scrollIntoView();
  withinCircle(c, function() {
      var styleA =
        {outside: true, x: 77, label: 'birds', labelX: 83,
         fillStyle: {image: shadeYellow}};
      drawCircle(c, merge(circleA, styleA));
      var styleC =
        merge(circleB,
              {shape: outCircle, label: 'wings', labelX: 160,
               fillStyle: {image: shadeSilver}});
      drawCircle(c, styleC);
    });
}

window.onload = draw;
