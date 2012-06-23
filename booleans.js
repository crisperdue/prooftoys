// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for booleans.html
//
// Requires logic-pix.js and canvas.js.

var circleA = {
  x: 105, y: 105, radius: 30, fillStyle: {image: shadeSilver},
  label: 'A', labelX: 105
};

var circleB = {
  x: 205, y: 105, radius: 150, fillStyle: {image: shadeBlue},
  label: 'B', labelX: 175
};

var circleC = {
  x: 5, y: 105, radius: 150, fillStyle: {image: shadeYellow},
  label: 'C', labelX: 35
};

var circleD = {
  x: 80, y: 105, radius: 38, fillStyle: {image: shadeYellow},
  label: 'D', labelX: 65
};

var circleD2 = merge(circleD, {x: 65});

var circleE = {
  x: 130, y: 105, radius: 38, fillStyle: {image: shadeSilver},
  label: 'E', labelX: 145
};

var circleE2 = merge(circleE, {x: 145});

function draw() {

  var cxtA = initCxt('canvasA');
  withinCircle(cxtA, function() {
      drawCircle(cxtA, circleA);
    });

  var cxtB = initCxt('canvasB');
  withinCircle(cxtB, function() {
      drawCircle(cxtB, circleB);
    });

  var cxtC = initCxt('canvasC');
  withinCircle(cxtC, function() {
      drawCircle(cxtC, circleC);
    });

  var cxtNotA = initCxt('canvasNotA');
  withinCircle(cxtNotA, function() {
      drawCircle(cxtNotA, circleA);
      drawCircle(cxtNotA, merge(circleA, {outside: true, fillStyle: 'lime'}));
    });

  var cxtNotB = initCxt('canvasNotB');
  withinCircle(cxtNotB, function() {
      drawCircle(cxtNotB, circleB);
      drawCircle(cxtNotB, merge(circleB, {outside: true, fillStyle: 'lime'}));
    });

  var cxtNotC = initCxt('canvasNotC');
  withinCircle(cxtNotC, function() {
      drawCircle(cxtNotC, circleC);
      drawCircle(cxtNotC, merge(circleC, {outside: true, fillStyle: 'lime'}));
    });

  var cxtOrDE = initCxt('canvasOrDE');
  withinCircle(cxtOrDE, function() {
      drawCircle(cxtOrDE, circleD);
      drawCircle(cxtOrDE, circleE);
    });

  var cxtOrDE2 = initCxt('canvasOrDE2');
  withinCircle(cxtOrDE2, function() {
      drawCircle(cxtOrDE2, merge(circleD, {fillStyle: {image: shadeBlue}}));
      drawCircle(cxtOrDE2, merge(circleE, {fillStyle: {image: shadeBlue}}));
    });

  var cxtAnd = initCxt('canvasAnd');
  window.cxtAnd = cxtAnd;
  drawAnd(cxtAnd, circleA, circleB);

  var cxtAndDE = initCxt('canvasAndDE');
  drawAnd(cxtAndDE,
	  merge(circleD, {fillStyle: {image: shadeBlue}}),
	  merge(circleE, {fillStyle: {image: shadeBlue}}));

  var cxtAndDE2 = initCxt('canvasAndDE2');
  drawAnd(cxtAndDE2, circleD2, circleE2);

  var cxtAll = initCxt('canvasAll');
  drawAll(cxtAll);
  cxtAll.fillStyle = 'black';
  cxtAll.fillText('all', 105, 105);
}

function drawAll(cxt) {
  withinCircle(cxt, function() {
      outside(cxt);
      cxt.fill();
      cxt.beginPath();
    });
}

function drawAnd(cxt, circle1, circle2) {
  withinCircle(cxt, function() {
      cxt.save();
      mergeStyle(cxt, circle1);
      drawAll(cxt);
      mergeStyle(cxt, circle2);
      drawAll(cxt);
      cxt.restore();
      var props = {outside: true, fillStyle: 'white'};
      drawCircle(cxt, merge(circle1, props));
      drawCircle(cxt, merge(circle2, props));
    });
}

window.onload = draw;
