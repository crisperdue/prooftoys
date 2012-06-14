// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for canvas-test.html

var cx = 105, cy = 105;
var r = 100;
var aRadius = 30;
var bRadius = 150;
var blue25 = 'hsla(240, 100%, 50%, 1)';
var green25 = 'hsla(120, 100%, 30%, 1)';
var red25 = 'hsla(10, 100%, 50%, 1)';

var labels = [];

function initCxt(canvas) {
  if (typeof canvas == 'string') {
    canvas = document.getElementById(canvas);
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

function pattern(element) {
  return function(cxt) { return cxt.createPattern(element, 'repeat'); };
}

////
//// Page-specific code
////

var circleA = function() {
  var canvas = document.createElement('canvas');
  canvas.width = 10;
  canvas.height = 10;
  var cxt = initCxt(canvas);
  cxt.strokeStyle = 'green';
  cxt.lineWidth = 1.4;
  cxt.lineCap = 'square';
  cxt.moveTo(0, 5);
  cxt.lineTo(5, 0);
  cxt.stroke();
  cxt.moveTo(5, 10);
  cxt.lineTo(10, 5);
  cxt.stroke();
  return {
    x: 105, y: 105, radius: 30, fillStyle: {image: canvas},
    label: 'A', labelX: 105
  };
}();

var circleB = function() {
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
  return {
    x: 205, y: 105, radius: 150, fillStyle: {image: canvas},
    label: 'B', labelX: 175
  };
}();


var circleC = function() {
  var canvas = document.createElement('canvas');
  canvas.width = 10;
  canvas.height = 10;
  var cxt = initCxt(canvas);
  cxt.strokeStyle = 'yellow';
  cxt.lineWidth = 1.4;
  cxt.lineCap = 'square';
  cxt.moveTo(0, 5);
  cxt.lineTo(5, 10);
  cxt.stroke();
  cxt.moveTo(5, 0);
  cxt.lineTo(10, 5);
  cxt.stroke();
  return {
    x: 5, y: 105, radius: 150, fillStyle: {image: canvas},
    label: 'C', labelX: 35
  };
}();  


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


  var cxtOr = initCxt('canvasOr');
  window.cxtOr = cxtOr;
  withinCircle(cxtOr, function() {
      drawCircle(cxtOr, circleA);
      drawCircle(cxtOr, circleB);
    });

  var cxtOrBC = initCxt('canvasOrBC');
  withinCircle(cxtOrBC, function() {
      drawCircle(cxtOrBC, circleB);
      drawCircle(cxtOrBC, circleC);
    });

  var cxtAnd = initCxt('canvasAnd');
  window.cxtAnd = cxtAnd;
  drawAnd(cxtAnd, circleA, circleB);

  var cxtAndBC = initCxt('canvasAndBC');
  drawAnd(cxtAndBC, circleB, circleC);

  var cxtAll = initCxt('canvasAll');
  drawAll(cxtAll);

  var cxtImplies = initCxt('canvasImplies');
  window.cxtImplies = cxtImplies;
  drawImplies(cxtImplies);
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
      mergeFillStyle(cxt, circle1);
      drawAll(cxt);
      mergeFillStyle(cxt, circle2);
      drawAll(cxt);
      cxt.restore();
      var props = {outside: true, fillStyle: 'white'};
      drawCircle(cxt, merge(circle1, props));
      drawCircle(cxt, merge(circle2, props));
    });
}

function drawImplies(cxt) {
  withinCircle(cxt, function() {
      drawCircle(cxt, merge(circleA, {outside: true}));
      drawCircle(cxt, circleB);
    });
}

window.onload = draw;
