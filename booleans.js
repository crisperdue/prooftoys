// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for booleans.html
//
// Requires canvas.js and logic-pix.js.

var circleA = merge(circleCenter,
                    silverShading,
                    {render: 'fillStroke', label: 'A', labelX: 105});

var circleB = merge(circleRight,
                    blueShading,
                    {label: 'B', labelX: 125});

var circleC = merge(circleLeft,
                    yellowShading,
                    {label: 'C', labelX: 85});

var circleD = merge(circleLeftish,
                    yellowShading,
                    {label: 'D', labelX: 65});

var circleE = merge(circleRightish,
                    silverShading,
                    {label: 'E', labelX: 145});

// These are like D and E, but don't overlap:
var circleD2 = merge(circleD, {x: 65});

var circleE2 = merge(circleE, {x: 145});

function draw() {
  // Add shading to all table cells that are "truthy".
  forEach(document.querySelectorAll('td.truthy'), function(elt) {
        elt.style.backgroundImage = 'url(' + shadeBlue.toDataURL() + ')';
      });

  var cxtA = initCxt('canvasA');
  window.cxt = cxtA;
  withinCircle(cxtA, function() {
      render(cxtA, circleA);
    });

  var cxtB = initCxt('canvasB');
  withinCircle(cxtB, function() {
      render(cxtB, circleB);
    });

  var cxtC = initCxt('canvasC');
  withinCircle(cxtC, function() {
      render(cxtC, circleC);
    });

  // Outside of shape shaded with blue lines.
  var outsideBlue = {outside: true, fillStyle: {image: shadeBlue}};

  var cxtNotA = initCxt('canvasNotA');
  withinCircle(cxtNotA, function() {
      render(cxtNotA, merge(circleA, {fillStyle: '#eee'}));
      render(cxtNotA, merge(circleA, outsideBlue));
    });

  var cxtNotB = initCxt('canvasNotB');
  withinCircle(cxtNotB, function() {
      render(cxtNotB, merge(circleB, {fillStyle: '#eee'}));
      render(cxtNotB, merge(circleB, outsideBlue));
    });

  var cxtNotC = initCxt('canvasNotC');
  withinCircle(cxtNotC, function() {
      render(cxtNotC, merge(circleC, {fillStyle: '#eee'}));
      render(cxtNotC, merge(circleC, outsideBlue));
    });

  var cxtOrDE = initCxt('canvasOrDE');
  withinCircle(cxtOrDE, function() {
      render(cxtOrDE, circleD);
      render(cxtOrDE, circleE);
    });

  var cxtOrDE2 = initCxt('canvasOrDE2');
  withinCircle(cxtOrDE2, function() {
      render(cxtOrDE2, merge(circleD, {fillStyle: {image: shadeBlue}}));
      render(cxtOrDE2, merge(circleE, {fillStyle: {image: shadeBlue}}));
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
      render(cxt, merge(circle1, props));
      render(cxt, merge(circle2, props));
    });
}

window.onload = draw;
