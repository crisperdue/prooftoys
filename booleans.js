// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for booleans.html
//
// Requires canvas.js and logic-pix.js.

var greenCircle = merge(circleCenter,
                        {render: 'fillStroke',
                         fillStyle: '#aea',
                         label: 'green',
                         labelX: 105});

var blueCircle = merge(circleRight,
                       {render: 'fillStroke',
                        fillStyle: '#ddf',
                        label: 'blue',
                        labelX: 125});

var yellowCircle = merge(circleLeft,
                         {render: 'fillStroke',
                          fillStyle: '#ff8',
                          label: 'yellow',
                          labelX: 85});

var circleD = merge(circleLeftish,
                    yellowShading,
                    {label: 'D', labelX: 65});

var circleE = merge(circleRightish,
                    greenShading,
                    {label: 'E', labelX: 145});

// These are like D and E, but don't overlap:
var circleD2 = merge(circleD, {x: 65});

var circleE2 = merge(circleE, {x: 145});

function drawBooleans() {
  // Add shading to all table cells that are "truthy".
  forEach(document.querySelectorAll('td.truthy'), function(elt) {
        elt.style.backgroundImage = 'url(' + shadeBlue.toDataURL() + ')';
      });

  var cxtA = initCxt('canvasA');
  window.cxt = cxtA;
  withinCircle(cxtA, function() {
      render(cxtA, greenCircle);
    });

  var cxtB = initCxt('canvasB');
  withinCircle(cxtB, function() {
      render(cxtB, blueCircle);
    });

  var cxtC = initCxt('canvasC');
  withinCircle(cxtC, function() {
      render(cxtC, yellowCircle);
    });

  // Outside of shape shaded with orange lines.
  var outsideOrange = {outside: true, fillStyle: {image: shadeOrange}};

  var cxtNotA = initCxt('canvasNotA');
  withinCircle(cxtNotA, function() {
      render(cxtNotA, merge(greenCircle, {fillStyle: '#eee'}));
      render(cxtNotA, merge(greenCircle, outsideOrange));
    });

  var cxtNotB = initCxt('canvasNotB');
  withinCircle(cxtNotB, function() {
      render(cxtNotB, merge(blueCircle, {fillStyle: '#eee'}));
      render(cxtNotB, merge(blueCircle, outsideOrange));
    });

  var cxtNotC = initCxt('canvasNotC');
  withinCircle(cxtNotC, function() {
      render(cxtNotC, merge(yellowCircle, {fillStyle: '#eee'}));
      render(cxtNotC, merge(yellowCircle, outsideOrange));
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

  var cxtAndDE = initCxt('canvasAndDE');
  drawAnd(cxtAndDE,
	  merge(circleD, {fillStyle: {image: shadeBlue}}),
	  merge(circleE, {fillStyle: {image: shadeBlue}}));

  var cxtAndDE2 = initCxt('canvasAndDE2');
  drawAnd(cxtAndDE2, circleD2, circleE2);
}

function drawAnd(cxt, circle1, circle2) {
  withinCircle(cxt, function() {
      var noFill = {noFill: true};
      render(cxt, merge(circle1, noFill));
      render(cxt, merge(circle2, noFill));
      withClipping(cxt, circle1, circle2);
    });
}

