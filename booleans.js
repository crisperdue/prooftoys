// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for booleans.html
//
// Requires canvas.js and logic-pix.js.

// Suppress loading of YUI in booleans.html.
window.noYUI = true;

/**
 * Missing jQuery utility function.
 */
function setClass(j, className, value) {
  if (value) {
    j.addClass(className);
  } else {
    j.removeClass(className);
  }
}

/**
 * Given a TABLE element of a truth table and boolean values for one
 * or two inputs, highlights the matching truth table cell plus its
 * row and column header cells by setting up cellHighlight and
 * thHighlight classes on the TD elements.
 */
function highlightCurrentCell(table, xCircle, yCircle) {
  table.find('td').each(function() {
      var yCell = this.getAttribute('y');
      // Y value is OK if it matches or there is none.
      var yMatch = yCell == null || yCell == '' + yCircle;
      setClass($(this),
               'cellHighlight',
               yMatch && this.getAttribute('x') == '' + xCircle);
    });
  table.find('th').each(function() {
      setClass($(this), 'thHighlight',
               (this.hasAttribute('x')
                ? this.getAttribute('x') == '' + xCircle
                : this.getAttribute('y') == '' + yCircle));
    });
}

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

function drawAnd(cxt, circle1, circle2) {
  withinCircle(cxt, function() {
      var noFill = {noFill: true};
      render(cxt, merge(circle1, noFill));
      render(cxt, merge(circle2, noFill));
      withClipping(cxt, circle1, circle2);
    });
}

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

  var byId = function(id) { return document.getElementById(id); };
  var dSpan = byId('inD');
  var eSpan = byId('inE');
  var spanOr = byId('inDOrE');
  var spanAnd = byId('inDAndE');
  var cxtOrDE = initCxt('canvasOrDE');
  cxtOrDE.canvas.onmousemove = function(event) {
    var d = isInside(cxt, eventPoint(cxtOrDE.canvas, event), circleD);
    var e = isInside(cxt, eventPoint(cxtOrDE.canvas, event), circleE);
    var table = $('table.disjunction1');
    highlightCurrentCell(table, d, e, d || e);
  };
  cxtOrDE.canvas.onmouseout = function(event) {
    $('table.disjunction1 td, table.disjunction1 th')
      .removeClass('cellHighlight thHighlight');
  };
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

var birds = {
  shape: circle,
  x: 105, y: 105, radius: 30, fillStyle: {image: shadeYellow},
  label: 'birds'
};

var wings = {
  shape: circle,
  x: 225, y: 105, radius: 160, fillStyle: {image: shadeGreen},
  label: 'wings', labelX: 170,
};

/**
 * Draws the picture suggested by the name.
 */
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
    fillStyle: {image: shadeGreen},
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

function drawStatements() {
  forEach(document.querySelectorAll('td.truthy'), function(elt) {
        elt.style.backgroundImage = 'url(' + shadeBlue.toDataURL() + ')';
      });

  // First picture: x > 10 or x < 100.
  var circle1 = {
    shape: circle,
    x: -15, y: 105, radius: 160, fillStyle: {image: shadeYellow},
    label: 'x < 100', labelX: 55
  };
  var c = initCxt('canvasOrAll');
  withinCircle(c, function() {
      render(c, circle1);
      render(c, merge(wings, {label: 'x > 10', labelX: 155}));
    });

  // Arrows.
  twoArrowsAndNumberLine();

  c = initCxt('canvasAnd');
  withinCircle(c, function() {
      var overrides = {fillStyle: {image: shadeBlue}, label: 'A and B'};
      var style2 =
        {shape: circle, x: cx, y: cy, radius: r, label: 'A and B',
         fillStyle: {image: shadeBlue}};
      render(c, style2);
    });

  // Venn diagram of an implication.
  c = initCxt('canvasImplies');
  withinCircle(c, function() {
      render(c, merge(birds, noFillStyle));
      render(c, merge(wings, noFillStyle));
    });

  // Venn diagram of a false implication, coloring in just the
  // area where the implication is false.
  c = initCxt('canvasNotImplies');
  withinCircle(c, function() {
      render(c, merge(wings, noFillStyle, {labelX: 160}));
      var birds2 = merge(birds, {x: 85, noFill: true});
      render(c, birds2);
      withClipping(c, {shape: canvas, fillStyle: 'orange'},
                   merge(wings, {outside: true}),
                   birds2);
    });

  // Picture where bird --> wings, with normal shading.
  c = initCxt('birdWingsTrue');
  withinCircle(c, function() {
      render(c, merge(birds, {outside: true}));
      render(c, wings);
    });

  // Picture where bird --> wings is not true everywhere, with normal shading.
  c = initCxt('birdWingsFalse');
  withinCircle(c, function() {
      render(c, merge(birds, {outside: true, x: 77, labelX: 83}));
      render(c, merge(wings, {labelX: 160}));
    });
}

