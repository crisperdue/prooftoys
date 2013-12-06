// Copyright 2012, 2013 Crispin Perdue.  All rights reserved.
//
// Code for booleans.html
//
// Requires canvas.js and logic-pix.js.

/**
 * Install event handlers to highlight cells in the jquery table
 * element based on mouse position in the canvas relative to the
 * circles.
 */
function installCircleHighlighting(table, canvas, circle1, circle2) {
  var cxt = canvas.getContext('2d');
  canvas.onmousemove = function(event) {
    var p = isInside(cxt, eventPoint(event.target, event), circle1);
    var q = (circle2
             ? isInside(cxt, eventPoint(event.target, event), circle2)
             : false);
    highlightCurrentCell(table, p, q);
  };
  canvas.onmouseout = function(event) {
    table.find('td, th')
      .removeClass('cellHighlight thHighlight');
  };
}

/**
 * Given a jquery table element for a truth table and boolean values
 * for one or two inputs, highlights the matching truth table cell
 * plus its row and column header cells by setting up cellHighlight
 * and thHighlight classes on the TD elements.
 */
function highlightCurrentCell(table, xCircle, yCircle) {
  table.find('td').each(function() {
      var yCell = this.getAttribute('y');
      // Y value is OK if it matches or there is none.
      var yMatch = yCell == null || yCell == '' + yCircle;
      $(this).toggleClass('cellHighlight',
                          yMatch && this.getAttribute('x') === '' + xCircle);
    });
  table.find('th').each(function() {
      $(this).toggleClass('thHighlight',
                          (this.hasAttribute('x')
                           ? this.getAttribute('x') === '' + xCircle
                           : this.getAttribute('y') === '' + yCircle));
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
      render(cxtNotA, merge(greenCircle, {fillStyle: 'white'}));
      render(cxtNotA, merge(greenCircle, outsideOrange));
    });
  var table = $('#negationTable');
  installCircleHighlighting(table, cxtNotA.canvas, greenCircle);

  var cxtNotB = initCxt('canvasNotB');
  withinCircle(cxtNotB, function() {
      render(cxtNotB, merge(blueCircle, {fillStyle: 'white'}));
      render(cxtNotB, merge(blueCircle, outsideOrange));
    });
  installCircleHighlighting(table, cxtNotB.canvas, blueCircle);

  var cxtNotC = initCxt('canvasNotC');
  withinCircle(cxtNotC, function() {
      render(cxtNotC, merge(yellowCircle, {fillStyle: 'white'}));
      render(cxtNotC, merge(yellowCircle, outsideOrange));
    });
  installCircleHighlighting(table, cxtNotC.canvas, yellowCircle);

  var cxtOrDE = initCxt('canvasOrDE');
  withinCircle(cxtOrDE, function() {
      render(cxtOrDE, circleD);
      render(cxtOrDE, circleE);
    });
  var table = $('#disjunctionTable');
  installCircleHighlighting(table, cxtOrDE.canvas, circleD, circleE);

  var cxtOrDE2 = initCxt('canvasOrDE2');
  withinCircle(cxtOrDE2, function() {
      render(cxtOrDE2, merge(circleD, {fillStyle: {image: shadeBlue}}));
      render(cxtOrDE2, merge(circleE, {fillStyle: {image: shadeBlue}}));
    });
  installCircleHighlighting(table, cxtOrDE2.canvas, circleD, circleE);

  var cxtAndDE = initCxt('canvasAndDE');
  drawAnd(cxtAndDE,
	  merge(circleD, {fillStyle: {image: shadeBlue}}),
	  merge(circleE, {fillStyle: {image: shadeBlue}}));
  installCircleHighlighting($('#conjunctionTable'),
                            cxtAndDE.canvas, circleD, circleE);

  var cxtAndDE2 = initCxt('canvasAndDE2');
  drawAnd(cxtAndDE2, circleD2, circleE2);
  installCircleHighlighting($('#conjunctionTable'),
                            cxtAndDE2.canvas, circleD2, circleE2);
}

var birds = {
  shape: circle,
  x: 105, y: 105, radius: 30, fillStyle: {image: shadeYellow},
  label: 'birds'
};

var birds2 = merge(birds, {x: 77, labelX: 83}); // {x: 85, noFill: true});

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
  // var birds2 = merge(birds, {x: 85, noFill: true});
  withinCircle(c, function() {
      render(c, merge(wings, noFillStyle, {labelX: 160}));
      render(c, merge(birds2, noFillStyle));
      withClipping(c, {shape: canvas, fillStyle: 'orange'},
                   merge(wings, {outside: true}),
                   birds2);
    });

  // Picture where bird ==> wings, with normal shading.
  c = initCxt('birdWingsTrue');
  withinCircle(c, function() {
      render(c, merge(birds, {outside: true}));
      render(c, wings);
    });
  installCircleHighlighting($('#implicationTable'),
                            c.canvas, birds, wings);

  // Picture where bird ==> wings is not true everywhere, with normal shading.
  c = initCxt('birdWingsFalse');
  withinCircle(c, function() {
      render(c, merge(birds2, {outside: true}));
      render(c, merge(wings, {labelX: 160}));
    });
  installCircleHighlighting($('#implicationTable'),
                            c.canvas, birds2, wings);
}

function drawCombinations() {
  var c = initCxt('DnandE');
  withinCircle(c, function() {
      render(c, merge(circleD, {outside: true, fillStyle: {image: shadeBlue}}));
      render(c, merge(circleE, {outside: true, fillStyle: {image: shadeBlue}}));
    });
  installCircleHighlighting($('#nandTable'),
                            c.canvas, circleD, circleE);
  c = initCxt('DnorE');
  withinCircle(c, function() {
      drawAnd(c,
              merge(circleD, {outside: true}, blueShading),
              merge(circleE, {outside: true}, blueShading));
    });
  installCircleHighlighting($('#norTable'),
                            c.canvas, circleD, circleE);
}
