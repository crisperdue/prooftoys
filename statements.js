// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for statements.html
//
// Requires logic-pix.js and canvas.js.

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
  forEach(document.querySelectorAll('td.truthy'), function(elt) {
        elt.style.backgroundImage = 'url(' + shadeBlue.toDataURL() + ')';
      });

  // First picture: x > 10 or x < 100.
  var c = initCxt('canvasOrAll');
  withinCircle(c, function() {
      render(c, merge(circleC, {label: 'x < 100', labelX: 55}));
      render(c, merge(circleB, {
	  label: 'x > 10', labelX: 155, fillStyle: {image: shadeYellow}}));
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
      var styleA = {label: 'birds', noFill: true};
      render(c, merge(circleA, styleA));
      var styleC = {label: 'wings', labelX: 170, noFill: true};
      render(c, merge(circleB, styleC));
    });

  // Venn diagram of a false implication, coloring in just the
  // area where the implication is false.
  c = initCxt('canvasNotImplies');
  c.canvas.scrollIntoView();
  withinCircle(c, function() {
      var styleC =
        merge(circleB,
              {shape: circle,
               label: 'wings', labelX: 160,
               noFill: true,
               xfillStyle: '#fff'});
      render(c, styleC);
      var styleA =
        merge(circleA, {x: 85, label: 'birds', fillStyle: '#fff'});
      render(c, styleA);
      withClipping(c, {shape: canvas, fillStyle: 'orange'},
                   merge(styleC, {outside: true}),
                   styleA);
    });

  // Picture where bird --> wings, with normal shading.
  c = initCxt('birdWingsTrue');
  withinCircle(c, function() {
      var styleA =
        {outside: true, label: 'birds', fillStyle: {image: shadeYellow}};
      render(c, merge(circleA, styleA));
      var styleC =
        merge(circleB,
              {label: 'wings', labelX: 170,
               fillStyle: {image: shadeSilver}});
      render(c, styleC);
    });

  // Picture where bird --> wings is not true everywhere, with normal shading.
  c = initCxt('birdWingsFalse');
  withinCircle(c, function() {
      var styleA =
        {outside: true, x: 77, label: 'birds', labelX: 83,
         fillStyle: {image: shadeYellow}};
      render(c, merge(circleA, styleA));
      var styleC =
        merge(circleB,
              {shape: circle, label: 'wings', labelX: 160,
               fillStyle: {image: shadeSilver}});
      render(c, styleC);
    });
}

window.onload = draw;
