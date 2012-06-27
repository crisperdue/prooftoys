// Copyright 2012 Crispin Perdue.  All rights reserved.
//
// Code for statements.html
//
// Requires logic-pix.js and canvas.js.

var birds = {
  shape: circle,
  x: 105, y: 105, radius: 30, fillStyle: {image: shadeYellow},
  label: 'birds'
};

var wings = {
  shape: circle,
  x: 225, y: 105, radius: 160, fillStyle: {image: shadeSilver},
  label: 'wings', labelX: 170,
};

/**
 * Draw a right arrow of unit length and width specified by
 * info.width, which defaults to .1, along the X axis from the origin.
 *
 * TODO: Parameterize at least by length, so the arrowhead does not
 * get stretched by scaling.
 */
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
  c.canvas.scrollIntoView();
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
