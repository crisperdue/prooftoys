// Copyright Crispin Perdue.  All rights reserved.

// This file gives a bit of an alternative to static
// site generation.  It generates standard page content
// that would otherwise be repeated in various files.

(function() {
  // Try the HTML5 way, otherwise look for a script
  // named boilerplate.js.
  var element = document.currentScript
    || document.querySelector('script[src$="boilerplate.js"]');
  var src = element.getAttribute('src');
  // URL of this script, up to the actual name:
  var prefix = src.replace(/boilerplate.js$/, '');

  function write(html) {
    document.write(html);
  }

  // Fortunately browsers seem to cancel out the prefix and initial
  // ".." in names.
  function getScript(name) {
    document.write('<script src="' + prefix + name + '"></script>');
  }

  // Include jQuery in all cases.
  write('<script src="https://code.jquery.com/jquery-3.6.0.js"></script>');

  write('<link rel=stylesheet href=' +
        '"https://fonts.googleapis.com/css?family=Roboto' +
        ':400,400i,700,700i">');

  // Include Font Awesome.
  write('<link rel="stylesheet" href=' +
        '"https://maxcdn.bootstrapcdn.com/font-awesome/4.7.0/css/font-awesome.css">');

  // Behavior can be customized by this global variable.
  if (!window.noTooltipster) {

    const tipster = 'tipster-4.2.5/';

    // These load Tooltipster and the light theme from current locations
    // in the source tree.
    write('<link rel="stylesheet" href="' + tipster +
          'css/tooltipster.bundle.css">');
    write('<link rel="stylesheet" href="' + tipster +
          'css/plugins/tooltipster/sideTip' +
          '/themes/tooltipster-sideTip-shadow.min.css">');
    write('<script src="' + tipster + 'js/tooltipster.bundle.js' +
          '"></script>');
  }

  // Include the application's styles _after_ tooltipster so its
  // styles override tooltipster.
  write('<link rel="stylesheet" href="../css/logic.css">');

  // Loading of scripts can be customized by this global variable.
  if (!window.noProofScripts) {
    getScript('site.js');
    getScript('util.js');
    getScript('prelim.js');
    getScript('expr.js');
    getScript('xutil.js');
    getScript('step-editor.js');
    getScript('rendering.js');
    getScript('solution-status.js');
    getScript('engine.js');
    getScript('logic.js');
    getScript('numbers.js');
  }
})();
