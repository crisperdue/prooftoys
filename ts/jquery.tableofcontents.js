(function ($) {

  'use strict';

  // @ts-expect-error
  $.fn.tableofcontents = function (options) {
    const settings = $.extend({
      // Elements to exclude
      exclude: ({}),
    }, options);
    // Use this to assign a unique name to each anchor created.
    var anchor_counter = 1;
    // Level established by a seen header tag.
    var current_level = 1;
    // Level of first seen header tag.
    var base_level = 1;
    // Will contain the HTML text for the TOC.
    var toc_html = "";
      
    // Get the desired header elements.
    $('h1, h2, h3, h4, h5, h6').not(settings.exclude).each (function () {
      let header_level = Number(this.tagName.substr(1,1));
      // Establish the base level from the first seen heading.
      if (!base_level) {
        base_level = header_level;
        current_level = base_level;
      }
      // Adjust the level to be at least the base.
      if (header_level < base_level) {
        header_level = base_level;
      }
      // Start or end lists to reach the level of this heading.
      while (current_level < header_level) {
        toc_html += '<ul>';
        current_level++;
      }
      while (current_level > header_level) {
        toc_html += '</ul>';
        current_level--;
      }

      // Get the HTML contents of the heading.
      const header_html = $(this).html();
      // Use the ID as the name if it has one, otherwise generate one.
      var toc_name = $(this).attr('id') || 'toc_' + anchor_counter;
      // Add a list item with that text and a link to the named anchor.
      // TODO: properly escape the header text.
      toc_html += '<li><a href="#' + toc_name + '">' + header_html + '</a>';

      // Add an anchor before the header element.
      $(this).before('<a name="' + toc_name + '"></a>');
      // Increment the counter in every case.
      anchor_counter++;
    });
    while (current_level-- > base_level) {
      toc_html += '</ul>';
    }
    // Add the TOC.
    $(this).append('<ul>' + toc_html + '</ul>');
    return $(this);
  }
}) (jQuery);

