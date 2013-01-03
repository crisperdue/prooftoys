(function ($) {

  $.fn.tableofcontents = function (options) {
    settings = $.extend({
      // Elements to exclude
      exclude: $(),
    }, options);
    // Use this to assign a unique name to each anchor created.
    var anchor_counter = 1;
    // Level established by a seen header tag.
    var current_level = null;
    // Will contain the HTML text for the TOC.
    var toc_text = "";
      
    // Get the desired header elements.
    $('h1, h2, h3, h4, h5, h6').not(settings.exclude).each (function () {
      header_level = Number(this.tagName.substr(1,1));

      // TODO: Improve the following code to properly handle transitions
      // from level N+2 back to level N, where level N _does_ have an
      // entry in the TOC.  Use a stack of old levels.
      if (!current_level) {
        // Do nothing.
      } else if (current_level < header_level) {
        toc_text += "<ul>";
      } else if (current_level > header_level) {
        toc_text += "</ul></li>";
      } else if (current_level == header_level) {
        toc_text += "</li>";
      }
      // Remember the current level.
      current_level = header_level;

      // Use the ID as the name if it has one, otherwise generate one.
      var toc_name = $(this).attr('id') || 'toc_' + anchor_counter;
      // Plain text of the element.
      header_text = $(this).text();
      // Start a list item.
      toc_text += '<li><a href="#' + toc_name + '">' + header_text + '</a>';

      // Add an anchor before the header element.
      $(this).before('<a name="' + toc_name + '"></a>');
      // Increment the counter in every case.
      anchor_counter++;
    });
    // Add the TOC.
    $(this).append('<ul>' + toc_text + '</ul>');
    return $(this);
  }
}) (jQuery);

