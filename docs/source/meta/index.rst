About this documentation
========================

..
  - organised according to Diátaxis Framework https://diataxis.fr/, see also https://www.youtube.com/watch?v=t4vKPhjcMZg
  - technically uses Sphinx, all written with reStructured and MyST markdown dialect https://myst-parser.readthedocs.io/
  - markdown parts are meant to be written in literate Idris https://idris2.readthedocs.io/en/latest/reference/literate.html#commonmark
    - these parts are tested to build successully with the current state of the library
    - only code blocks are checked during this check, inline Idris snippets are treated as comments
    - although, small letter filenames are meant to be used, fully qualified module name (if used) should use capitalised names,
      as Idris would expect; there is some machinery that capitalises file and dir names during docs testing

.. toctree::
  :maxdepth: 1
  :caption: Contents:
  :hidden:

  test
