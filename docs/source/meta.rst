.. role:: idris(code)
   :language: idris

========================
About this documentation
========================

This documentation is organised using the following principles.

- Documentation is organised according to the `Diátaxis Framework <https://diataxis.fr/>`_
  with clear distinction between several parts according to the goals of
  `learning <https://diataxis.fr/tutorials/>`_,
  `solving particular problems <https://diataxis.fr/how-to-guides/>`_,
  `referencing during programming <https://diataxis.fr/reference/>`_
  and `understanding the library <https://diataxis.fr/explanation/>`_.
  You can watch a `wonderful talk by Daniele Procida <https://www.youtube.com/watch?v=t4vKPhjcMZg>`_ about such documentation organisation.

- Documentation technically uses `Sphinx <https://www.sphinx-doc.org/>`_.
  All material is written in `reStructuredTest <https://www.sphinx-doc.org/en/master/usage/restructuredtext/basics.html>`_
  and `MyST markdown dialect <https://myst-parser.readthedocs.io/>`_.

- All sections of the documentation containing compilable code are meant to be written in
  `literate Idris <https://idris2.readthedocs.io/en/latest/reference/literate.html#commonmark>`_.

  - These parts are tested to be built successfully against the current state of the library.
  - Markdown mode of literate Idris is used because it is the only common format supported both by Sphinx and Idris.
  - Only code blocks are checked during this test, inline snippets like :idris:`the (Vect 3 Nat) [1, 2, 3]` are not checked.
  - Although, small letter filenames are meant to be used,
    fully qualified module name (if used) should use capitalised names, as Idris would expect,
    There is some machinery that capitalises file and directory names during docs testing.
    You can look at :ref:`this section <sect-literate-sample>` for the example.

This documentation is likely to be not yet full.
There are a lot of places still to be filled.
You can look at the list of places that are marked as "todos" :any:`here <meta/todos>`.

.. toctree::
  :hidden:

  meta/test
  meta/todos
