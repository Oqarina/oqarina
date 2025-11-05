# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))

# sys.path.insert(0, os.path.abspath('../../src')).


# -- Project information -----------------------------------------------------

project = 'oqarina'
#copyright = '2021, J. Hugues'
#author = 'J. Hugues'

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = [
    "alectryon.sphinx", # Added Alectryon
    "sphinx.ext.mathjax",
    'sphinx.ext.autosectionlabel',
    "sphinxcontrib.bibtex"
]

bibtex_bibfiles = ['bibliography.bib']

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = ['_build', 'Thumbs.db', '.DS_Store']

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
html_theme = 'alabaster'

html_theme_options = {
    'page_width': '80%',
   'show_powered_by' : 'False',
   'fixed_sidebar' : 'True',
}

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

# -- Options for LaTeX output ------------------------------------------------

latex_additional_files = [
    'alectryon.sty',
]

latex_elements = {
    # The paper size ('letterpaper' or 'a4paper').
    'papersize': 'a4paper',

    # The font size ('10pt', '11pt' or '12pt').
    'pointsize': '10pt',

    # Additional stuff for the LaTeX preamble.
    'preamble': r'''
   \usepackage{standalone}
    \usepackage{sphinx}
    \DeclareUnicodeCharacter{3B4}{$\delta$}
        \DeclareUnicodeCharacter{3B5}{$\varepsilon$}
    \DeclareUnicodeCharacter{3BB}{$\lambda$}
    \DeclareUnicodeCharacter{2264}{$\leq$}
    \DeclareUnicodeCharacter{2208}{$\in$}

''',

}

# -- Alectryon configuration -------------------------------------------------

import alectryon.docutils
alectryon.docutils.CACHE_DIRECTORY = "_build/alectryon/"
alectryon.docutils.LONG_LINE_THRESHOLD = 100

# Point to a fresh build of Oqarina
alectryon.docutils.AlectryonTransform.SERTOP_ARGS = ("-Q", "../_build/default/src,Oqarina")

# -- MathJax configuration ---------------------------------------------------

from sphinx.ext import mathjax
mathjax.MATHJAX_URL = alectryon.docutils.HtmlTranslator.MATHJAX_URL # MathJax 3

# This configuration is explained in recipes/mathjax.rst
# Use either this (Sphinx ≥ 4.0 only):

html_js_files = ['mathjax_config.js']
mathjax_options = { "priority": 1000 }

# or this (but inline the configuration instead of open(…).read()):

from pathlib import Path
html_js_files = [
    (None, {
        "body": Path("_static/mathjax_config.js").read_text(),
        "priority": 0
    })
]

# or this:

html_js_files = [('mathjax_config.js', { "priority": 0 })]
