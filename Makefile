## ------------------------------------------------------------------------
## Oqarina -- Coq mechanization of AADL
## ------------------------------------------------------------------------
##

all: help

help:               ## Show this help
	    @sed -ne '/@sed/!s/## //p' $(MAKEFILE_LIST)

# -----------------------------------------------------------------------------
# * Management of dependencies: Coq libraries can be installed through
#   opam. We provide two targets:
#   - install_deps installs required libraries to use Oqarina from a Coq IDE
#

install_deps:       ## Install dependencies
	opam repo add coq-released --all-switches https://coq.inria.fr/opam/released
	opam repo add coq-extra-dev --all-switches https://coq.inria.fr/opam/extra-dev
	opam install --deps-only .

# -----------------------------------------------------------------------------
# * Build system: we support two approaches
#   - using _CoqProject, for inclusion with Coq IDE
#   - using Dune, for packaging
#
# _CoqProject build is no longer supported. To resurrect it, copy _CoqProject.
# legacy to _CoqProject, and eventually manually update any missing elements.

build_makefile:
	coq_makefile -f _CoqProject -o coq_makefile

install:            ## Install Oqarina as a stand alone Coq library
	dune install

compile:
	make -f coq_makefile

build:              ## Build
	dune build

build_bin:          ## Build Oqarina binary
	( cd _build/default/extraction  ; ocamlbuild extraction.native -lib unix )

test:               ## Run testsuite
	make -C testsuite test

# -----------------------------------------------------------------------------
# Documentation generation
#

.PHONY: html

# We use alectryon ( https://github.com/cpitclaudel/alectryon ) to
# generate documentation from a subset of the Coq code base. Alectryon supports
# rst syntax which provides more flexibilty to generate either a PDF or HTML
# pages

ALECTRYON_FILES=src/formalisms/all.v src/formalisms/lts.v \
	src/formalisms/DEVS/classic/all.v \
	src/formalisms/DEVS/classic/devs.v \
	src/formalisms/DEVS/classic/coupled.v \
	src/AADL/all.v \
	src/AADL/Kernel/categories.v \
	src/AADL/Kernel/component.v \
	src/AADL/behavior/thread.v \
	src/AADL/behavior/port_variable.v \
	src/AADL/behavior/system.v \
	src/AADL/resolute/resolute.v \
	examples/AADL/full_example.v \
	examples/3rd-party/aadl2prosa.v

alectryon:
	DOCUTILSCONFIG=docs/docutils.conf \
	alectryon --coq-driver sertop -Q _build/default/src Oqarina \
		--long-line-threshold 150 \
		--frontend coq+rst --backend rst  \
		$(ALECTRYON_FILES)
	(cd src ; find */ -type f  -name "*.v.rst" -exec bash -c 'file=$${1#./}; mv "$$file" ../docs/coq/"$${file//\//_}"' _ '{}' \; )
	(cd examples ; find */ -type f  -name "*.v.rst" -exec bash -c 'file=$${1#./}; mv "$$file" ../docs/coq/"$${file//\//_}"' _ '{}' \; )
	gsed -i -e '/(\*\*\*/,/\*\*\*)/d' docs/coq/*.v.rst

html:               ## Build HTML documentation
	( cd docs; make html )

pdf:                ## Build LaTeX documentation
	( cd docs ; make latexpdf )

COQ_FILES = $(shell find src/ -type f -name '*.v')
sloc:               ## Get SLOCs
	@coqwc $(COQ_FILES)

world:              ## All of the above
	$(MAKE) clean distclean build alectryon html pdf

build_docker:	    ## Build docker image for testing
	docker build -t safir/coq .

test_build_docker:  ## Test build using docker
	$(MAKE) clean distclean
	docker run -ti  -v `pwd`:/work oqarina/oqarina make dune_build

# -----------------------------------------------------------------------------
# Cleaning rules

clean:              ## Clean generated files
	-$(MAKE) -f coq_makefile clean
	-rm -f coq_makefile* coq_resources coqdoc.sty *~ .*.aux
	-rm -rf _build
	-rm -f latex-src/generated-content/* latex-src/coqdoc.sty
	-( cd latex-src ; latexmk -pdf -C techreport.tex )
	-( cd latex-src ; rm techreport.bbl)
	-(cd docs ; rm *.v.rst* *,bak )
	$(MAKE) -C extraction clean
	-rm -rf src/**/*.vo deps.dot* deps.png
	find . -type f -name '.*.aux' -exec rm {} +

distclean:          ## Distclean
	$(MAKE) clean
	-rm -rf html coq-oqarina.opam .lia.cache
	-rm extraction/*.ml extraction/*.mli main.ml*
	-rm -rf coq-ocarina*

# -----------------------------------------------------------------------------
# License management
#
# See https://github.com/jjhugues/licenseheaders for an adaptation of
# the licenseheaders.py script to support Coq.
#

.PHONY: update_license
update_license:     ## Update all license headers
	python3 `which licenseheaders.py` -t tools/license-header.txt -cy -d src
	python3 `which licenseheaders.py` -t tools/license-header.txt -cy -d extraction

deps.dot: _CoqProject
	tools/deps.sh > deps.dot-
	grep -v coq_utils deps.dot- > deps.dot
	grep -v core deps.dot > deps.dot-
	mv deps.dot- deps.dot

deps.png: deps.dot
	dot -T png deps.dot > deps.png

# -----------------------------------------------------------------------------
# Packaging
#

PKG_NAME=coq-ocarina-0.0.1
FILES=$(shell gls --ignore="$(PKG_NAME)*" --ignore=latex-src .)

package:            ## Build package
	rm -rf mkdir $(PKG_NAME)
	mkdir $(PKG_NAME)
	cp -r $(FILES) $(PKG_NAME)
	tar zcvf $(PKG_NAME).tar.gz $(PKG_NAME)
