## ------------------------------------------------------------------------
## Oqarina -- Coq mechanization of AADL
## ------------------------------------------------------------------------
##

EXTRA_DIR:=extra

COQDOCFLAGS:= \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

-include coq_makefile.conf

all: help

help:               ## Show this help
	    @sed -ne '/@sed/!s/## //p' $(MAKEFILE_LIST)

# -----------------------------------------------------------------------------
# * Management of dependencies: Coq libraries can be instaleld through
#   opam. We provide two targets:
#   - install_deps installs required libraries to use Oqarina from a Coq IDE
#   - install_deps_bin instalels additional libraries for code extraction
#

install_deps:       ## Install dependencies (no extraction)
	opam repo add coq-released --all-switches https://coq.inria.fr/opam/released
	opam repo add coq-extra-dev --all-switches https://coq.inria.fr/opam/extra-dev
	opam install -y coq-ext-lib menhir coq-menhirlib coq-json

install_deps_bin:   ## Install dependencies (extraction)
	$(MAKE) install_deps
	opam install -y coq-io-system

# -----------------------------------------------------------------------------
# * Build system: we support two approaches
#   - using _CoqProject, for inclusion with Coq IDE
#   - using Dune, for packaging
#

build_makefile:     ## Generate coq makefile
	coq_makefile -f _CoqProject -o coq_makefile
	$(MAKE) generate_parser
	mkdir -p extraction/generated-src

install:            ## Install Oqarina as a stand alone Coq library
	make -f coq_makefile install

# This (obsolete) target generates menhir parser. It is kept to serve
# as proof of concept and might be removed

generate_parser:
	make -C src/AADL/atin_frontend

compile:            ## Compile Coq files
	make -f coq_makefile

dune_build:         ## Build using dune
	dune build

build_bin:          ## Build Oqarina binary
	make -C extraction

validate:           ## Validate all proofs
	make -f coq_makefile validate

# -----------------------------------------------------------------------------
# Documentation generation
#

.PHONY: html
html:               ## Generate HTML
	make -f coq_makefile html
	cp $(EXTRA_DIR)/resources/* html

generate_latex:     ## Generate LaTeX files from Coq
	-mkdir latex-src/generated-content
	coqdoc \
		$(COQDOCFLAGS) --latex  \
		-d latex-src/generated-content -s --body-only -g --interpolate `coqdep -sort $(COQMF_VFILES)`
		mv latex-src/generated-content/*.sty latex-src/

pdf:                ## Build tech report
	( cd latex-src ; latexmk -pdf techreport.tex )

sloc:               ## Get SLOCs
	cloc src extraction

debug:
	echo $(COQMF_VFILES)

world:              ## All of the above
	$(MAKE) clean distclean build_makefile compile generate_latex pdf

build_docker:	    ## Build docker image for testing
	docker build -t safir/coq .

test_build_docker:  ## Test build using docker
	$(MAKE) clean distclean
	docker run -ti  -v `pwd`:/work safir/coq make generate_parser dune_build

# -----------------------------------------------------------------------------
# Cleaning rules

clean:              ## Clean generated files
	-$(MAKE) -f coq_makefile clean
	-rm -f coq_makefile* coq_resources coqdoc.sty *~ .*.aux
	-rm -rf _build
	-rm -f latex-src/generated-content/* latex-src/coqdoc.sty
	( cd latex-src ; latexmk -pdf -C techreport.tex )
	-( cd latex-src ; rm techreport.bbl)
	$(MAKE) -C extraction clean
	$(MAKE) -C src/AADL/atin_frontend clean
	-rm -rf src/**/*.vo deps.dot* deps.png
	find . -type f -name '.*.aux' -exec rm {} +

distclean:          ## Distclean
	$(MAKE) clean
	-rm -rf html coq-oqarina.opam
	-rm extraction/*.ml extraction/*.mli

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
