## ------------------------------------------------------------------------
## Oqarina -- Coq mechanization of AADL
## ------------------------------------------------------------------------
##

EXTRA_DIR:=extra
COQDOCFLAGS:= \
  --external 'http://ssr2.msr-inria.inria.fr/doc/ssreflect-1.5/' Ssreflect \
  --external 'http://ssr2.msr-inria.inria.fr/doc/mathcomp-1.5/' MathComp \
  --toc --toc-depth 2 --html --interpolate \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(EXTRA_DIR)/header.html --with-footer $(EXTRA_DIR)/footer.html
export COQDOCFLAGS

-include coq_makefile.conf

all: help

help:               ## Show this help
	    @sed -ne '/@sed/!s/## //p' $(MAKEFILE_LIST)

install_deps:       ## Install dependencies (no extraction)
	opam repo add coq-released --all-switches https://coq.inria.fr/opam/released
	opam repo add coq-extra-dev --all-switches https://coq.inria.fr/opam/extra-dev
	opam install -y coq-ext-lib menhir coq-menhirlib coq-json

install_deps_bin:   ## Install dependencies (extraction)
	$(MAKE) install_deps
	opam install -y coq-io-system

##

build_makefile:     ## Generate coq makefile
	coq_makefile -f _CoqProject -o coq_makefile
	$(MAKE) generate_parser
	mkdir -p extraction/generated-src

install:            ## Install Oqarina as a stand alone Coq library
	make -f coq_makefile install

generate_parser:
	make -C src/AADL/atin_frontend

compile:            ## Compile Coq files
	make -f coq_makefile

build_bin:          ## Build Oqarina binary
	make -C extraction

validate:           ## Validate proofs in Coq
	make -f coq_makefile validate

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
	docker run -ti  -v `pwd`:/work safir/coq make install_deps generate_parser dune_build

dune_build:         ## Build using dune
	dune build

##

clean:              ## Clean generated files
	-make -f coq_makefile clean
	-rm -f coq_makefile* coq_resources coqdoc.sty *~ .*.aux
	-rm -f latex-src/generated-content/* latex-src/coqdoc.sty
	( cd latex-src ; latexmk -pdf -C techreport.tex )
	-( cd latex-src ; rm techreport.bbl)
	make -C extraction clean
	make -C src/AADL/atin_frontend clean
	-rm -rf src/**/*.vo
	find . -type f -name '.*.aux' -exec rm {} +

distclean:
	-rm -rf html
	-rm extraction/*.ml extraction/*.mli
