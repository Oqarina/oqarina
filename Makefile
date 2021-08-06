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


install_deps:       ## Install dependencies
	opam repo add coq-released
	opam install coq-list-string menhir coq-menhirlib coq-io-system coq-json coq-ext-lib

##

build_makefile:     ## Generate coq makefile
	coq_makefile -f _CoqProject -o coq_makefile
	make generate_parser
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
	$(MAKE) clean build_makefile compile generate_latex pdf

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

distclean:
	-rm -rf html
	-rm extraction/*.ml extraction/*.mli
