## ------------------------------------------------------------------------
## SAFIR Coq
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

##

build_makefile:     ## Generate coq makefile
	coq_makefile -f _CoqProject -o coq_makefile

compile:            ## Compile Coq files
	make -f coq_makefile

validate:           ## Validate proofs in Coq
	make -f coq_makefile validate

.PHONY: html
html:               ## Generate HTML
	make -f coq_makefile html
	cp $(EXTRA_DIR)/resources/* html

generate_latex:     ## Generate LaTeX files from Coq
	coqdoc \
		$(COQDOCFLAGS) --latex  \
		-d latex-src/generated-content -s --body-only -g --interpolate `coqdep -sort $(COQMF_VFILES)`
		mv latex-src/generated-content/*.sty latex-src/

pdf:
	( cd latex-src ; latexmk -pdf techreport.tex )

debug:
	echo $(COQMF_VFILES)

world:              ## All of the above
	$(MAKE) clean build_makefile compile

##

clean:              ## Clean generated files
	-make -f coq_makefile clean
	-rm -f coq_makefile* coq_resources coqdoc.sty *~ .*.aux
	-rm -f latex-src/generated-content/* latex-src/coqdoc.sty
	( cd latex-src ; latexmk -pdf -C techreport.tex )
	( cd latex-src ; rm techreport.bbl)

distclean:
	-rm -rf html
