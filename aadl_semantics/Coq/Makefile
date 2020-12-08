##------------------------------------------------------------------------
## SAFIR Coq
##------------------------------------------------------------------------
##

all: help

help:               ## Show this help
	    @sed -ne '/@sed/!s/##//p' $(MAKEFILE_LIST)

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

world:              ## All of the above
	$(MAKE) clean build_makefile compile

##

clean:              ## Clean generated files
	-make -f coq_makefile clean
	-rm -f coq_makefile* coq_resources coqdoc.sty *~ .*.aux