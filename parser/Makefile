## ------------------------------------------------------------------------
## SAFIR Coq / parser
## ------------------------------------------------------------------------
##
all: help

help:                ## Show this help
	@sed -ne '/@sed/!s/## //p' $(MAKEFILE_LIST)

##

generate-coq-parser: ## Generate parser
	menhir parser.vy --coq #--coq-no-actions

clean:               ## Clean generated files
	rm -f parser.ml parser.v parser.mli
	corebuild -clean
