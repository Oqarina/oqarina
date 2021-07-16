MENHIR            := menhir
MENHIRFLAGS       := --coq --coq-no-complete

all: aadl_parser.vy
	$(MENHIR) $(MENHIRFLAGS) $<

clean:
	rm -f aadl_parser.v