MENHIR            := menhir
MENHIRFLAGS       := --coq --coq-no-complete

all: atin_parser.vy
	$(MENHIR) $(MENHIRFLAGS) $<

clean:
	-rm -f atin_parser.v