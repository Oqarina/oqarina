OQARINA_BIN = ../_build/default/extraction/extraction.native

TEST_FILES = car.impl.json rma.impl.json system_mini.impl.json

test:
	@for file in $(TEST_FILES); do \
		$(OQARINA_BIN) --parse $$file ; \
	done