SUBDIRS=car rma

all:
	@for dir in $(SUBDIRS); do \
		($(MAKE) -C $${dir}) || exit 1;  \
	done

distclean:
	for dir in $(SUBDIRS); do \
		($(MAKE) -C $${dir} distclean) || exit 1;  \
	done
	rm *~
