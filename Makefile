DY_HOME ?= ../../..

EXAMPLES = nsl_pk_no_events_lookup simple/TwoMessageP simple/Online
EXAMPLE_DIRS = $(addprefix examples/, $(EXAMPLES))
include $(DY_HOME)/Makefile