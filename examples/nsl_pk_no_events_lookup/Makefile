TUTORIAL_HOME ?= ../..

EXAMPLES = nsl_pk_no_events_lookup
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_OnlineS_Run.native
	$(TUTORIAL_HOME)/obj/DY_OnlineS_Run.native
