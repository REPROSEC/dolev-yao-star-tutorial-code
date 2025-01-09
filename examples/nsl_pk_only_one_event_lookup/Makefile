TUTORIAL_HOME ?= ../..

EXAMPLES = nsl_pk_only_one_event_lookup
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; $(FSTAR-EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Example_NSL_Debug.native
	$(TUTORIAL_HOME)/obj/DY_Example_NSL_Debug.native
