TUTORIAL_HOME ?= ../..

EXAMPLES = NSL_with_properties
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; $(FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_NSLP_Run.native
	$(TUTORIAL_HOME)/obj/DY_NSLP_Run.native
