TUTORIAL_HOME ?= ../..

EXAMPLES = Online
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; $(FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_Online_Run.native
	$(TUTORIAL_HOME)/obj/DY_Online_Run.native
