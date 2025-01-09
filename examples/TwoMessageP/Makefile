TUTORIAL_HOME ?= ../..

EXAMPLES = TwoMessageP
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; $(FSTAR-EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_TwoMessage_Run.native
	$(TUTORIAL_HOME)/obj/DY_TwoMessage_Run.native
