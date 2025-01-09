TUTORIAL_HOME ?= ../..

EXAMPLES = Online_with_secrecy
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; $(FSTAR-EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_OnlineS_Run.native
	$(TUTORIAL_HOME)/obj/DY_OnlineS_Run.native
