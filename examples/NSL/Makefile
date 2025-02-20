TUTORIAL_HOME ?= ../..

EXAMPLES = NSL
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; $(FSTAR_EXE) --ocamlenv ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_NSL_Run.native
	$(TUTORIAL_HOME)/obj/DY_NSL_Run.native
