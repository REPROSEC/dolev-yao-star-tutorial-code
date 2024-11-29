TUTORIAL_HOME ?= ../..

EXAMPLES = Online_with_authn
EXAMPLE_DIRS = $(addprefix $(TUTORIAL_HOME)/examples/, $(EXAMPLES))

include $(TUTORIAL_HOME)/Makefile

test:
	cd $(TUTORIAL_HOME)/obj; OCAMLPATH=$(FSTAR_HOME)/lib:$(OCAMLPATH) ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib DY_OnlineA_Run.native
	$(TUTORIAL_HOME)/obj/DY_OnlineA_Run.native
