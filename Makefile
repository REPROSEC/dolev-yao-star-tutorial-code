Z3 		?= $(shell which z3)
FSTAR_HOME 	?= $(dir $(shell which fstar.exe))/..
TUTORIAL_HOME   ?= .
DY_HOME 	?= $(TUTORIAL_HOME)/../dolev-yao-star-extrinsic
COMPARSE_HOME 	?= $(DY_HOME)/../comparse

INNER_SOURCE_DIRS = dy-extensions
# SOURCE_DIRS = $(addprefix $(DY_HOME)/src/, $(INNER_SOURCE_DIRS))
SOURCE_DIRS = $(addprefix $(TUTORIAL_HOME)/, $(INNER_SOURCE_DIRS))

INNER_EXAMPLE_DIRS = nsl_pk_only_one_event_lookup TwoMessageP Online Online_with_secrecy Online_with_authn
EXAMPLE_DIRS ?= $(addprefix $(TUTORIAL_HOME)/examples/, $(INNER_EXAMPLE_DIRS))


DY_INCLUDE_DIRS = core lib lib/comparse lib/crypto lib/event lib/hpke lib/state lib/utils
INCLUDE_DIRS = $(SOURCE_DIRS) $(EXAMPLE_DIRS) $(COMPARSE_HOME)/src $(addprefix $(DY_HOME)/src/, $(DY_INCLUDE_DIRS))
FSTAR_INCLUDE_DIRS = $(addprefix --include , $(INCLUDE_DIRS))

ADMIT ?=
MAYBE_ADMIT = $(if $(ADMIT),--admit_smt_queries true)

FSTAR_EXE ?= $(FSTAR_HOME)/bin/fstar.exe
FSTAR = $(FSTAR_EXE) $(MAYBE_ADMIT)

FSTAR_EXTRACT = --extract '-* +DY +Comparse'

# Allowed warnings:
# - (Warning 242) Definitions of inner let-rec ... and its enclosing top-level letbinding are not encoded to the solver, you will only be able to reason with their types
# - (Warning 335) Interface ... is admitted without an implementation 

FSTAR_FLAGS = $(FSTAR_INCLUDE_DIRS) --cache_checked_modules --already_cached '+Prims +FStar' --warn_error '@0..1000' --warn_error '+242-335' --record_hints --hint_dir $(TUTORIAL_HOME)/hints --cache_dir $(TUTORIAL_HOME)/cache --odir $(TUTORIAL_HOME)/obj --cmi

.PHONY: all clean

all: copy_lib

clean:
	#dune clean
	rm -rf $(TUTORIAL_HOME)/hints $(TUTORIAL_HOME)/obj $(TUTORIAL_HOME)/cache $(TUTORIAL_HOME)/ml/lib/src $(TUTORIAL_HOME)/ml/tests/src

# Dependency analysis

FSTAR_ROOTS = \
  $(wildcard $(addsuffix /*.fsti,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(SOURCE_DIRS))) \
  $(wildcard $(addsuffix /*.fsti,$(EXAMPLE_DIRS))) \
  $(wildcard $(addsuffix /*.fst,$(EXAMPLE_DIRS)))

ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef MAKE_RESTARTS
$(TUTORIAL_HOME)/.depend: .FORCE
	$(FSTAR) $(FSTAR_FLAGS) --dep full $(FSTAR_EXTRACT) $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include $(TUTORIAL_HOME)/.depend

# Verification

$(TUTORIAL_HOME)/hints:
	mkdir $@

$(TUTORIAL_HOME)/cache:
	mkdir $@

$(TUTORIAL_HOME)/obj:
	mkdir $@


%.checked: FSTAR_RULE_FLAGS=

%.checked: | $(TUTORIAL_HOME)/hints $(TUTORIAL_HOME)/cache $(TUTORIAL_HOME)/obj
	$(FSTAR) $(FSTAR_FLAGS) $(FSTAR_RULE_FLAGS) $< && touch -c $@

# Extraction
.PRECIOUS: $(TUTORIAL_HOME)/obj/%.ml
$(TUTORIAL_HOME)/obj/%.ml:
	$(FSTAR) $(FSTAR_FLAGS) $(notdir $(subst .checked,,$<)) --codegen OCaml \
	--extract_module $(basename $(notdir $(subst .checked,,$<)))

.PHONY: extract_lib copy_lib

extract_lib: $(ALL_ML_FILES)

copy_lib: extract_lib
	mkdir -p $(TUTORIAL_HOME)/ml/lib/src
	cp $(ALL_ML_FILES) $(TUTORIAL_HOME)/ml/lib/src

%.fst-in %.fsti-in:
	@echo $(FSTAR_INCLUDE_DIRS) --include $(TUTORIAL_HOME)/obj

# Compilation

.PHONY: check #$(addprefix check-,$(INNER_EXAMPLE_DIRS))

check-%: copy_lib
	make -C examples/$* test

check: $(addprefix check-,$(INNER_EXAMPLE_DIRS))
