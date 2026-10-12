.PHONY: all verify audit clean

# Source roots to scan for .fst/.fsti files.
# Current directory is scanned top-level only; other roots are recursive.
SOURCE_ROOT_DIRS=. helpers examples
SOURCES=$(shell { \
	for dir in $(SOURCE_ROOT_DIRS); do \
		if [ "$$dir" = "." ]; then \
			find "$$dir" -maxdepth 1 -type f \( -name '*.fst' -o -name '*.fsti' \); \
		else \
			find "$$dir" -type f \( -name '*.fst' -o -name '*.fsti' \); \
		fi; \
	done; \
} | sort)
ROOTS=$(filter %.fst,$(SOURCES)) # scan these files for dependences
OUTPUT_DIR=output
$(shell mkdir -p $(OUTPUT_DIR))
INCLUDE_PATHS=$(sort $(dir $(SOURCES)))

ifdef FSTAR_HOME
  ifeq ($(OS),Windows_NT)
    FSTAR_EXE := $(shell cygpath -m $(FSTAR_HOME)/bin/fstar.exe)
  else
    FSTAR_EXE := $(FSTAR_HOME)/bin/fstar.exe
  endif
else
  FSTAR_EXE := fstar.exe
endif

#cache_dir: where to find checked files
#odir: where to put all output artifacts
#include: where to find source and checked files
#already_cached: fstar ulib is already built

FSTAR=$(FSTAR_EXE) \
	--cache_dir $(OUTPUT_DIR) \
	--odir $(OUTPUT_DIR) \
	$(addprefix --include , $(INCLUDE_PATHS) $(OUTPUT_DIR)) \
	--already_cached 'Prims'

all: verify

# generate a dependency graph
.depend: $(SOURCES)
	$(FSTAR) --dep full $(ROOTS) --extract '* -Prims -FStar' --output_deps_to $@

# this defines the $(ALL_CHECKED_FILES) variable and the dependences between them
include .depend

# recipe to verify a file and produce its .checked file
$(OUTPUT_DIR)/%.checked:
	$(FSTAR) $< --cache_checked_modules

verify: $(ALL_CHECKED_FILES)

# report every escape hatch (admit, assume, ...) used in the sources; run after
# `make verify` so that dependencies are loaded from the cache
audit: verify
	FSTAR_EXE="$(FSTAR_EXE)" python3 scripts/audit_assumes.py

clean:
	rm -f $(OUTPUT_DIR)/*.checked .depend
