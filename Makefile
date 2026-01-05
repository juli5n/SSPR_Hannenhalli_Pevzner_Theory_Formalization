# Utility functions
rwildcard = $(foreach d,$(wildcard $(1:=/*)),$(call rwildcard,$d,$2) $(filter $(subst *,%,$2),$d))

PROJECT_ROOT =.
PROJECT_NAME =SSPRHannenhalliPevznerTheory

# Gather source paths
ROOT_SOURCE_FILE=$(PROJECT_ROOT)/$(PROJECT_NAME).lean
MAIN_SOURCE_DIRECTORY =$(PROJECT_ROOT)/$(PROJECT_NAME)
MAIN_SOURCE_DIRECTORY_SOURCES=$(call rwildcard,$(MAIN_SOURCE_DIRECTORY),*.lean) 

SOURCE=$(ROOT_SOURCE_FILE) $(MAIN_SOURCE_DIRECTORY_SOURCES)

$(info SOURCE=$(SOURCE))


# Gather output paths
DOCBUILD_DIRECTORY =$(PROJECT_ROOT)/docbuild
DOCBUILD_LAKE_DIRECTORY =$(DOCBUILD_DIRECTORY)/.lake
DOC_OUTPUT_DIRECTORY = $(DOCBUILD_LAKE_DIRECTORY)/build/doc
DOC_INDEX_FILE = $(DOC_OUTPUT_DIRECTORY)/index.html

.RECIPEPREFIX = >

.PHONY: all
all: docs

.PHONY: docs 
docs: $(DOC_INDEX_FILE)


$(DOC_INDEX_FILE): $(SOURCE)
> cd $(DOCBUILD_DIRECTORY) && lake build $(PROJECT_NAME):docs
> touch $(DOC_INDEX_FILE)

.PHONY: open_doc
open_doc:
> open $(DOC_OUTPUT_DIRECTORY)/index.html

.PHONY: bod
bod: build_and_open_doc
.PHONY: build_and_open_doc
build_and_open_doc: docs open_doc

.PHONY: nothing
nothing: