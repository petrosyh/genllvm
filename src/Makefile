## GenLLVM Project Makefile

#### Build Configuration Information

## Project Source Locations
# Rocq sources
ROCQDIR = rocq

# OCaml sources
EXTRACTDIR = ml/extracted

## Vellvm submodule rocq source
VELLVM_SRC_DIR = ../vellvm/src
VELLVM_ROCQ_DIR = $(VELLVM_SRC_DIR)/rocq
VELLVM_ML_DIR = $(VELLVM_SRC_DIR)/ml


ROCQINCLUDES=$(ROCQDIR), -R $(ROCQDIR) GenLLVM -R $(EXTRACTDIR) Extract -R Vellvm $(VELLVM_ROCQ_DIR)
ROCQEXEC="$(ROCQBIN)rocq" top -q -w none $(ROCQINCLUDES) -batch -load-vernac-source
ROCQMAKEFILE="$(ROCQBIN)rocq" makefile


######## The full genllvm executable
GENLLVM_EXE=_build/default/ml/main.exe
# Override with `make DUNE_PROFILE=dev` for debug builds.
DUNE_PROFILE?=dev
# DUNE_PROFILE?=release

ROCQFILES_EXEC := GenLLVM
EXEC_VOFILES := $(ROCQFILES_EXEC:%=rocq/%.vo)

.DEFAULT_GOAL := all

RocqMakefile: _RocqProject
	$(ROCQMAKEFILE) -f _RocqProject -o RocqMakefile

.PHONY: all
all:
	$(MAKE) vellvm
	$(MAKE) rocq
	$(MAKE) genllvm

.PHONY: rocq
rocq: real-all


####### Only need the "interp" parts of Vellvm
.PHONY: vellvm
vellvm:
	make interp -C ../vellvm/src 



.PHONY: extracted
extracted: $(EXTRACTDIR)/STAMP

$(EXTRACTDIR)/STAMP: $(EXEC_VOFILES) $(EXTRACTDIR)/Extract.v
	@echo "Extracting"
	$(ROCQEXEC) $(EXTRACTDIR)/Extract.v
	@echo "Post-processing extraction: unbox the itree node wrapper"
	perl -i -pe 's/^(\| Coq_go of .* itreeF)$$/$$1 [\@\@unboxed]/' $(EXTRACTDIR)/ITreeDefinition.ml $(EXTRACTDIR)/ITreeDefinition.mli
	touch $(EXTRACTDIR)/STAMP

$(GENLLVM_EXE): extracted ml/dune ml/extracted/dune 
	@echo "Compiling GenLLVM"
	dune build --profile $(DUNE_PROFILE) ml/main.exe

genllvm: $(GENLLVM_EXE)
	touch genllvm

clean: extractedclean clean-rocqmakefile
	make clean -C $(VELLVM_SRC_DIR)
	rm -f genllvm

.PHONY: extractedclean
extractedclean:
	rm -f $(EXTRACTDIR)/STAMP $(EXTRACTDIR)/FRONTEND_STAMP $(EXTRACTDIR)/*.ml $(EXTRACTDIR)/*.mli $(EXTRACTDIR)/\#* $(EXTRACTDIR)/.!*

.PHONY: clean-rocqmakefile
clean-rocqmakefile: RocqMakefile
	$(MAKE) -j --no-print-directory -f RocqMakefile clean


######## Hand-written source files used as prerequisites above: an empty
######## recipe marks them "terminal" so the catch-all pattern rule below
######## never mistakes one of them for a stale RocqMakefile-generated
######## target (which would otherwise happen the moment RocqMakefile
######## itself is regenerated and becomes newer than these).
Makefile _RocqProject $(EXTRACTDIR)/Extract.v ml/dune ml/extracted/dune: ;




######## Anything else (a bare Rocq target such as `rocq/Foo/Bar.vo`, or a
######## target only defined by the generated RocqMakefile, e.g. `real-all`,
######## `html`, `install`) is forwarded there, scoped to just that target.
######## Same always-ask-RocqMakefile reasoning as above, via a shared
######## .PHONY marker rather than a plain file-mtime prerequisite.
.PHONY: invoke-rocqmakefile
invoke-rocqmakefile: RocqMakefile

%: invoke-rocqmakefile
	+$(MAKE) -j --no-print-directory -f RocqMakefile $@
