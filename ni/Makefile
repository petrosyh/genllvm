.DEFAULT_GOAL := all
.PHONY: all clean check bench

RocqMakefile: _RocqProject
	opam exec --switch=genllvm -- rocq makefile -f _RocqProject -o $@

all clean: RocqMakefile
	+opam exec --switch=genllvm -- $(MAKE) -f RocqMakefile $@

check:
	opam exec --switch=genllvm -- python3 check.py

bench:
	opam exec --switch=genllvm -- python3 check.py --benchmark
