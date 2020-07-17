all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

factb: factb/factb.vo

head: head/head.vo

listz: listz/foldl.vo listz/revert.vo

ns: ns/ns.vo ns/ns_acc.vo

dfs: dfs/dfs_term.vo

nm: nm/nm_term.vo

unif: unif/unif_term.vo

.PHONY: all clean

dummy:

%.vo: Makefile.coq dummy
	+make -f Makefile.coq $@

