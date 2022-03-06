COQMAKEFILE?=Makefile.coq

BINS?=FileTest.native

all: clean
	$(MAKE) $(BINS)

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f $^ -o $@

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $^ cleanall
	@rm -f $^ $^.conf *~ *.ml* *.log
	@ocamlbuild -clean

%.native:
	$(MAKE) $(COQMAKEFILE)
	$(MAKE) -f $(COQMAKEFILE) $*.vo
	ocamlbuild -use-ocamlfind $@

test: $(BINS)
	$(RM) logs.txt
	./FileTest.native 2> error.txt
