COQMAKEFILE?=Makefile.coq
EXE?=FileTest.native
INSTALLDIR?=$(shell opam var bin)

all: $(COQMAKEFILE)
	@+$(MAKE) -f $< $@
	@+$(MAKE) -C extract

clean: $(COQMAKEFILE)
	@+$(MAKE) -f $< cleanall
	@rm -f $< $<.conf

$(COQMAKEFILE): _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o $@

force _CoqProject Makefile: ;

%: $(COQMAKEFILE) force
	@+$(MAKE) -f $< $@

.PHONY: all clean force

test: all
	$(MAKE) -C extract test

install: $(COQMAKEFILE)
	@+$(MAKE) -f $^ $@
	install extract/$(EXE) $(INSTALLDIR)
