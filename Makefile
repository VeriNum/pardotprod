CC=gcc
CFLAGS=-O2

CFILES=dotprod.c parsplit.c

dotprod: dotprod.o parsplit.o threads.o SC_atomics.o
	gcc $^ -o $@

dotprod.o: dotprod.c parsplit.h

parsplit.o: parsplit.c parsplit.h threads.h

threads.o: threads.c threads.h SC_atomics.h

SC_atomics.o: SC_atomics.c SC_atomics.h

test: dotprod
	time ./dotprod 1000000 8 1000
# Sample output of "make test": 
# N=1000000  T=8  R=1000  result=249995018.955975
#
# real    0m1.549s
# user    0m11.093s
# sys     0m0.061s

clean:
	rm -f *.o dotprod *{.vo,vo?,glob}

CLIGHTGEN=/cygdrive/c/local/CompCert-3.10-32/clightgen

ifdef CLIGHTGEN
cv-files: $(patsubst %.c,%.v,$(CFILES))

$(patsubst %.c,%.v,$(CFILES)):  threads_stub.c $(CFILES)
	$(CLIGHTGEN) ${CGFLAGS} -normalize threads_stub.c $(CFILES)
endif

COQC=coqc
COQDEP=coqdep
COQPROJECT != cat _CoqProject
COQFLAGS=$(COQPROJECT)

proof: verif_dotprod.vo verif_parsplit.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v > .depend

-include .depend
