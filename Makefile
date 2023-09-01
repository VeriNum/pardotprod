CFILES= main.c dotprod.c parsplit.c seqdotprod.c
COQMF_COQLIB=$(shell coqc -where)
VSTLIB=$(COQMF_COQLIB)/user-contrib/VSTlib
INCLUDE=$(VSTLIB)/include

CC=gcc
CFLAGS=-O2 -I$(INCLUDE)

dotprod: main.o dotprod.o parsplit.o threads.o locks.o SC_atomics.o
	gcc $^ -o $@

main.o: main.c dotprod.h

dotprod.o: dotprod.c parsplit.h

parsplit.o: parsplit.c parsplit.h $(INCLUDE)/VSTthreads.h

threads.o: $(VSTLIB)/src/threads.c $(INCLUDE)/VSTthreads.h 
	$(CC) $(CFLAGS) -c $< -o $@

locks.o: $(VSTLIB)/src/locks.c $(INCLUDE)/VSTthreads.h $(INCLUDE)/SC_atomics.h
	$(CC) $(CFLAGS) -c $< -o $@

SC_atomics.o: $(VSTLIB)/src/SC_atomics.c $(INCLUDE)/SC_atomics.h
	$(CC) $(CFLAGS) -c $< -o $@

test: dotprod
	time ./dotprod 1000000 4 1000
# Sample output of "make test": 
# N=1000000  T=4  R=1000  result=249995018.955975
#
# real    0m1.549s
# user    0m11.093s
# sys     0m0.061s

clean:
	rm -f *.o dotprod *{.vo,vo?,glob}

CLIGHTGEN=clightgen
CGFLAGS=-I$(INCLUDE)

cv-files: $(patsubst %.c,%.v,$(CFILES))

main.v: main.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $< -o $@

dotprod.v: dotprod.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $< -o $@

parsplit.v: parsplit.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $< -o $@

seqdotprod.v: seqdotprod.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $< -o $@

locks.v: $(VSTLIB)/src/locks.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $< -o $@

threads.v: $(VSTLIB)/src/threads.c
	$(CLIGHTGEN) ${CGFLAGS} -normalize $< -o $@

COQC=coqc
COQDEP=coqdep
COQPROJECT != cat _CoqProject
COQFLAGS=$(COQPROJECT)

proof: verif_dotprod.vo verif_parsplit.vo

seqdotprod: verif_seqdotprod.vo

%.vo: %.v
	$(COQC) $(COQFLAGS) $*.v

depend: 
	$(COQDEP) $(COQFLAGS) *.v > .depend

-include .depend
