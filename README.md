# Parallel Dot Product, proved correct in VST

Copyright (c) 2022 Andrew W. Appel

Formally verified implementation of a multithreaded C program, using the Verified Software Toolchain.

The C program uses semaphores in a simple handshake protocol, and gets good speedup.

The VST verification uses threads and locks with resource invariants.

Program build, from the top down:
- dotprod.c:    Compute parallel dot product using parsplit.h API
- parsplit.h:   Andrew's little API for parallel tasks
- parsplit.c:   Implement the API using threads.h API
- threads.h:   William Mansky's API for VST-provable threads and semaphores
- threads.c:    Mansky's proved-correct implementation, based on SC_atomics.h API
- SC_atomics.h:  Mansky's API for some special cases of the C11 atomic operations
- SC_atomics.c:  Mansky's implementation, axiomatized in VST but not proved

Cygwin: This builds and runs for me on cygwin
   (make sure your Cygwin-devel package is 3.2.0 or after).

Linux: It does not build for me on Ubuntu; at link time it can't 
  find thrd_create.  I think it's missing the stdthreads.a library.

Proof build, from the top down:
- dotprod.c:    Compute parallel dot product using parsplit.h API
- parsplit.h:   Andrew's little API for parallel tasks
- parsplit.c:   Implement the API using threads.h API
- threads.h:    William Mansky's API for VST-provable threads and semaphores
- threads_stub.c:  For the time being, verication is w.r.t. an _axiomatized_ threads library.

- spec_parsplit.v:   Specification of the parsplit.h API
- verif_dotprod.v:   Specification and verification of dotprod.c
- verif_parsplit.v:  Verification of parsplit.c
