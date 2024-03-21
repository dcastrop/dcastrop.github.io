---
title: "Compiling first-order functions to session-typed parallel code"
collection: publications
authors: "David Castro-Perez, Nobuko Yoshida"
permalink: /publication/2020-cc-compiling
year: 2020
venue: 'CC'
pages: '143-154'
paperurl: 'files/2020-cc-compiling.pdf'
---

Building correct and efficient message-passing parallel programs still poses
many challenges. The incorrect use of message-passing constructs can introduce
deadlocks, and a bad task decomposition will not achieve good speedups. Current
approaches focus either on correctness or efficiency, but limited work has been
done on ensuring both. In this paper, we propose a new parallel programming
framework, PAlg, which is a first-order language with participant annotations
that ensures deadlock-freedom by construction. PAlg programs are coupled with
an abstraction of their communication structure, a global type from the theory
of multiparty session types (MPST). This global type serves as an output for
the programmer to assess the efficiency of their achieved parallelisation. PAlg
is implemented as an EDSL in Haskell, from which we: 1. compile to low-level
message-passing C code; 2. compile to sequential C code, or interpret as
sequential Haskell functions; and, 3. infer the communication protocol followed
by the compiled message-passing program. We use the properties of global types
to perform message reordering optimisations to the compiled C code. We prove
the extensional equivalence of the compiled code, as well as protocol
compliance. We achieve linear speedups on a shared-memory 12-core machine, and
a speedup of 16 on a 2-node, 24-core NUMA.
